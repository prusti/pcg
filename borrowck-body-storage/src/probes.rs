//! Borrow-check probes: with `BORROWCK_PROBES=<file>`, `mir_promoted`
//! inserts the accesses listed in that file into the MIR before the borrow
//! checker runs, so that rustc's real borrow checker decides whether each
//! access is allowed at its point.
//!
//! Each line `PROBE\t<id>\t<function>\t<block>\t<index>\t<shared|mut>\t<local>\t<projection>...`
//! of the file (as `pcg_bin` writes it with `PCG_ORACLE_PROBES`) inserts
//! `_fresh = &p` or `_fresh = &mut p` before statement `index` of `block` of
//! the function whose def path is `<function>`. `_fresh` is never used, so
//! the probe's loan ends at once and does not change any other fact. Each
//! probe gets its own one-byte span inside the body, printed as
//! `PROBE-SPAN\t<id>\t<byte offset>`, so that an error reported with
//! `--error-format=json` names the probe it belongs to.

use std::cell::RefCell;

use pcg::rustc_interface::{
    abi::{FieldIdx, VariantIdx},
    data_structures::{fx::FxHashMap, steal::Steal},
    hir::def_id::LocalDefId,
    index::IndexVec,
    middle::{
        mir::{
            self, BorrowKind, LocalDecl, MutBorrowKind, Promoted, Rvalue, SourceInfo, Statement,
            StatementKind,
        },
        ty::{self, Ty, TyCtxt},
        util::Providers,
    },
    session::Session,
    span::BytePos,
};

/// One access to insert.
struct Probe {
    id: String,
    block: usize,
    index: usize,
    mutable: bool,
    local: usize,
    projection: String,
}

thread_local! {
    static PROBES: RefCell<Option<FxHashMap<String, Vec<Probe>>>> = const { RefCell::new(None) };
}

/// Whether probes are inserted: the PCG then does not run.
pub fn probes_enabled() -> bool {
    std::env::var_os("BORROWCK_PROBES").is_some()
}

fn load_probes() -> FxHashMap<String, Vec<Probe>> {
    let path = std::env::var("BORROWCK_PROBES").unwrap();
    let mut probes: FxHashMap<String, Vec<Probe>> = FxHashMap::default();
    let content = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("Failed to read the probes in {path}: {e}"));
    for line in content.lines() {
        let columns = line.split('\t').collect::<Vec<_>>();
        if columns.len() < 8 || columns[0] != "PROBE" {
            continue;
        }
        probes
            .entry(columns[2].to_owned())
            .or_default()
            .push(Probe {
                id: columns[1].to_owned(),
                block: columns[3].parse().unwrap(),
                index: columns[4].parse().unwrap(),
                mutable: columns[5] == "mut",
                local: columns[6].parse().unwrap(),
                projection: columns[7].to_owned(),
            });
    }
    probes
}

type MirPromoted<'tcx> = (
    &'tcx Steal<mir::Body<'tcx>>,
    &'tcx Steal<IndexVec<Promoted, mir::Body<'tcx>>>,
);

fn mir_promoted_with_probes<'tcx>(tcx: TyCtxt<'tcx>, def_id: LocalDefId) -> MirPromoted<'tcx> {
    let mut providers = Providers::default();
    rustc_mir_transform::provide(&mut providers);
    let (body, promoted) = (providers.queries.mir_promoted)(tcx, def_id);
    let name = tcx.def_path_str(def_id.to_def_id());
    let Some(mut probes) =
        PROBES.with(|p| p.borrow_mut().get_or_insert_with(load_probes).remove(&name))
    else {
        return (body, promoted);
    };
    let mut body = body.steal();
    // Inserting from the back keeps the indices of the earlier probes.
    probes.sort_by_key(|p| std::cmp::Reverse((p.block, p.index)));
    let source_map = tcx.sess.source_map();
    for (ordinal, probe) in probes.iter().enumerate() {
        let place = decode_projection(
            tcx,
            &body,
            mir::Local::from_usize(probe.local),
            &probe.projection,
        );
        let ty: Ty<'tcx> = place.ty(&body.local_decls, tcx).ty;
        let erased = tcx.lifetimes.re_erased;
        let (kind, mutability) = if probe.mutable {
            (
                BorrowKind::Mut {
                    kind: MutBorrowKind::Default,
                },
                ty::Mutability::Mut,
            )
        } else {
            (BorrowKind::Shared, ty::Mutability::Not)
        };
        let lo = body.span.lo() + BytePos(u32::try_from(ordinal).unwrap());
        let span = body.span.with_lo(lo).with_hi(lo + BytePos(1));
        let fresh = body.local_decls.push(LocalDecl::new(
            Ty::new_ref(tcx, erased, ty, mutability),
            span,
        ));
        let block = &mut body.basic_blocks_mut()[mir::BasicBlock::from_usize(probe.block)];
        let scope = block
            .statements
            .get(probe.index)
            .map_or(block.terminator().source_info.scope, |s| {
                s.source_info.scope
            });
        block.statements.insert(
            probe.index,
            Statement::new(
                SourceInfo { span, scope },
                StatementKind::Assign(Box::new((fresh.into(), Rvalue::Ref(erased, kind, place)))),
            ),
        );
        eprintln!(
            "PROBE-SPAN\t{}\t{}",
            probe.id,
            source_map.lookup_byte_offset(lo).pos.0
        );
    }
    (tcx.alloc_steal_mir(body), promoted)
}

/// The place of `body` with base `local` and the projection `projection`
/// that `pcg::oracle::encode_projection` wrote.
fn decode_projection<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mir::Body<'tcx>,
    local: mir::Local,
    projection: &str,
) -> mir::Place<'tcx> {
    let mut place = mir::Place::from(local);
    for part in projection.split(',').filter(|s| !s.is_empty()) {
        let place_ty = place.ty(&body.local_decls, tcx);
        let (head, rest) = part.split_at(1);
        let numbers = || {
            rest.split(':')
                .map(|n| n.parse::<u64>().unwrap())
                .collect::<Vec<_>>()
        };
        let elem = match head {
            "d" => mir::ProjectionElem::Deref,
            "f" => {
                let field = FieldIdx::from_usize(rest.parse().unwrap());
                let field_ty =
                    mir::PlaceTy::field_ty(tcx, place_ty.ty, place_ty.variant_index, field);
                mir::ProjectionElem::Field(
                    field,
                    tcx.normalize_erasing_regions(body.typing_env(tcx), field_ty),
                )
            }
            "v" => {
                mir::ProjectionElem::Downcast(None, VariantIdx::from_usize(rest.parse().unwrap()))
            }
            "i" => mir::ProjectionElem::Index(mir::Local::from_usize(rest.parse().unwrap())),
            "c" => {
                let n = numbers();
                mir::ProjectionElem::ConstantIndex {
                    offset: n[0],
                    min_length: n[1],
                    from_end: n[2] == 1,
                }
            }
            "s" => {
                let n = numbers();
                mir::ProjectionElem::Subslice {
                    from: n[0],
                    to: n[1],
                    from_end: n[2] == 1,
                }
            }
            _ => panic!("Unknown projection {part}"),
        };
        place = place.project_deeper(&[elem], tcx);
    }
    place
}

/// Overrides `mir_promoted` to insert the probes of `BORROWCK_PROBES`.
pub(crate) fn set_probe_provider(_session: &Session, providers: &mut Providers) {
    providers.queries.mir_promoted = mir_promoted_with_probes;
}
