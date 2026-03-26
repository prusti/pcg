use crate::{
    rustc_interface::{
        self,
        middle::ty::{self, TyCtxt},
        span::{BytePos, Span},
    },
    utils::{CompilerCtxt, Place, display::DisplayWithCompilerCtxt},
};
use serde_derive::{Deserialize, Serialize};
use std::{
    borrow::Cow,
    fmt::Write,
    fs::File,
    io::{self},
    path::Path,
};

use rustc_interface::middle::mir::{
    self, BinOp, Local, Operand, Rvalue, Statement, TerminatorKind, UnwindAction,
};

#[rustversion::since(2025-03-02)]
use rustc_interface::middle::mir::RawPtrKind;

#[rustversion::before(2025-03-02)]
use rustc_interface::ast::Mutability;

#[derive(Serialize)]
#[cfg_attr(feature = "type-export", derive(specta::Type))]
struct MirGraph {
    nodes: Vec<MirNode>,
    edges: Vec<MirEdge>,
}

#[derive(Deserialize, Serialize, Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "type-export", derive(specta::Type))]
pub struct SourcePos {
    pub line: usize,
    pub column: usize,
}

impl SourcePos {
    pub(crate) fn new(pos: BytePos, tcx: TyCtxt<'_>) -> Self {
        let source_map = tcx.sess.source_map();
        let loc = source_map.lookup_char_pos(pos);
        Self {
            line: loc.line,
            column: loc.col_display,
        }
    }
}

#[derive(Serialize)]
#[cfg_attr(feature = "type-export", derive(specta::Type))]
struct MirStmtSpan {
    low: SourcePos,
    high: SourcePos,
}

#[derive(Serialize)]
#[cfg_attr(feature = "type-export", derive(specta::Type))]
struct MirStmt {
    stmt: String,
    debug_stmt: String,
    span: MirStmtSpan,
    loans_invalidated_start: Vec<String>,
    loans_invalidated_mid: Vec<String>,
    borrows_in_scope_start: Vec<String>,
    borrows_in_scope_mid: Vec<String>,
}

#[derive(Serialize)]
#[cfg_attr(feature = "type-export", derive(specta::Type))]
struct MirNode {
    id: String,
    block: usize,
    stmts: Vec<MirStmt>,
    terminator: MirStmt,
    /// DOT graph of the signature shape (from fn def signature), if this
    /// block's terminator is a call.
    sig_shape_dot: Option<String>,
    /// DOT graph of the call shape derived solely from call-site operand types.
    call_shape_dot: Option<String>,
}

#[derive(Serialize)]
#[cfg_attr(feature = "type-export", derive(specta::Type))]
struct MirEdge {
    source: String,
    target: String,
    label: Cow<'static, str>,
}

fn format_bin_op(op: BinOp) -> &'static str {
    match op {
        BinOp::Add | BinOp::AddWithOverflow => "+",
        BinOp::Sub | BinOp::SubWithOverflow => "-",
        BinOp::Mul | BinOp::MulWithOverflow => "*",
        BinOp::Div => "/",
        BinOp::Rem => "%",
        BinOp::AddUnchecked => todo!(),
        BinOp::SubUnchecked => todo!(),
        BinOp::MulUnchecked => todo!(),
        BinOp::BitXor => "^",
        BinOp::BitAnd => "&",
        BinOp::BitOr => "|",
        BinOp::Shl | BinOp::ShlUnchecked => "<<",
        BinOp::Shr | BinOp::ShrUnchecked => ">>",
        BinOp::Eq => "==",
        BinOp::Lt => "<",
        BinOp::Le => "<=",
        BinOp::Ne => "!=",
        BinOp::Ge => ">=",
        BinOp::Gt => ">",
        BinOp::Offset => todo!(),
        BinOp::Cmp => todo!(),
    }
}

fn format_local<'tcx>(local: Local, ctxt: CompilerCtxt<'_, 'tcx>) -> String {
    let place: Place<'tcx> = local.into();
    place.display_string(ctxt)
}

fn format_place<'tcx>(place: &mir::Place<'tcx>, ctxt: CompilerCtxt<'_, 'tcx>) -> String {
    let place: Place<'tcx> = (*place).into();
    place.display_string(ctxt)
}

#[allow(unreachable_patterns)]
fn format_operand<'tcx>(operand: &Operand<'tcx>, ctxt: CompilerCtxt<'_, 'tcx>) -> String {
    match operand {
        Operand::Copy(p) => format_place(p, ctxt),
        Operand::Move(p) => format!("move {}", format_place(p, ctxt)),
        Operand::Constant(c) => format!("{c}"),
        other => todo!("{other:?}"),
    }
}

#[rustversion::since(2025-03-02)]
fn format_raw_ptr<'tcx>(
    kind: RawPtrKind,
    place: &mir::Place<'tcx>,
    ctxt: CompilerCtxt<'_, 'tcx>,
) -> String {
    let kind = match kind {
        RawPtrKind::Mut => "mut",
        RawPtrKind::Const => "const",
        RawPtrKind::FakeForPtrMetadata => "fake",
    };
    format!("&raw {} {}", kind, format_place(place, ctxt))
}

#[rustversion::before(2025-03-02)]
fn format_raw_ptr<'tcx>(
    kind: &Mutability,
    place: &mir::Place<'tcx>,
    ctxt: CompilerCtxt<'_, 'tcx>,
) -> String {
    let kind = match kind {
        Mutability::Mut => "mut",
        Mutability::Not => "const",
    };
    format!("*{} {}", kind, format_place(place, ctxt))
}

#[allow(unreachable_patterns)]
fn format_rvalue<'tcx>(rvalue: &Rvalue<'tcx>, ctxt: CompilerCtxt<'_, 'tcx>) -> String {
    match rvalue {
        Rvalue::Use(operand) => format_operand(operand, ctxt),
        Rvalue::Repeat(operand, c) => format!("repeat {} {}", format_operand(operand, ctxt), c),
        Rvalue::Ref(_region, kind, place) => {
            let kind = match kind {
                mir::BorrowKind::Shared => "",
                mir::BorrowKind::Mut { .. } => "mut",
                mir::BorrowKind::Fake(_) => "fake",
            };
            format!("&{} {}", kind, format_place(place, ctxt))
        }
        Rvalue::RawPtr(kind, place) => format_raw_ptr(*kind, place, ctxt),
        Rvalue::ThreadLocalRef(_) => todo!(),
        Rvalue::Cast(_, operand, ty) => format!("{} as {}", format_operand(operand, ctxt), ty),
        Rvalue::BinaryOp(op, box (lhs, rhs)) => {
            format!(
                "{} {} {}",
                format_operand(lhs, ctxt),
                format_bin_op(*op),
                format_operand(rhs, ctxt)
            )
        }
        Rvalue::UnaryOp(op, val) => {
            format!("{:?} {}", op, format_operand(val, ctxt))
        }
        Rvalue::Discriminant(place) => format!("Discriminant({})", format_place(place, ctxt)),
        Rvalue::Aggregate(kind, ops) => {
            format!(
                "Aggregate {:?} {}",
                kind,
                ops.iter()
                    .map(|op| format_operand(op, ctxt))
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        }
        Rvalue::ShallowInitBox(operand, _) => format!("Box({})", format_operand(operand, ctxt)),
        Rvalue::CopyForDeref(place) => format!("CopyForDeref({})", format_place(place, ctxt)),
        _ => todo!(),
    }
}
fn format_terminator<'tcx>(
    terminator: &TerminatorKind<'tcx>,
    ctxt: CompilerCtxt<'_, 'tcx>,
) -> String {
    match terminator {
        TerminatorKind::Drop {
            place,
            target,
            unwind,
            ..
        } => {
            format!(
                "drop({}) -> [return: {target:?}, unwind: {unwind:?}]",
                format_place(place, ctxt)
            )
        }
        TerminatorKind::Call {
            func,
            args,
            destination,
            target: _,
            unwind: _,
            call_source: _,
            fn_span: _,
        } => {
            format!(
                "{} = {}({})",
                format_place(destination, ctxt),
                format_operand(func, ctxt),
                args.iter()
                    .map(|arg| format_operand(&arg.node, ctxt))
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        }
        _ => format!("{terminator:?}"),
    }
}

fn format_stmt<'tcx>(stmt: &Statement<'tcx>, ctxt: CompilerCtxt<'_, 'tcx>) -> String {
    match &stmt.kind {
        mir::StatementKind::Assign(box (place, rvalue)) => {
            format!(
                "{} = {}",
                format_place(place, ctxt),
                format_rvalue(rvalue, ctxt)
            )
        }
        mir::StatementKind::FakeRead(box (_, place)) => {
            format!("FakeRead({})", format_place(place, ctxt))
        }
        mir::StatementKind::SetDiscriminant {
            place,
            variant_index,
        } => format!(
            "SetDiscriminant({} {:?})",
            format_place(place, ctxt),
            variant_index
        ),
        mir::StatementKind::StorageLive(local) => {
            format!("StorageLive({})", format_local(*local, ctxt))
        }
        mir::StatementKind::StorageDead(local) => {
            format!("StorageDead({})", format_local(*local, ctxt))
        }
        mir::StatementKind::Retag(_, _) => todo!(),
        mir::StatementKind::PlaceMention(place) => {
            format!("PlaceMention({})", format_place(place, ctxt))
        }
        mir::StatementKind::AscribeUserType(_, _) => "AscribeUserType(...)".to_owned(),
        mir::StatementKind::Coverage(_) => "coverage".to_owned(),
        mir::StatementKind::Intrinsic(non_diverging_intrinsic) => {
            format!("Intrinsic({non_diverging_intrinsic:?})")
        }
        mir::StatementKind::ConstEvalCounter => todo!(),
        mir::StatementKind::Nop => todo!(),
        _ => todo!(),
    }
}

fn mk_mir_stmt(
    stmt: String,
    debug_stmt: String,
    span: Span,
    location: mir::Location,
    ctxt: CompilerCtxt<'_, '_>,
) -> MirStmt {
    let bc = ctxt.borrow_checker.rust_borrow_checker().unwrap();
    let location_table = ctxt
        .borrow_checker
        .rust_borrow_checker()
        .unwrap()
        .location_table();
    let invalidated_at = &bc.input_facts().loan_invalidated_at;
    let loans_invalidated_start = invalidated_at
        .iter()
        .filter_map(|(point, idx)| {
            if *point == location_table.start_index(location) {
                let borrow_region = bc.borrow_index_to_region(*idx);
                Some(format!("{borrow_region:?}"))
            } else {
                None
            }
        })
        .collect::<Vec<_>>();
    let loans_invalidated_mid = invalidated_at
        .iter()
        .filter_map(|(point, idx)| {
            if *point == location_table.mid_index(location) {
                let borrow_region = bc.borrow_index_to_region(*idx);
                Some(format!("{borrow_region:?}"))
            } else {
                None
            }
        })
        .collect::<Vec<_>>();
    let borrows_in_scope_start = bc
        .borrows_in_scope_at(location, true)
        .iter()
        .map(|bi| format!("{bi:?}"))
        .collect::<Vec<_>>();
    let borrows_in_scope_mid = bc
        .borrows_in_scope_at(location, false)
        .iter()
        .map(|bi| format!("{bi:?}"))
        .collect::<Vec<_>>();
    let source_pos_low = SourcePos::new(span.lo(), ctxt.tcx());
    let source_pos_high = SourcePos::new(span.hi(), ctxt.tcx());
    MirStmt {
        stmt,
        debug_stmt,
        span: MirStmtSpan {
            low: source_pos_low,
            high: source_pos_high,
        },
        loans_invalidated_start,
        loans_invalidated_mid,
        borrows_in_scope_start,
        borrows_in_scope_mid,
    }
}

/// Resolve a call terminator's `func` operand to a `DefId` and generic args.
fn resolve_callee<'tcx>(
    func: &Operand<'tcx>,
    body: &mir::Body<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> Option<rustc_interface::hir::def_id::DefId> {
    let func_ty = func.ty(body, tcx);
    if let ty::TyKind::FnDef(def_id, _) = func_ty.kind() {
        Some(*def_id)
    } else {
        None
    }
}

/// Render a [`FunctionShape`] as a DOT bipartite graph with the given name.
fn function_shape_to_dot(
    shape: crate::borrow_pcg::abstraction::FunctionShape,
    graph_name: &str,
) -> Option<String> {
    let edges: Vec<_> = shape.edges().collect();
    let (inputs, outputs) = shape.take_inputs_and_outputs();

    let mut dot = String::new();
    writeln!(dot, "digraph \"{graph_name}\" {{").ok()?;
    writeln!(dot, "  rankdir=LR;").ok()?;
    writeln!(dot, "  node [shape=box fontname=monospace fontsize=12];").ok()?;
    writeln!(dot, "  subgraph cluster_inputs {{").ok()?;
    writeln!(dot, "    label=\"Inputs\";").ok()?;
    for input in &inputs {
        writeln!(dot, "    \"in_{input}\" [label=\"{input}\"];").ok()?;
    }
    writeln!(dot, "  }}").ok()?;
    writeln!(dot, "  subgraph cluster_outputs {{").ok()?;
    writeln!(dot, "    label=\"Outputs\";").ok()?;
    for output in &outputs {
        writeln!(dot, "    \"out_{output}\" [label=\"{output}\"];").ok()?;
    }
    writeln!(dot, "  }}").ok()?;
    for edge in &edges {
        writeln!(dot, "  \"in_{}\" -> \"out_{}\";", edge.input, edge.output).ok()?;
    }
    writeln!(dot, "}}").ok()?;
    Some(dot)
}

/// Generate a DOT graph representing the function shape (bipartite graph of
/// lifetime outlives relationships) for the callee at a call site.
fn generate_function_shape_dot(
    def_id: rustc_interface::hir::def_id::DefId,
    ctxt: CompilerCtxt<'_, '_>,
) -> Option<String> {
    use crate::borrow_pcg::abstraction::FunctionShape;
    let shape = FunctionShape::for_fn_sig(def_id, ctxt).ok()?;
    let fn_name = ctxt.tcx().def_path_str(def_id);
    function_shape_to_dot(shape, &fn_name)
}

/// Generate a DOT graph representing the call shape derived solely from the
/// types of the operands at the call site (ignoring the callee's fn def
/// signature).
fn generate_call_shape_dot<'tcx>(
    input_tys: Vec<ty::Ty<'tcx>>,
    output_ty: ty::Ty<'tcx>,
    location: mir::Location,
    ctxt: CompilerCtxt<'_, 'tcx>,
) -> Option<String> {
    use crate::borrow_pcg::{
        abstraction::FunctionShape, edge::abstraction::function::FnCallDataSource,
    };

    let data_source = FnCallDataSource::new(location, input_tys, output_ty);
    let shape = FunctionShape::new(&data_source, ctxt).ok()?;
    function_shape_to_dot(shape, "call_shape")
}

fn mk_mir_graph(ctxt: CompilerCtxt<'_, '_>) -> MirGraph {
    let mut nodes = Vec::new();
    let mut edges = Vec::new();

    for (bb, data) in ctxt.body().basic_blocks.iter_enumerated() {
        let stmts = data.statements.iter().enumerate().map(|(idx, stmt)| {
            let stmt_text = format_stmt(stmt, ctxt);
            let location = mir::Location {
                block: bb,
                statement_index: idx,
            };
            mk_mir_stmt(
                stmt_text,
                format!("{stmt:?}"),
                stmt.source_info.span,
                location,
                ctxt,
            )
        });

        let terminator_text = format_terminator(&data.terminator().kind, ctxt);
        let terminator_location = mir::Location {
            block: bb,
            statement_index: data.statements.len(),
        };
        let terminator = mk_mir_stmt(
            terminator_text,
            format!("{:?}", data.terminator()),
            data.terminator().source_info.span,
            terminator_location,
            ctxt,
        );

        // TODO: In principle, we can also create graphs for call shapes for
        // undefined functions (e.g. function pointers, closures).
        let (sig_shape_dot, call_shape_dot) = if let TerminatorKind::Call {
            func,
            args,
            destination,
            ..
        } = &data.terminator().kind
        {
            let sig_shape = resolve_callee(func, ctxt.body(), ctxt.tcx())
                .and_then(|def_id| generate_function_shape_dot(def_id, ctxt));
            let input_tys = args
                .iter()
                .map(|arg| arg.node.ty(ctxt.body(), ctxt.tcx()))
                .collect();
            let output_ty = destination.ty(ctxt.body(), ctxt.tcx()).ty;
            let call_shape =
                generate_call_shape_dot(input_tys, output_ty, terminator_location, ctxt);
            (sig_shape, call_shape)
        } else {
            (None, None)
        };

        nodes.push(MirNode {
            id: format!("{bb:?}"),
            block: bb.as_usize(),
            stmts: stmts.collect(),
            terminator,
            sig_shape_dot,
            call_shape_dot,
        });

        match &data.terminator().kind {
            TerminatorKind::Goto { target } => {
                edges.push(MirEdge {
                    source: format!("{bb:?}"),
                    target: format!("{target:?}"),
                    label: Cow::Borrowed("goto"),
                });
            }
            TerminatorKind::SwitchInt { discr: _, targets } => {
                for (val, target) in targets.iter() {
                    edges.push(MirEdge {
                        source: format!("{bb:?}"),
                        target: format!("{target:?}"),
                        label: Cow::Owned(format!("{val}")),
                    });
                }
                edges.push(MirEdge {
                    source: format!("{bb:?}"),
                    target: format!("{:?}", targets.otherwise()),
                    label: Cow::Borrowed("otherwise"),
                });
            }
            TerminatorKind::UnwindResume | TerminatorKind::Return | TerminatorKind::Unreachable => {
            }
            TerminatorKind::UnwindTerminate(_) => todo!(),
            TerminatorKind::Drop { target, .. } => {
                edges.push(MirEdge {
                    source: format!("{bb:?}"),
                    target: format!("{target:?}"),
                    label: Cow::Borrowed("drop"),
                });
            }
            TerminatorKind::Call {
                func: _,
                args: _,
                destination: _,
                target,
                unwind,
                call_source: _,
                fn_span: _,
            } => {
                if let Some(target) = target {
                    edges.push(MirEdge {
                        source: format!("{bb:?}"),
                        target: format!("{target:?}"),
                        label: Cow::Borrowed("call"),
                    });
                    match unwind {
                        UnwindAction::Continue => todo!(),
                        UnwindAction::Unreachable => todo!(),
                        UnwindAction::Terminate(_) => todo!(),
                        UnwindAction::Cleanup(cleanup) => {
                            edges.push(MirEdge {
                                source: format!("{bb:?}"),
                                target: format!("{cleanup:?}"),
                                label: Cow::Borrowed("unwind"),
                            });
                        }
                    }
                }
            }
            TerminatorKind::Assert {
                cond: _,
                expected: _,
                msg: _,
                target,
                unwind,
            } => {
                match unwind {
                    UnwindAction::Continue => todo!(),
                    UnwindAction::Unreachable => todo!(),
                    UnwindAction::Terminate(_) => todo!(),
                    UnwindAction::Cleanup(cleanup) => {
                        edges.push(MirEdge {
                            source: format!("{bb:?}"),
                            target: format!("{cleanup:?}"),
                            label: Cow::Borrowed("unwind"),
                        });
                    }
                }
                edges.push(MirEdge {
                    source: format!("{bb:?}"),
                    target: format!("{target:?}"),
                    label: Cow::Borrowed("success"),
                });
            }
            TerminatorKind::Yield {
                value: _,
                resume: _,
                resume_arg: _,
                drop: _,
            } => todo!(),
            TerminatorKind::FalseEdge {
                real_target,
                imaginary_target: _,
            }
            | TerminatorKind::FalseUnwind {
                real_target,
                unwind: _,
            } => {
                edges.push(MirEdge {
                    source: format!("{bb:?}"),
                    target: format!("{real_target:?}"),
                    label: Cow::Borrowed("real"),
                });
            }
            TerminatorKind::InlineAsm { .. } => todo!(),
            TerminatorKind::CoroutineDrop => todo!(),
            _ => todo!(),
        }
    }

    MirGraph { nodes, edges }
}
pub(crate) fn generate_json_from_mir(path: &Path, ctxt: CompilerCtxt<'_, '_>) -> io::Result<()> {
    let mir_graph = mk_mir_graph(ctxt);
    let mut file = File::create(path)?;
    serde_json::to_writer(&mut file, &mir_graph)?;
    Ok(())
}
