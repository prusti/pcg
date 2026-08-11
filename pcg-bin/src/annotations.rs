//! Parsing and attribution of the PCG annotations that appear in test sources.
//!
//! The span of a body textually contains the spans of the bodies nested inside
//! it (closures, async blocks, nested items), so containment alone does not say
//! which body an annotation describes. An annotation is therefore attributed to
//! the *innermost* body containing it: a body claims an annotation only when
//! none of the bodies directly nested inside it does.

use pcg::{
    borrow_pcg::region_projection::{PcgRegion, RegionIdx},
    rustc_interface::{
        data_structures::fx::FxHashMap,
        middle::{
            mir::{Body, Local},
            ty::{RegionVid, TyCtxt},
        },
        span::{BytePos, Span, SpanSnippetError, def_id::LocalDefId},
    },
    utils::{CompilerCtxt, Place},
};

/// The spans of the bodies directly nested inside each body owner of the crate.
pub(crate) struct NestedBodies {
    spans: FxHashMap<LocalDefId, Vec<Span>>,
}

impl NestedBodies {
    pub(crate) fn new(tcx: TyCtxt<'_>) -> Self {
        let mut spans: FxHashMap<LocalDefId, Vec<Span>> = FxHashMap::default();
        for def_id in tcx.hir_body_owners() {
            if let Some(parent) = tcx.opt_local_parent(def_id) {
                // `def_span` of a closure covers only its header (`|x| `), so
                // the span that includes the body is the one that tells us
                // which annotations are written inside the nested body.
                let span = tcx.hir_span_with_body(tcx.local_def_id_to_hir_id(def_id));
                spans.entry(parent).or_default().push(span);
            }
        }
        Self { spans }
    }

    fn directly_nested_in(&self, def_id: LocalDefId) -> &[Span] {
        self.spans.get(&def_id).map_or(&[], Vec::as_slice)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum AnnotationKind {
    /// The PCG state must arise somewhere in the annotated body.
    Expected,
    /// The PCG state must not arise anywhere in the annotated body.
    Forbidden,
    /// Overrides how a lifetime of the annotated body is rendered.
    LifetimeDisplay,
}

struct AnnotationMarker {
    text: &'static str,
    kind: AnnotationKind,
}

const MARKERS: [AnnotationMarker; 3] = [
    AnnotationMarker {
        text: "// PCG: ",
        kind: AnnotationKind::Expected,
    },
    AnnotationMarker {
        text: "// ~PCG: ",
        kind: AnnotationKind::Forbidden,
    },
    AnnotationMarker {
        text: "// PCG_LIFETIME_DISPLAY: ",
        kind: AnnotationKind::LifetimeDisplay,
    },
];

struct MarkerMatch<'a> {
    kind: AnnotationKind,
    payload: &'a str,
    /// Byte offset of the marker within its line.
    offset: usize,
}

impl<'a> MarkerMatch<'a> {
    fn of_line(line: &'a str) -> Option<Self> {
        let mut found: Option<Self> = None;
        for marker in &MARKERS {
            let Some(offset) = line.find(marker.text) else {
                continue;
            };
            assert!(
                found.is_none(),
                "line carries more than one PCG annotation: {line}"
            );
            found = Some(Self {
                kind: marker.kind,
                payload: line[offset + marker.text.len()..].trim(),
                offset,
            });
        }
        found
    }
}

fn contains(span: Span, pos: BytePos) -> bool {
    span.lo() <= pos && pos < span.hi()
}

/// The annotations belonging to a single body, i.e. those that no body nested
/// inside it claims.
#[derive(Default)]
pub(crate) struct BodyAnnotations {
    expected: Vec<String>,
    forbidden: Vec<String>,
    lifetime_display: Vec<LifetimeRenderAnnotation>,
}

impl BodyAnnotations {
    pub(crate) fn of_body<'tcx>(
        tcx: TyCtxt<'tcx>,
        body: &Body<'tcx>,
        nested: &NestedBodies,
    ) -> Result<Self, Box<SpanSnippetError>> {
        let span = body.span;
        let snippet = tcx
            .sess
            .source_map()
            .span_to_snippet(span)
            .map_err(Box::new)?;
        let nested_spans = nested.directly_nested_in(body.source.def_id().expect_local());
        let mut annotations = Self::default();
        let mut line_start = span.lo();
        for line in snippet.split_inclusive('\n') {
            if let Some(found) = MarkerMatch::of_line(line) {
                let pos = line_start + BytePos(u32::try_from(found.offset).unwrap());
                if !nested_spans.iter().any(|nested| contains(*nested, pos)) {
                    annotations.push(found);
                }
            }
            line_start = line_start + BytePos(u32::try_from(line.len()).unwrap());
        }
        Ok(annotations)
    }

    fn push(&mut self, found: MarkerMatch<'_>) {
        match found.kind {
            AnnotationKind::Expected => self.expected.push(found.payload.to_string()),
            AnnotationKind::Forbidden => self.forbidden.push(found.payload.to_string()),
            AnnotationKind::LifetimeDisplay => self
                .lifetime_display
                .push(LifetimeRenderAnnotation::parse(found.payload)),
        }
    }

    pub(crate) fn expected(&self) -> &[String] {
        &self.expected
    }

    pub(crate) fn forbidden(&self) -> &[String] {
        &self.forbidden
    }

    pub(crate) fn lifetime_display(&self) -> &[LifetimeRenderAnnotation] {
        &self.lifetime_display
    }
}

pub(crate) struct LifetimeRenderAnnotation {
    var: String,
    region_idx: RegionIdx,
    display_as: String,
}

impl LifetimeRenderAnnotation {
    fn parse(payload: &str) -> Self {
        let parts = payload.split(' ').collect::<Vec<_>>();
        assert_eq!(
            parts.len(),
            3,
            "PCG_LIFETIME_DISPLAY takes <var> <region index> <name>, got: {payload}"
        );
        Self {
            var: parts[0].to_string(),
            region_idx: parts[1].parse::<usize>().unwrap().into(),
            display_as: parts[2].to_string(),
        }
    }

    fn get_place<'tcx>(&self, tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> Place<'tcx> {
        if self.var.starts_with('_')
            && let Ok(idx) = self.var.split_at(1).1.parse::<usize>()
        {
            let local: Local = idx.into();
            local.into()
        } else {
            CompilerCtxt::new(body, tcx, ())
                .local_place(self.var.as_str())
                .unwrap()
        }
    }

    pub(crate) fn to_pair<'tcx>(
        &self,
        tcx: TyCtxt<'tcx>,
        body: &Body<'tcx>,
    ) -> (RegionVid, String) {
        let place = self.get_place(tcx, body);
        let region: PcgRegion = place.regions(CompilerCtxt::new(body, tcx, ()))[self.region_idx];
        (region.vid().unwrap(), self.display_as.clone())
    }
}
