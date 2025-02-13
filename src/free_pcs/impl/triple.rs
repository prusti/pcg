// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use rustc_interface::middle::mir::{
    visit::Visitor, BorrowKind, Local, Location, Operand, ProjectionElem, Rvalue, Statement,
    StatementKind, Terminator, TerminatorKind, RETURN_PLACE,
};

use crate::{
    combined_pcs::{PCGError, PCGUnsupportedError},
    free_pcs::CapabilityKind,
    rustc_interface,
    utils::{Place, PlaceRepacker},
};

#[derive(Debug, Clone, Copy)]
pub(crate) struct Triple<'tcx> {
    pre: Condition<'tcx>,
    post: Option<Condition<'tcx>>,
}

impl<'tcx> Triple<'tcx> {
    pub fn pre(self) -> Condition<'tcx> {
        self.pre
    }
    pub fn post(self) -> Option<Condition<'tcx>> {
        self.post
    }

    /// Replace all places in the `Condition` with ones that are just above the
    /// first dereference of a ref.
    pub fn replace_place<'b>(self, repacker: PlaceRepacker<'b, 'tcx>) -> Self {
        Self {
            pre: self.pre.fpcg_condition(repacker),
            post: self.post.map(|c| c.fpcg_condition(repacker)),
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub(crate) enum Condition<'tcx> {
    Capability(Place<'tcx>, CapabilityKind),
    AllocateOrDeallocate(Local),
    Unalloc(Local),
    Return,
}

impl<'tcx> Condition<'tcx> {
    fn new<T: Into<Place<'tcx>>>(place: T, capability: CapabilityKind) -> Condition<'tcx> {
        Condition::Capability(place.into(), capability)
    }

    fn exclusive<T: Into<Place<'tcx>>>(place: T) -> Condition<'tcx> {
        Self::new(place, CapabilityKind::Exclusive)
    }

    fn lent<T: Into<Place<'tcx>>>(place: T) -> Condition<'tcx> {
        Self::new(place, CapabilityKind::Lent)
    }

    fn write<T: Into<Place<'tcx>>>(place: T) -> Condition<'tcx> {
        Self::new(place, CapabilityKind::Write)
    }

    fn read<T: Into<Place<'tcx>>>(place: T) -> Condition<'tcx> {
        Self::new(place, CapabilityKind::Read)
    }

    /// Returns the condition for the place in the free PCG. If the place is
    /// already in the free PCG, this will be the same condition. However, if
    /// the place is in the borrow PCG, we must have an exclusive access to the
    /// corresponding place in the free PCG, e.g., obtaining "Write" capability
    /// to *_2 requires an exclusive capability to _2
    pub fn fpcg_condition<'b>(self, repacker: PlaceRepacker<'b, 'tcx>) -> Self {
        match self {
            Condition::Capability(place, kind) => {
                let fpcg_place = get_place_to_expand_to(place, repacker);
                let capability_kind = if place != fpcg_place {
                    CapabilityKind::Exclusive
                } else {
                    kind
                };
                Condition::Capability(fpcg_place, capability_kind)
            }
            _ => self,
        }
    }
}

fn get_place_to_expand_to<'b, 'tcx>(
    place: Place<'tcx>,
    repacker: PlaceRepacker<'b, 'tcx>,
) -> Place<'tcx> {
    let mut curr_place: Place<'tcx> = place.local.into();
    for elem in place.projection {
        if *elem == ProjectionElem::Deref && curr_place.ty(repacker).ty.is_ref() {
            return curr_place;
        }

        // For some reason the field projection may yield a different lifetime parameter
        // what is expected based on the ADT definition and substs.
        // We use the ADT definition because it will ensure that in the PCS the lifetime parameter
        // of all fields relates to the parameter of their parent struct.
        curr_place = curr_place
            .mk_place_elem(*elem, repacker)
            .with_inherent_region(repacker);
    }
    return curr_place;
}

#[derive(Debug, Default)]
pub(crate) struct TripleWalker<'tcx> {
    /// Evaluate all Operands/Rvalues
    pub(crate) operand_triples: Vec<Triple<'tcx>>,
    /// Evaluate all other statements/terminators
    pub(crate) main_triples: Vec<Triple<'tcx>>,

    pub(crate) error: Option<PCGError>,
}

impl<'tcx> Visitor<'tcx> for TripleWalker<'tcx> {
    fn visit_operand(&mut self, operand: &Operand<'tcx>, location: Location) {
        self.super_operand(operand, location);
        let triple = match *operand {
            Operand::Copy(place) => Triple {
                pre: Condition::read(place),
                post: None,
            },
            Operand::Move(place) => Triple {
                pre: Condition::exclusive(place),
                post: Some(Condition::write(place)),
            },
            Operand::Constant(..) => return,
        };
        self.operand_triples.push(triple);
    }

    fn visit_rvalue(&mut self, rvalue: &Rvalue<'tcx>, location: Location) {
        self.super_rvalue(rvalue, location);
        use Rvalue::*;
        let pre = match rvalue {
            Use(_)
            | Repeat(_, _)
            | ThreadLocalRef(_)
            | Cast(_, _, _)
            | BinaryOp(_, _)
            | NullaryOp(_, _)
            | UnaryOp(_, _)
            | Aggregate(_, _)
            | ShallowInitBox(_, _) => return,

            &Ref(_, kind, place) => match kind {
                BorrowKind::Shared => Condition::read(place),
                BorrowKind::Fake(..) => return,
                BorrowKind::Mut { .. } => Condition::exclusive(place),
            },
            &RawPtr(mutbl, place) => {
                if mutbl.is_mut() {
                    Condition::exclusive(place)
                } else {
                    Condition::read(place)
                }
            }
            &Len(place) | &Discriminant(place) | &CopyForDeref(place) => Condition::read(place),
        };
        self.operand_triples.push(Triple { pre, post: None });
    }

    fn visit_statement(&mut self, statement: &Statement<'tcx>, location: Location) {
        self.super_statement(statement, location);
        use StatementKind::*;
        let t = match &statement.kind {
            &Assign(box (place, ref rvalue)) => Triple {
                pre: Condition::write(place),
                post: rvalue.capability().map(|cap| Condition::new(place, cap)),
            },
            &FakeRead(box (_, place)) => Triple {
                pre: Condition::exclusive(place),
                post: None,
            },
            // Looking into `rustc` it seems that `PlaceMention` is effectively ignored.
            &PlaceMention(_) => return,
            &SetDiscriminant { box place, .. } => Triple {
                pre: Condition::exclusive(place),
                post: None,
            },
            &Deinit(box place) => Triple {
                pre: Condition::exclusive(place),
                post: Some(Condition::write(place)),
            },
            &StorageLive(local) => Triple {
                pre: Condition::Unalloc(local),
                post: Some(Condition::AllocateOrDeallocate(local)),
            },
            &StorageDead(local) => Triple {
                pre: Condition::AllocateOrDeallocate(local),
                post: Some(Condition::Unalloc(local)),
            },
            &Retag(_, box place) => Triple {
                pre: Condition::exclusive(place),
                post: None,
            },
            _ => return,
        };
        self.main_triples.push(t);
        if let Assign(box (_, Rvalue::Ref(_, kind, place))) = &statement.kind {
            let triple = match kind {
                BorrowKind::Shared => Triple {
                    pre: Condition::read(*place),
                    post: Some(Condition::read(*place)),
                },
                BorrowKind::Fake(..) => return,
                BorrowKind::Mut { .. } => Triple {
                    pre: Condition::exclusive(*place),
                    post: Some(Condition::lent(*place)),
                },
            };
            self.main_triples.push(triple);
        }
    }

    fn visit_terminator(&mut self, terminator: &Terminator<'tcx>, location: Location) {
        self.super_terminator(terminator, location);
        use TerminatorKind::*;
        let t = match &terminator.kind {
            Goto { .. }
            | SwitchInt { .. }
            | UnwindResume
            | UnwindTerminate(_)
            | Unreachable
            | Assert { .. }
            | FalseEdge { .. }
            | FalseUnwind { .. } => return,
            Return => Triple {
                pre: Condition::Return,
                post: Some(Condition::write(RETURN_PLACE)),
            },
            &Drop { place, .. } => Triple {
                pre: Condition::write(place),
                post: None,
            },
            &Call { destination, .. } => Triple {
                pre: Condition::write(destination),
                post: Some(Condition::exclusive(destination)),
            },
            &Yield { resume_arg, .. } => Triple {
                pre: Condition::write(resume_arg),
                post: Some(Condition::exclusive(resume_arg)),
            },
            InlineAsm { .. } => {
                self.error = Some(PCGError::Unsupported(PCGUnsupportedError::InlineAssembly));
                return;
            }
            CoroutineDrop => todo!(),
            _ => todo!("{terminator:?}"),
        };
        self.main_triples.push(t);
    }
}

trait ProducesCapability {
    fn capability(&self) -> Option<CapabilityKind>;
}

impl ProducesCapability for Rvalue<'_> {
    fn capability(&self) -> Option<CapabilityKind> {
        use Rvalue::*;
        match self {
            Ref(_, BorrowKind::Fake(_), _) => None,
            Use(_)
            | Repeat(_, _)
            | Ref(_, _, _)
            | RawPtr(_, _)
            | ThreadLocalRef(_)
            | Len(_)
            | Cast(_, _, _)
            | BinaryOp(_, _)
            | NullaryOp(_, _)
            | UnaryOp(_, _)
            | Discriminant(_)
            | Aggregate(_, _)
            | CopyForDeref(_) => Some(CapabilityKind::Exclusive),
            ShallowInitBox(_, _) => Some(CapabilityKind::ShallowExclusive),
        }
    }
}
