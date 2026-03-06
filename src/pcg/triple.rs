// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{
    pcg::OwnedCapability,
    rustc_interface::middle::mir::{
        self, BorrowKind, Local, Location, Operand, RETURN_PLACE, Rvalue, Statement, StatementKind,
        Terminator, TerminatorKind,
    },
};

#[rustversion::before(2025-03-02)]
use crate::rustc_interface::middle::mir::Mutability;

#[rustversion::since(2025-03-02)]
use crate::rustc_interface::middle::mir::RawPtrKind;

use crate::{
    error::{PcgError, PcgUnsupportedError},
    pcg::PositiveCapability,
    utils::{CompilerCtxt, Place, visitor::FallableVisitor},
};

#[derive(Debug, Clone)]
pub(crate) struct Triple<'tcx> {
    pre: PlacePrecondition<'tcx>,
    post: PlacePostcondition<'tcx>,
}

impl<'tcx> Triple<'tcx> {
    pub(crate) fn new(pre: PlacePrecondition<'tcx>, post: PlacePostcondition<'tcx>) -> Self {
        Self { pre, post }
    }

    pub fn pre(&self) -> &PlacePrecondition<'tcx> {
        &self.pre
    }

    pub fn post(&self) -> PlacePostcondition<'tcx> {
        self.post
    }
}

#[derive(Debug, Clone)]
pub(crate) enum PlacePrecondition<'tcx> {
    IfAllocated(Local, Box<PlacePrecondition<'tcx>>),
    Capability(Place<'tcx>, PositiveCapability),
    True,
}

#[derive(Debug, Clone, Copy)]
pub(crate) enum PlacePostcondition<'tcx> {
    Capability(Place<'tcx>, OwnedCapability),
    Unalloc(Local),
    Alloc(Local),
    True,
}

pub(crate) struct TripleWalker<'a, 'tcx: 'a> {
    /// Evaluate all Operands/Rvalues
    pub(crate) operand_triples: Vec<Triple<'tcx>>,
    /// Evaluate all other statements/terminators
    pub(crate) main_triples: Vec<Triple<'tcx>>,
    pub(crate) ctxt: CompilerCtxt<'a, 'tcx>,
}

impl<'a, 'tcx> TripleWalker<'a, 'tcx> {
    pub(crate) fn new(ctxt: CompilerCtxt<'a, 'tcx>) -> Self {
        Self {
            operand_triples: Vec::new(),
            main_triples: Vec::new(),
            ctxt,
        }
    }
}
impl<'tcx> FallableVisitor<'tcx> for TripleWalker<'_, 'tcx> {
    fn visit_operand_fallable(
        &mut self,
        operand: &mir::Operand<'tcx>,
        location: mir::Location,
    ) -> Result<(), PcgError<'tcx>> {
        self.super_operand_fallable(operand, location)?;
        #[allow(clippy::match_same_arms)]
        let triple = match *operand {
            Operand::Copy(place) => {
                let place = Place::from_mir_place(place, self.ctxt);
                Triple {
                    pre: PlacePrecondition::Capability(place, PositiveCapability::Read),
                    post: PlacePostcondition::True,
                }
            }
            Operand::Move(place) => {
                let place = Place::from_mir_place(place, self.ctxt);
                Triple {
                    pre: PlacePrecondition::Capability(place, PositiveCapability::Exclusive),
                    post: PlacePostcondition::Capability(place, OwnedCapability::Uninitialized),
                }
            }
            Operand::Constant(..) => return Ok(()),
            #[allow(unreachable_patterns)]
            _ => return Ok(()),
        };
        self.operand_triples.push(triple);
        Ok(())
    }

    #[allow(unreachable_patterns)]
    fn visit_rvalue_fallable(
        &mut self,
        rvalue: &mir::Rvalue<'tcx>,
        location: mir::Location,
    ) -> Result<(), PcgError<'tcx>> {
        self.super_rvalue_fallable(rvalue, location)?;
        use Rvalue::{
            Aggregate, BinaryOp, Cast, CopyForDeref, Discriminant, RawPtr, Ref, Repeat,
            ShallowInitBox, ThreadLocalRef, UnaryOp, Use,
        };
        let triple = match rvalue {
            Use(_)
            | Repeat(_, _)
            | ThreadLocalRef(_)
            | Cast(_, _, _)
            | BinaryOp(_, _)
            | UnaryOp(_, _)
            | Aggregate(_, _)
            | ShallowInitBox(_, _) => return Ok(()),
            &Ref(_, kind, place) => {
                let place = Place::from_mir_place(place, self.ctxt);
                match kind {
                    BorrowKind::Shared => Triple::new(
                        PlacePrecondition::Capability(place, PositiveCapability::Read),
                        PlacePostcondition::True,
                    ),
                    BorrowKind::Fake(..) => return Ok(()),
                    BorrowKind::Mut { .. } => Triple::new(
                        PlacePrecondition::Capability(place, PositiveCapability::Exclusive),
                        PlacePostcondition::True,
                    ),
                }
            }
            &RawPtr(mutbl, place) => {
                let place = Place::from_mir_place(place, self.ctxt);
                #[rustversion::since(2025-03-02)]
                let pre = if matches!(mutbl, RawPtrKind::Mut) {
                    PlacePrecondition::Capability(place, PositiveCapability::Exclusive)
                } else {
                    PlacePrecondition::Capability(place, PositiveCapability::Read)
                };
                #[rustversion::before(2025-03-02)]
                let pre = if matches!(mutbl, Mutability::Mut) {
                    PlacePrecondition::Capability(place, PositiveCapability::Exclusive)
                } else {
                    PlacePrecondition::Capability(place, PositiveCapability::Read)
                };
                Triple::new(pre, PlacePostcondition::True)
            }
            &Discriminant(place) | &CopyForDeref(place) => {
                let place = Place::from_mir_place(place, self.ctxt);
                Triple::new(
                    PlacePrecondition::Capability(place, PositiveCapability::Read),
                    PlacePostcondition::True,
                )
            }
            other => {
                #[rustversion::since(2026-01-01)]
                {
                    assert!(matches!(other, Rvalue::WrapUnsafeBinder(_, _)));
                    return Ok(());
                }
                #[rustversion::before(2026-01-01)]
                {
                    match other {
                        &Rvalue::Len(place) => {
                            let place = Place::from_mir_place(place, self.ctxt);
                            Triple::new(
                                PlacePrecondition::Capability(place, PositiveCapability::Read),
                                PlacePostcondition::True,
                            )
                        }
                        Rvalue::NullaryOp(_, _) => return Ok(()),
                        _ => todo!("{other:?}"),
                    }
                }
            }
        };
        self.operand_triples.push(triple);
        Ok(())
    }

    fn visit_statement_fallable(
        &mut self,
        statement: &Statement<'tcx>,
        location: Location,
    ) -> Result<(), PcgError<'tcx>> {
        self.super_statement_fallable(statement, location)?;
        use StatementKind::{Assign, FakeRead, Retag, SetDiscriminant, StorageDead, StorageLive};
        let t = match statement.kind {
            Assign(box (place, ref rvalue)) => {
                let place = Place::from_mir_place(place, self.ctxt);
                Triple {
                    pre: PlacePrecondition::Capability(place, PositiveCapability::Write),
                    post: rvalue
                        .capability()
                        .and_then(PositiveCapability::into_owned_capability)
                        .map_or(PlacePostcondition::True, |cap| {
                            PlacePostcondition::Capability(place, cap)
                        }),
                }
            }
            FakeRead(box (_, place)) => {
                let place = Place::from_mir_place(place, self.ctxt);
                Triple {
                    pre: PlacePrecondition::Capability(place, PositiveCapability::Read),
                    post: PlacePostcondition::True,
                }
            }
            SetDiscriminant { box place, .. } | Retag(_, box place) => {
                let place = Place::from_mir_place(place, self.ctxt);
                Triple {
                    pre: PlacePrecondition::Capability(place, PositiveCapability::Exclusive),
                    post: PlacePostcondition::True,
                }
            }
            StorageLive(local) => Triple {
                pre: PlacePrecondition::True,
                post: PlacePostcondition::Alloc(local),
            },
            StorageDead(local) => Triple {
                pre: PlacePrecondition::IfAllocated(
                    local,
                    Box::new(PlacePrecondition::Capability(local.into(), PositiveCapability::Write)),
                ),
                post: PlacePostcondition::Unalloc(local),
            },
            _ => return Ok(()),
        };
        self.main_triples.push(t);
        Ok(())
    }

    fn visit_terminator_fallable(
        &mut self,
        terminator: &Terminator<'tcx>,
        location: mir::Location,
    ) -> Result<(), PcgError<'tcx>> {
        self.super_terminator_fallable(terminator, location)?;
        use TerminatorKind::{
            Assert, Call, CoroutineDrop, Drop, FalseEdge, FalseUnwind, Goto, InlineAsm, Return,
            SwitchInt, Unreachable, UnwindResume, UnwindTerminate, Yield,
        };
        let t = match &terminator.kind {
            Goto { .. }
            | SwitchInt { .. }
            | UnwindResume
            | UnwindTerminate(_)
            | Unreachable
            | CoroutineDrop
            | Assert { .. }
            | FalseEdge { .. }
            | FalseUnwind { .. } => return Ok(()),
            Return => {
                let place = Place::from_mir_place(RETURN_PLACE.into(), self.ctxt);
                Triple {
                    pre: PlacePrecondition::True,
                    post: PlacePostcondition::Capability(place, OwnedCapability::Uninitialized),
                }
            }
            &Drop { place, .. } => {
                let place = Place::from_mir_place(place, self.ctxt);
                Triple {
                    pre: PlacePrecondition::Capability(place, PositiveCapability::Write),
                    post: PlacePostcondition::True,
                }
            }
            &Call { destination, .. } => {
                let destination = Place::from_mir_place(destination, self.ctxt);
                Triple {
                    pre: PlacePrecondition::Capability(destination, PositiveCapability::Write),
                    post: PlacePostcondition::Capability(destination, OwnedCapability::Deep),
                }
            }
            &Yield { resume_arg, .. } => {
                let resume_arg = Place::from_mir_place(resume_arg, self.ctxt);
                Triple {
                    pre: PlacePrecondition::Capability(resume_arg, PositiveCapability::Write),
                    post: PlacePostcondition::Capability(resume_arg, OwnedCapability::Deep),
                }
            }
            InlineAsm { .. } => {
                return Err(PcgError::unsupported(PcgUnsupportedError::InlineAssembly));
            }
            _ => todo!("{terminator:?}"),
        };
        self.main_triples.push(t);
        Ok(())
    }

    fn visit_place_fallable(
        &mut self,
        place: Place<'tcx>,
        _context: mir::visit::PlaceContext,
        _location: mir::Location,
    ) -> Result<(), PcgError<'tcx>> {
        if place.contains_unsafe_deref(self.ctxt) {
            return Err(PcgError::unsupported(PcgUnsupportedError::DerefUnsafePtr));
        }
        Ok(())
    }

    fn to_place(&self, place: mir::Place<'tcx>) -> Place<'tcx> {
        Place::from_mir_place(place, self.ctxt)
    }
}

trait ProducesCapability {
    fn capability(&self) -> Option<PositiveCapability>;
}

impl ProducesCapability for Rvalue<'_> {
    #[allow(unreachable_patterns)]
    fn capability(&self) -> Option<PositiveCapability> {
        use Rvalue::{
            Aggregate, BinaryOp, Cast, CopyForDeref, Discriminant, RawPtr, Ref, Repeat,
            ShallowInitBox, ThreadLocalRef, UnaryOp, Use,
        };
        match self {
            Ref(_, BorrowKind::Fake(_), _) => None,
            Use(_)
            | Repeat(_, _)
            | Ref(_, _, _)
            | RawPtr(_, _)
            | ThreadLocalRef(_)
            | Cast(_, _, _)
            | BinaryOp(_, _)
            | UnaryOp(_, _)
            | Discriminant(_)
            | Aggregate(_, _)
            | CopyForDeref(_) => Some(PositiveCapability::Exclusive),
            ShallowInitBox(_, _) => Some(PositiveCapability::ShallowExclusive),
            _ => {
                #[rustversion::before(2026-01-01)]
                {
                    assert!(matches!(self, Rvalue::Len(_) | Rvalue::NullaryOp(_, _)));
                    Some(PositiveCapability::Exclusive)
                }
                #[rustversion::since(2026-01-01)]
                {
                    assert!(matches!(self, Rvalue::WrapUnsafeBinder(_, _)));
                    Some(PositiveCapability::Exclusive)
                }
            }
        }
    }
}
