use crate::rustc_interface::middle::mir::ProjectionElem;
use crate::utils::Place;
use std::fmt::{Debug, Formatter, Result};


impl Debug for Place<'_> {
    fn fmt(&self, fmt: &mut Formatter) -> Result {
        for elem in self.projection.iter().rev() {
            match elem {
                ProjectionElem::OpaqueCast(_) | ProjectionElem::Downcast(_, _) => {
                    write!(fmt, "(").unwrap();
                }
                ProjectionElem::Deref => {
                    write!(fmt, "(*").unwrap();
                }
                ProjectionElem::Field(_, _)
                | ProjectionElem::Index(_)
                | ProjectionElem::ConstantIndex { .. }
                | ProjectionElem::Subslice { .. } => {}
                _ => todo!(),
            }
        }

        write!(fmt, "{:?}", self.local)?;

        for &elem in self.projection {
            match elem {
                ProjectionElem::OpaqueCast(ty) => {
                    write!(fmt, "@{ty})")?;
                }
                ProjectionElem::Downcast(Some(name), _index) => {
                    write!(fmt, "@{name})")?;
                }
                ProjectionElem::Downcast(None, index) => {
                    write!(fmt, "@variant#{index:?})")?;
                }
                ProjectionElem::Deref => {
                    write!(fmt, ")")?;
                }
                ProjectionElem::Field(field, _ty) => {
                    write!(fmt, ".{:?}", field.index())?;
                }
                ProjectionElem::Index(ref index) => {
                    write!(fmt, "[{index:?}]")?;
                }
                ProjectionElem::ConstantIndex {
                    offset,
                    min_length,
                    from_end: false,
                } => {
                    write!(fmt, "[{offset:?} of {min_length:?}]")?;
                }
                ProjectionElem::ConstantIndex {
                    offset,
                    min_length,
                    from_end: true,
                } => {
                    write!(fmt, "[-{offset:?} of {min_length:?}]")?;
                }
                ProjectionElem::Subslice {
                    from,
                    to: 0,
                    from_end: true,
                } => {
                    write!(fmt, "[{from:?}:]")?;
                }
                ProjectionElem::Subslice {
                    from: 0,
                    to,
                    from_end: true,
                } => {
                    write!(fmt, "[:-{to:?}]")?;
                }
                ProjectionElem::Subslice {
                    from,
                    to,
                    from_end: true,
                } => {
                    write!(fmt, "[{from:?}:-{to:?}]")?;
                }
                ProjectionElem::Subslice {
                    from,
                    to,
                    from_end: false,
                } => {
                    write!(fmt, "[{from:?}..{to:?}]")?;
                }
                _ => todo!(),
            }
        }

        Ok(())
    }
}
