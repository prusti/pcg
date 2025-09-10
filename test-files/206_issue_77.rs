pub struct Fields {
    pub field_1: u32,
    pub field_2: (),
}

#[repr(i8)]
enum Enum {
    VariantA = 0,
    VariantB(Fields, Option<bool>) = -128,
    VariantC {
        field_1: u32,
        field_2: (),
    } = 127,
}

pub fn enum_test(e: Enum, v: u8) {
    match v {
        0 => {
            let value = match e {
                Enum::VariantA => {
                    0
                }
                Enum::VariantB(f, _) => {
                    f.field_1
                }
                Enum::VariantC { field_1, field_2 } => {
                    field_1
                }
            };
        }
        1 => {
            let Enum::VariantB(a, b) = e else {
                return;
            };
        }
        2 => {
            if let Enum::VariantC { field_1, field_2 } = e {

            } else {
                return;
            }
        }
        _ => {
            return;
        }
    }
    // PCG: bb14[0] post_main: e: W
}

fn main(){}
