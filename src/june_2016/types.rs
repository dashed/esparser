// rust imports

use std::mem;

// 3rd-party imports

use enum_set::{EnumSet, CLike};

// Ref: https://is.gd/kEGYIp
// TODO: `ag is_debug_mode` should return only 1 result
macro_rules! ensure_params {
    ($input:expr; $callee:expr; $( $test:expr );*) => {

        if is_debug_mode!() {

            // validation
            if !($input.is_empty() $(|| $input.contains(& $test ))*) {
                panic!("misuse of {}", $callee);
            }

        }
    };
}

// TODO: better name
macro_rules! iterable_enum {
    (enum $enum_name:ident { $( $enum_item:ident,)* } ) => (

        #[repr(u32)]
        #[derive(Clone)]
        pub enum $enum_name {
            $($enum_item,)*
        }

        impl CLike for $enum_name {
            fn to_u32(&self) -> u32 {
                let encoded: Self = self.clone();
                encoded as u32
            }

            unsafe fn from_u32(v: u32) -> Self {
                mem::transmute(v)
            }
        }

        // Return vector containing all the enum values
        impl $enum_name {
            fn make_vec() -> Vec<Self> {
                vec![$($enum_name::$enum_item,)*]
            }
        }
    )
}

// Based on: http://www.ecma-international.org/ecma-262/7.0/#sec-grammar-notation
//
// Used to conditionally include or exclude production grammar rules.
iterable_enum!(
    enum Parameter {
        In,
        Yield,
        Return,
        Default,
    }
);

pub type Parameters = EnumSet<Parameter>;
