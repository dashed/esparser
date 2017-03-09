// rust imports

use std::mem;

// 3rd-party imports

use enum_set::{EnumSet, CLike};

// Ref: https://is.gd/kEGYIp
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

// Based on: http://www.ecma-international.org/ecma-262/7.0/#sec-grammar-notation
//
// Used to conditionally include or exclude production grammar rules.
#[repr(u32)]
#[derive(Clone)]
pub enum Parameter {
    In,
    Yield,
    Return,
    Default,
}

impl CLike for Parameter {
    fn to_u32(&self) -> u32 {
        let encoded: Self = self.clone();
        encoded as u32
    }

    unsafe fn from_u32(v: u32) -> Self {
        mem::transmute(v)
    }
}

pub type Parameters = EnumSet<Parameter>;
