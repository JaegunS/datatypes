use common::*;
use std::collections::HashSet;

/* ----------------------------- Error Handling ----------------------------- */

#[repr(u64)]
pub enum SnakeErr {
    ArithmeticOverflow = 0,
    ExpectedNum = 1,
    ExpectedBool = 2,
    ExpectedArray = 3,
    NegativeLength = 4,
    IndexOutOfBounds = 5,
}

#[export_name = "\u{1}snake_error"]
pub extern "C" fn snake_error(ecode: SnakeErr, v: SnakeValue) -> SnakeValue {
    match ecode {
        SnakeErr::ArithmeticOverflow => eprintln!("arithmetic operation overflowed"),
        SnakeErr::ExpectedNum => eprintln!("expected a number, got {}", sprint_snake_val(v)),
        SnakeErr::ExpectedBool => eprintln!("expected a boolean, got {}", sprint_snake_val(v)),
        SnakeErr::ExpectedArray => eprintln!("expected an array, got {}", sprint_snake_val(v)),
        SnakeErr::NegativeLength => eprintln!("length {} is negative", sprint_snake_val(v)),
        SnakeErr::IndexOutOfBounds => eprintln!("index {} out of bounds", sprint_snake_val(v)),
    }
    std::process::exit(1)
}

/* ---------------------------- Print Snake Value --------------------------- */

/* Implement the following function for printing a snake value.
**/
pub fn sprint_snake_val(x: SnakeValue) -> String {
    todo!("implement this")
}
