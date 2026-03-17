mod extensions;
mod common;
use common::*;
use extensions::sprint_snake_val;

static HEAP_SIZE: u64 = 100000;
static mut HEAP_START: [u64; 100000] = [0; 100000];
static mut HEAP_PTR: *mut u64 = unsafe { HEAP_START.as_mut_ptr() };

/* --------------------------- External Functions --------------------------- */

#[export_name = "\u{1}print"]
extern "sysv64" fn print(val: SnakeValue) -> SnakeValue {
    println!("{}", sprint_snake_val(val));
    val
}

#[export_name = "\u{1}big_fun_nine"]
extern "sysv64" fn big_fun_nine(
    x1: SnakeValue, x2: SnakeValue, x3: SnakeValue, x4: SnakeValue, x5: SnakeValue, x6: SnakeValue,
    x7: SnakeValue, x8: SnakeValue, x9: SnakeValue,
) -> SnakeValue {
    println!(
        "x1: {}\nx2: {}\nx3: {}\nx4: {}\nx5: {}\nx6: {}\nx7: {}\nx8: {}\nx9: {}",
        sprint_snake_val(x1),
        sprint_snake_val(x2),
        sprint_snake_val(x3),
        sprint_snake_val(x4),
        sprint_snake_val(x5),
        sprint_snake_val(x6),
        sprint_snake_val(x7),
        sprint_snake_val(x8),
        sprint_snake_val(x9)
    );
    SnakeValue(signed_to_unsigned(
        (0) + unsigned_to_signed(x1.0)
            + unsigned_to_signed(x2.0)
            + unsigned_to_signed(x3.0)
            + unsigned_to_signed(x4.0)
            + unsigned_to_signed(x5.0)
            + unsigned_to_signed(x6.0)
            + unsigned_to_signed(x7.0)
            + unsigned_to_signed(x8.0)
            + unsigned_to_signed(x9.0),
    ))
}

/* ----------------------------- Array Allocator ---------------------------- */

/* Implement the following function for array allocation.
 * Again, feel free to change the function signature if needed.
**/
#[export_name = "\u{1}snake_new_array"]
extern "sysv64" fn snake_new_array(size: u64) -> *mut u64 {
    let arr_ptr = unsafe { HEAP_PTR as u64 };
    unsafe {
        *HEAP_PTR = size;
        if arr_ptr + 8 * (size + 1) >= (HEAP_START.as_ptr() as u64) + 8 * HEAP_SIZE {
            eprintln!("out of memory");
            std::process::exit(1);
        }
        for _i in 0..size {
            HEAP_PTR = HEAP_PTR.add(1);
            *HEAP_PTR = 0;
        }
        HEAP_PTR = HEAP_PTR.add(1)
    }
    arr_ptr as *mut u64
}

/* ---------------------------- Parse Snake Value --------------------------- */

fn parse_snake_basic_val(s: &str) -> SnakeValue {
    let s = s.trim();
    if s == "true" {
        SNAKE_TRU
    } else if s == "false" {
        SNAKE_FLS
    } else if let Ok(x) = s.parse::<i64>() {
        SnakeValue(signed_to_unsigned(x << 1))
    } else {
        panic!("invalid basic snake value: {}", s)
    }
}

/* ------------------------------- Entry Point ------------------------------ */

#[link(name = "compiled_code", kind = "static")]
extern "sysv64" {
    #[link_name = "\u{1}entry"]
    fn entry(param: SnakeValue) -> SnakeValue;
}

fn main() {
    unsafe {
        if HEAP_START.as_ptr() as u64 & FULL_MASK != 0 {
            eprintln!("the heap is misaligned!");
            std::process::exit(1);
        }
    }
    let args: Vec<String> = std::env::args().skip(1).collect();
    let snake_args: Vec<SnakeValue> = args.iter().map(|s| parse_snake_basic_val(s)).collect();
    let snake_arg_array_ptr = snake_new_array(snake_args.len() as u64);
    let snake_arg_array = SnakeValue((snake_arg_array_ptr as u64) | ARRAY_TAG);
    let mut arg_array_ptr = load_snake_array(snake_arg_array_ptr);
    for i in 0..arg_array_ptr.size {
        let idx = i as usize;
        unsafe {
            *arg_array_ptr.elts.wrapping_add(idx) = snake_args[idx];
        }
    }
    let output = unsafe { entry(snake_arg_array) };
    println!("{}", sprint_snake_val(output));
}
