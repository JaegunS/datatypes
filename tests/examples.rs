macro_rules! mk_test {
    ($test_name:ident, $file_name:expr, $input:expr, $expected_output:expr) => {
        #[test]
        fn $test_name() -> std::io::Result<()> {
            test_example_file($file_name, $input, $expected_output)
        }
    };
}

macro_rules! mk_frontend_test {
    ($test_name:ident, $file_name:expr, $input:expr, $expected_output:expr) => {
        #[test]
        fn $test_name() -> std::io::Result<()> {
            test_example_frontend($file_name, $input, $expected_output)
        }
    };
}

macro_rules! mk_middle_end_test {
    ($test_name:ident, $file_name:expr, $input:expr, $expected_output:expr) => {
        #[test]
        fn $test_name() -> std::io::Result<()> {
            test_example_middle_end($file_name, $input, $expected_output)
        }
    };
}

macro_rules! mk_fail_test {
    ($test_name:ident, $file_name:expr, $expected_output:expr) => {
        #[test]
        fn $test_name() -> std::io::Result<()> {
            test_example_fail($file_name, [], $expected_output)
        }
    };
}

macro_rules! mk_dyn_fail_test {
    ($test_name:ident, $file_name:expr, $input:expr, $expected_output:expr) => {
        #[test]
        fn $test_name() -> std::io::Result<()> {
            test_example_fail($file_name, $input, $expected_output)
        }
    };
}

/*
 * YOUR TESTS GO HERE
 */

mod public_adder {
    use super::*;
    /* The following defines a test named "test1" that compiles and runs the file
     * examples/add1.dbk and I expect it to return 43 with input 42
     */
    mk_test!(test1, "add1.dbk", ["42"], "43");

    /* The following test is similar to test1, but instead of using the
     * full compiler pipeline, it runs the frontend and then tests that
     * the interpreter outputs the desired result
     */
    mk_frontend_test!(test1_frontend, "add1.dbk", ["42"], "43");

    /* Similarly, the following test uses your frontend followed by your
     * middleend, then runs the SSA interpreter on the resulting
     * intermediate representation.
     */
    mk_middle_end_test!(test1_middleend, "add1.dbk", ["42"], "43");

    /*
     * The following test checks that when run on exmaples/free.dbk, the
     * compiler produces an error containing the substring "variable z unbound".
     */
    mk_fail_test!(free, "free.dbk", "variable \"z\" unbound");

    mk_fail_test!(let_dupe, "let_dupe.dbk", "\"x\" defined twice in let-expression");
}

/* ----------------------- Public Cobra Tests ---------------------- */
mod public_cobra {
    use super::*;
    // one regression test for tail recursion
    mk_test!(test_tail_recursive_constant_space_3, "peano.dbk", ["100000000"], "100000001");
    // one for testing extern with few arguments
    mk_test!(test_print_3, "print.dbk", ["0"], "1\n2\n3\n4\n24");
    // one for testing extern with many arguments
    mk_test!(
        test_big_extern_nine_3,
        "extern_big_nine.dbk",
        ["0"],
        "x1: -1
x2: -2
x3: -3
x4: -4
x5: -5
x6: -6
x7: -7
x8: -8
x9: -9
-46
"
    );
    // one for testing internal call with few arguments
    mk_test!(test_simple_non_tail_call_1_3, "local_non_tail_call.dbk", ["1"], "3");
    // one for testing internal call with many arguments
    mk_test!(test_big_local_3, "local_big_eight.dbk", ["1"], "40319");
    // one for testing internal call with recursion
    mk_test!(test_non_tail_recursion_3, "non_tail_factorial.dbk", ["5"], "120");
    // one for testing recursive internal call with capture
    mk_test!(test_rec_call_capture_3, "pow.dbk", ["2"], "256");
}

mod public_diamondback {
    use super::*;
    mk_dyn_fail_test!(test_out_of_bounds, "out_of_bounds.dbk", [], "index 4 out of bounds");
    mk_dyn_fail_test!(test_overflow_3_2, "overflow3.dbk", [], "arithmetic operation overflowed");
    mk_test!(test_array_empty_2, "array_empty.dbk", ["483"], "[[], 483, []]");
    mk_test!(
        test_array_cyclic_tree,
        "array_cyclic_tree.dbk",
        ["0", "0", "0"],
        "[[395, 476, 1453, <loop>], 0, [[], <loop>, <loop>, [395, 476, 1453, <loop>], <loop>, []]]"
    );
}
/*
 * YOUR TESTS END HERE
 */

/* ----------------------- Test Implementation Details ---------------------- */

use diamondback::{interp, runner};
use std::path::Path;

fn test_example_file(
    f: &str, args: impl IntoIterator<Item = &'static str>, expected: &str,
) -> std::io::Result<()> {
    let tmp_dir = tempfile::TempDir::new()?;
    let mut buf = Vec::new();
    match runner::compile_and_run_file(
        &Path::new(&format!("examples/{}", f)),
        tmp_dir.path(),
        args,
        &mut buf,
    ) {
        Ok(()) => {
            assert_eq!(String::from_utf8_lossy(&buf).trim(), expected.trim())
        }
        Err(e) => {
            assert!(false, "Expected {}, got an error: {}", expected, e)
        }
    }
    Ok(())
}

#[allow(unused)]
fn test_example_frontend(
    f: &str, args: impl IntoIterator<Item = &'static str>, expected: &str,
) -> std::io::Result<()> {
    let res = runner::emit_ast(&Path::new(&format!("examples/{}", f)))
        .and_then(|(_, ast)| interp::ast::Machine::run(&ast, args).map_err(|e| format!("{}", e)));
    match res {
        Ok(v) => assert_eq!(v.to_string(), expected),
        Err(e) => assert!(false, "Expected {}, got an error: {}", expected, e),
    }
    Ok(())
}

#[allow(unused)]
fn test_example_middle_end(
    f: &str, args: impl IntoIterator<Item = &'static str>, expected: &str,
) -> std::io::Result<()> {
    let res = runner::emit_ssa(&Path::new(&format!("examples/{}", f))).and_then(|(_, ssa)| {
        let mut interp = interp::ssa::Interp::new();
        interp.run(&ssa, args).map_err(|e| format!("{}", e))
    });
    match res {
        Ok(v) => assert_eq!(v.to_string(), expected),
        Err(e) => assert!(false, "Expected {}, got an error: {}", expected, e),
    }
    Ok(())
}

fn test_example_fail(
    f: &str, args: impl IntoIterator<Item = &'static str>, includes: &str,
) -> std::io::Result<()> {
    let tmp_dir = tempfile::TempDir::new()?;
    let mut buf = Vec::new();
    match runner::compile_and_run_file(
        &Path::new(&format!("examples/{}", f)),
        tmp_dir.path(),
        args,
        &mut buf,
    ) {
        Ok(()) => {
            assert!(false, "Expected a failure but got: {}", String::from_utf8_lossy(&buf).trim())
        }
        Err(e) => {
            let msg = format!("{}", e);
            assert!(
                msg.contains(includes),
                "Expected error message to include the string \"{}\" but got the error: {}",
                includes,
                msg
            )
        }
    }
    Ok(())
}
