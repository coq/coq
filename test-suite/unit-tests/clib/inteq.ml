open Utest

let log_out_ch = open_log_out_ch __FILE__

let eq0 = mk_bool_test "clib-inteq0"
            "CInt.equal on 0"
            (CInt.equal 0 0)

let eq42 = mk_bool_test "clib-inteq42"
             "CInt.equal on 42"
             (CInt.equal 42 42)

let tests = [ eq0; eq42 ]

let _ = run_tests __FILE__ log_out_ch tests
