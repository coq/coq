open Utest

let unicode0 = mk_eq_test "clib-unicode0"
                 "split_at_first_letter, first letter is character"
                 None
                 (Unicode.split_at_first_letter "ident")

let unicode1 = mk_eq_test "clib-unicode1"
                 "split_at_first_letter, first letter not character"
                 (Some ("__","ident"))
                 (Unicode.split_at_first_letter "__ident")

let tests = [ unicode0; unicode1 ]

let _ = run_tests __FILE__ tests
