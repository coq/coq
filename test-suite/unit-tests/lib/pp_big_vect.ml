open OUnit
open Pp

let pr_big_vect =
  let n = "pr_big_vect" in
  n >:: (fun () ->
      let v = Array.make (1 lsl 20) () in
      let pp = prvecti_with_sep spc (fun _ _ -> str"x") v in
      let str = string_of_ppcmds pp in
      ignore(str))

let tests = [pr_big_vect]

let () = Utest.run_tests __FILE__ (Utest.open_log_out_ch __FILE__) tests
