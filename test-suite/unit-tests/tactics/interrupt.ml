(* An IDE stops a running tactic by setting [Control.interrupt]. [tclREPEAT0]
   reads the flag on every pass, [tclDO] did not. See rocq#22433. *)

open Utest

let log_out_ch = open_log_out_ch __FILE__

(* Empty proofview: [tclDO] does not look at goals. The flag is cleared on the
   way out, by hand when the break did not fire, so it cannot leak. *)
let t1 =
  let count = ref 0 in
  let body =
    Proofview.tclBIND (Proofview.tclUNIT ()) (fun () -> incr count; Proofview.tclUNIT ())
  in
  let _, pv = Proofview.init Evd.empty [] in
  let name = Names.Id.of_string "tacticals_interrupt_test" in
  Control.interrupt := true;
  let broke =
    try
      let _ =
        Proofview.apply ~name ~poly:PolyFlags.default Environ.empty_env
          (Tacticals.tclDO 1000 body) pv
      in
      false
    with Sys.Break -> true
  in
  Control.interrupt := false;
  mk_bool_test "tactics-interrupt0"
    "do N tac stops within one iteration of an interrupt (rocq#22433)"
    (broke && !count = 1)

let tests = [ t1 ]

let _ = run_tests __FILE__ log_out_ch tests
