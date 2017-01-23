open Ltac_plugin
DECLARE PLUGIN "test_plugin"
let () = Mltop.add_known_plugin (fun () -> ()) "test_plugin";;

VERNAC COMMAND EXTEND Test CLASSIFIED AS SIDEFF
  | [ "TestCommand" ] -> [ () ]
END

TACTIC EXTEND test
| [ "test_tactic" ] -> [ Test_aux.tac ]
END



