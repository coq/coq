DECLARE PLUGIN "test_plugin"
let () = Mltop.add_known_plugin (fun () -> ()) "test_plugin";;

VERNAC COMMAND EXTEND Test CLASSIFIED AS SIDEFF
  | [ "Test" ] -> [ () ]
END

TACTIC EXTEND test
| [ "test" ] -> [ Test_aux.tac ]
END



