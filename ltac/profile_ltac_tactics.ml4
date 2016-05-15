(*i camlp4deps: "grammar/grammar.cma" i*)

open Profile_ltac
open Stdarg

DECLARE PLUGIN "profile_ltac_plugin"

let tclSET_PROFILING b =
   Proofview.tclLIFT (Proofview.NonLogical.make (fun () ->
   set_profiling b))

TACTIC EXTEND start_profiling
  | [ "start" "profiling" ] -> [ tclSET_PROFILING true  ]
END

TACTIC EXTEND stop_profiling
  | [ "stop" "profiling" ] ->  [ tclSET_PROFILING false ]
END;;


VERNAC COMMAND EXTEND StartProfiling CLASSIFIED AS SIDEFF
 [ "Start" "Profiling" ] -> [ set_profiling true ]
END

VERNAC COMMAND EXTEND StopProfiling CLASSIFIED AS SIDEFF
 [ "Stop" "Profiling" ] -> [ set_profiling false ]
 END

VERNAC COMMAND EXTEND ResetProfiling CLASSIFIED AS SIDEFF
 [ "Reset" "Profile" ] -> [ reset_profile() ]
END

VERNAC COMMAND EXTEND ShowProfile CLASSIFIED AS QUERY
 [ "Show" "Profile" ] -> [ print_results() ]
END


VERNAC COMMAND EXTEND ShowProfileTactic CLASSIFIED AS QUERY
 [ "Show" "Profile" string(s) ] -> [ print_results_tactic s ]
END
