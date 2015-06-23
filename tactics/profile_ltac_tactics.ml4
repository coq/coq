(*i camlp4deps: "parsing/grammar.cma" i*)

open Profile_ltac

let tclSET_PROFILING b = fun gl -> 
   set_profiling b; Tacticals.tclIDTAC gl    

TACTIC EXTEND start_profiling
  | [ "start" "profiling" ] -> [ tclSET_PROFILING true  ]    
END
    
TACTIC EXTEND stop_profiling 
  | [ "stop" "profiling" ] ->  [ tclSET_PROFILING false ]    
END;;


VERNAC COMMAND EXTEND StartProfiling
 [ "Start" "Profiling" ] -> [ reset_profile(); set_profiling true ]
END

VERNAC COMMAND EXTEND StopProfiling
 [ "Stop" "Profiling" ] -> [ set_profiling false ]
 END

VERNAC COMMAND EXTEND ResetProfiling
 [ "Reset" "Profile" ] -> [ reset_profile() ]
END

VERNAC COMMAND EXTEND ShowProfile
 [ "Show" "Profile" ] -> [ print_results() ]
END


VERNAC COMMAND EXTEND ShowProfileTactic
 [ "Show" "Profile" string(s) ] -> [ print_results_tactic s ]
END