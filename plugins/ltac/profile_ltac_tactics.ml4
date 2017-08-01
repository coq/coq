(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4deps: "grammar/grammar.cma" i*)

(** Ltac profiling entrypoints *)

open Profile_ltac
open Stdarg

DECLARE PLUGIN "profile_ltac_plugin"

let tclSET_PROFILING b =
   Proofview.tclLIFT (Proofview.NonLogical.make (fun () -> set_profiling b))

TACTIC EXTEND start_ltac_profiling
| [ "start" "ltac" "profiling" ] -> [ tclSET_PROFILING true ]
END

TACTIC EXTEND stop_profiling
| [ "stop" "ltac" "profiling" ] -> [ tclSET_PROFILING false ]
END

VERNAC COMMAND EXTEND ResetLtacProfiling CLASSIFIED AS SIDEFF
  [ "Reset" "Ltac" "Profile" ] -> [ reset_profile() ]
END

VERNAC COMMAND EXTEND ShowLtacProfile CLASSIFIED AS QUERY
| [ "Show" "Ltac" "Profile" ] -> [ print_results ~cutoff:!Flags.profile_ltac_cutoff ]
| [ "Show" "Ltac" "Profile" "CutOff" int(n) ] -> [ print_results ~cutoff:(float_of_int n) ]
END

VERNAC COMMAND EXTEND ShowLtacProfileTactic CLASSIFIED AS QUERY
  [ "Show" "Ltac" "Profile" string(s) ] -> [ print_results_tactic s ]
END
