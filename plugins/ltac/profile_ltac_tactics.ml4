(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Ltac profiling entrypoints *)

open Profile_ltac
open Stdarg

DECLARE PLUGIN "ltac_plugin"

let tclSET_PROFILING b =
   Proofview.tclLIFT (Proofview.NonLogical.make (fun () -> set_profiling b))

let tclRESET_PROFILE =
   Proofview.tclLIFT (Proofview.NonLogical.make reset_profile)

let tclSHOW_PROFILE ~cutoff =
   Proofview.tclLIFT (Proofview.NonLogical.make (fun () -> print_results ~cutoff))

let tclSHOW_PROFILE_TACTIC s =
   Proofview.tclLIFT (Proofview.NonLogical.make (fun () -> print_results_tactic s))

let tclRESTART_TIMER s =
   Proofview.tclLIFT (Proofview.NonLogical.make (fun () -> restart_timer s))

let tclFINISH_TIMING ?(prefix="Timer") (s : string option) =
   Proofview.tclLIFT (Proofview.NonLogical.make (fun () -> finish_timing ~prefix s))

TACTIC EXTEND start_ltac_profiling
| [ "start" "ltac" "profiling" ] -> [ tclSET_PROFILING true ]
END

TACTIC EXTEND stop_ltac_profiling
| [ "stop" "ltac" "profiling" ] -> [ tclSET_PROFILING false ]
END

TACTIC EXTEND reset_ltac_profile
| [ "reset" "ltac" "profile" ] -> [ tclRESET_PROFILE ]
END

TACTIC EXTEND show_ltac_profile
| [ "show" "ltac" "profile" ] -> [ tclSHOW_PROFILE ~cutoff:!Flags.profile_ltac_cutoff ]
| [ "show" "ltac" "profile" "cutoff" int(n) ] -> [ tclSHOW_PROFILE ~cutoff:(float_of_int n) ]
| [ "show" "ltac" "profile" string(s) ] -> [ tclSHOW_PROFILE_TACTIC s ]
END

TACTIC EXTEND restart_timer
| [ "restart_timer" string_opt(s) ] -> [ tclRESTART_TIMER s ]
END

TACTIC EXTEND finish_timing
| [ "finish_timing" string_opt(s) ] -> [ tclFINISH_TIMING ~prefix:"Timer" s ]
| [ "finish_timing" "(" string(prefix) ")" string_opt(s) ] -> [ tclFINISH_TIMING ~prefix s ]
END

VERNAC COMMAND EXTEND ResetLtacProfiling CLASSIFIED AS SIDEFF
  [ "Reset" "Ltac" "Profile" ] -> [ reset_profile () ]
END

VERNAC COMMAND EXTEND ShowLtacProfile CLASSIFIED AS QUERY
| [ "Show" "Ltac" "Profile" ] -> [ print_results ~cutoff:!Flags.profile_ltac_cutoff ]
| [ "Show" "Ltac" "Profile" "CutOff" int(n) ] -> [ print_results ~cutoff:(float_of_int n) ]
END

VERNAC COMMAND EXTEND ShowLtacProfileTactic CLASSIFIED AS QUERY
  [ "Show" "Ltac" "Profile" string(s) ] -> [ print_results_tactic s ]
END
