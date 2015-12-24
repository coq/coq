(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4deps: "grammar/grammar.cma" i*)

open Pp
open Genarg
open Tacexpr

DECLARE PLUGIN "g_auto"

(* Hint bases *)

let pr_hintbases _prc _prlc _prt = Pptactic.pr_hintbases

ARGUMENT EXTEND hintbases
  TYPED AS preident_list_opt
  PRINTED BY pr_hintbases
| [ "with" "*" ] -> [ None ]
| [ "with" ne_preident_list(l) ] -> [ Some l ]
| [ ] -> [ Some [] ]
END

let pr_constr_coma_sequence prc _ _ =
  prlist_with_sep pr_comma (fun (_,c) -> prc c)

ARGUMENT EXTEND constr_coma_sequence
  TYPED AS open_constr_list
  PRINTED BY pr_constr_coma_sequence
| [ open_constr(c) "," constr_coma_sequence(l) ] -> [ c::l ]
| [ open_constr(c) ] -> [ [c] ]
END

let pr_auto_using prc _prlc _prt = Pptactic.pr_auto_using (fun (_,c) -> prc c)

ARGUMENT EXTEND auto_using
  TYPED AS open_constr_list
  PRINTED BY pr_auto_using
| [ "using" constr_coma_sequence(l) ] -> [ l ]
| [ ] -> [ [] ]
END

TACTIC EXTEND trivial
| [ "trivial" auto_using(lems) hintbases(db) ] ->
    [ Auto.h_trivial lems db ]
END

TACTIC EXTEND info_trivial
| [ "info_trivial" auto_using(lems) hintbases(db) ] ->
    [ Auto.h_trivial ~debug:Info lems db ]
END

TACTIC EXTEND debug_trivial
| [ "debug" "trivial" auto_using(lems) hintbases(db) ] ->
    [ Auto.h_trivial ~debug:Debug lems db ]
END

TACTIC EXTEND auto
| [ "auto" int_or_var_opt(n) auto_using(lems) hintbases(db) ] ->
    [ Auto.h_auto n lems db ]
END

TACTIC EXTEND info_auto
| [ "info_auto" int_or_var_opt(n) auto_using(lems) hintbases(db) ] ->
    [ Auto.h_auto ~debug:Info n lems db ]
END

TACTIC EXTEND debug_auto
| [ "debug" "auto" int_or_var_opt(n) auto_using(lems) hintbases(db) ] ->
    [ Auto.h_auto ~debug:Debug n lems db ]
END
