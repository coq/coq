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

let eval_uconstrs ist cs =
  let flags = {
    Pretyping.use_typeclasses = false;
    use_unif_heuristics = true;
    use_hook = Some Pfedit.solve_by_implicit_tactic;
    fail_evar = false;
    expand_evars = true
  } in
  List.map (fun c -> Tacinterp.type_uconstr ~flags ist c) cs

let pr_auto_using _ _ _ = Pptactic.pr_auto_using (fun _ -> mt ())

ARGUMENT EXTEND auto_using
  TYPED AS uconstr_list
  PRINTED BY pr_auto_using
| [ "using" ne_uconstr_list_sep(l, ",") ] -> [ l ]
| [ ] -> [ [] ]
END

TACTIC EXTEND trivial
| [ "trivial" auto_using(lems) hintbases(db) ] ->
    [ Auto.h_trivial (eval_uconstrs ist lems) db ]
END

TACTIC EXTEND info_trivial
| [ "info_trivial" auto_using(lems) hintbases(db) ] ->
    [ Auto.h_trivial ~debug:Info (eval_uconstrs ist lems) db ]
END

TACTIC EXTEND debug_trivial
| [ "debug" "trivial" auto_using(lems) hintbases(db) ] ->
    [ Auto.h_trivial ~debug:Debug (eval_uconstrs ist lems) db ]
END

TACTIC EXTEND auto
| [ "auto" int_or_var_opt(n) auto_using(lems) hintbases(db) ] ->
    [ Auto.h_auto n (eval_uconstrs ist lems) db ]
END

TACTIC EXTEND info_auto
| [ "info_auto" int_or_var_opt(n) auto_using(lems) hintbases(db) ] ->
    [ Auto.h_auto ~debug:Info n (eval_uconstrs ist lems) db ]
END

TACTIC EXTEND debug_auto
| [ "debug" "auto" int_or_var_opt(n) auto_using(lems) hintbases(db) ] ->
    [ Auto.h_auto ~debug:Debug n (eval_uconstrs ist lems) db ]
END
