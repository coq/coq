(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4deps: "grammar/grammar.cma" i*)

open Misctypes
open Class_tactics

DECLARE PLUGIN "g_class"

TACTIC EXTEND progress_evars
  [ "progress_evars" tactic(t) ] -> [ progress_evars (Tacinterp.eval_tactic t) ]
END

(** Options: depth, debug and transparency settings. *)

let set_transparency cl b =
  List.iter (fun r ->
    let gr = Smartlocate.global_with_alias r in
    let ev = Tacred.evaluable_of_global_reference (Global.env ()) gr in
      Classes.set_typeclass_transparency ev false b) cl

VERNAC COMMAND EXTEND Typeclasses_Unfold_Settings CLASSIFIED AS SIDEFF
| [ "Typeclasses" "Transparent" reference_list(cl) ] -> [
    set_transparency cl true ]
END

VERNAC COMMAND EXTEND Typeclasses_Rigid_Settings CLASSIFIED AS SIDEFF
| [ "Typeclasses" "Opaque" reference_list(cl) ] -> [
    set_transparency cl false ]
END

open Genarg

let pr_debug _prc _prlc _prt b =
  if b then Pp.str "debug" else Pp.mt()

ARGUMENT EXTEND debug TYPED AS bool PRINTED BY pr_debug
| [ "debug" ] -> [ true ]
| [ ] -> [ false ]
END

let pr_depth _prc _prlc _prt = function
    Some i -> Pp.int i
  | None -> Pp.mt()

ARGUMENT EXTEND depth TYPED AS int option PRINTED BY pr_depth
| [ int_or_var_opt(v) ] -> [ match v with Some (ArgArg i) -> Some i | _ -> None ]
END

(* true = All transparent, false = Opaque if possible *)

VERNAC COMMAND EXTEND Typeclasses_Settings CLASSIFIED AS SIDEFF
 | [ "Typeclasses" "eauto" ":=" debug(d) depth(depth) ] -> [
     set_typeclasses_debug d;
     set_typeclasses_depth depth
   ]
END

TACTIC EXTEND typeclasses_eauto
| [ "typeclasses" "eauto" "with" ne_preident_list(l) ] -> [ Proofview.V82.tactic (typeclasses_eauto l) ]
| [ "typeclasses" "eauto" ] -> [ Proofview.V82.tactic (typeclasses_eauto ~only_classes:true [Hints.typeclasses_db]) ]
END

TACTIC EXTEND head_of_constr
  [ "head_of_constr" ident(h) constr(c) ] -> [ head_of_constr h c ]
END

TACTIC EXTEND not_evar
  [ "not_evar" constr(ty) ] -> [ not_evar ty ]
END

TACTIC EXTEND is_ground
  [ "is_ground" constr(ty) ] -> [ Proofview.V82.tactic (is_ground ty) ]
END

TACTIC EXTEND autoapply
  [ "autoapply" constr(c) "using" preident(i) ] -> [ Proofview.V82.tactic (autoapply c i) ]
END
