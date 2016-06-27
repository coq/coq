(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4deps: "grammar/grammar.cma" i*)

open Misctypes
open Class_tactics
open Pcoq.Tactic
open Stdarg
open Constrarg

DECLARE PLUGIN "g_class"

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

(** Compatibility: typeclasses eauto has 8.5 and 8.6 modes *)
TACTIC EXTEND typeclasses_eauto
 | [ "typeclasses" "eauto" depth(d) "with" ne_preident_list(l) ] ->
    [ typeclasses_eauto d l ]
 | [ "typeclasses" "eauto" depth(d) ] -> [
     typeclasses_eauto ~only_classes:true ~depth:d [Hints.typeclasses_db] ]
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

(** TODO: DEPRECATE *)
(* A progress test that allows to see if the evars have changed *)
open Term
open Proofview.Goal
open Proofview.Notations

let rec eq_constr_mod_evars x y =
  match kind_of_term x, kind_of_term y with
  | Evar (e1, l1), Evar (e2, l2) when not (Evar.equal e1 e2) -> true
  | _, _ -> compare_constr eq_constr_mod_evars x y

let progress_evars t =
  Proofview.Goal.nf_enter { enter = begin fun gl ->
    let concl = Proofview.Goal.concl gl in
    let check =
      Proofview.Goal.nf_enter { enter = begin fun gl' ->
        let newconcl = Proofview.Goal.concl gl' in
        if eq_constr_mod_evars concl newconcl
        then Tacticals.New.tclFAIL 0 (Pp.str"No progress made (modulo evars)")
        else Proofview.tclUNIT ()
      end }
    in t <*> check
  end }

TACTIC EXTEND progress_evars
  [ "progress_evars" tactic(t) ] -> [ progress_evars (Tacinterp.tactic_of_value ist t) ]
END
