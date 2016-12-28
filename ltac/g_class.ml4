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
open Pltac
open Stdarg
open Tacarg

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

let pr_search_strategy _prc _prlc _prt = function
  | Some Dfs -> Pp.str "dfs"
  | Some Bfs -> Pp.str "bfs"
  | None -> Pp.mt ()

ARGUMENT EXTEND eauto_search_strategy PRINTED BY pr_search_strategy
| [ "(bfs)" ] -> [ Some Bfs ]
| [ "(dfs)" ] -> [ Some Dfs ]
| [ ] -> [ None ] 
END

(* true = All transparent, false = Opaque if possible *)

VERNAC COMMAND EXTEND Typeclasses_Settings CLASSIFIED AS SIDEFF
 | [ "Typeclasses" "eauto" ":=" debug(d) eauto_search_strategy(s) int_opt(depth) ] -> [
     set_typeclasses_debug d;
     Option.iter set_typeclasses_strategy s;
     set_typeclasses_depth depth
   ]
END

(** Compatibility: typeclasses eauto has 8.5 and 8.6 modes *)
TACTIC EXTEND typeclasses_eauto
 | [ "typeclasses" "eauto" "bfs" int_or_var_opt(d) "with" ne_preident_list(l) ] ->
    [ typeclasses_eauto ~strategy:Bfs ~depth:d l ]
 | [ "typeclasses" "eauto" int_or_var_opt(d) "with" ne_preident_list(l) ] ->
    [ typeclasses_eauto ~depth:d l ]
 | [ "typeclasses" "eauto" int_or_var_opt(d) ] -> [
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
