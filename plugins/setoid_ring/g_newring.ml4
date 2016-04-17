(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4deps: "grammar/grammar.cma" i*)

open Pp
open Util
open Libnames
open Printer
open Newring_ast
open Newring
open Stdarg
open Constrarg
open Pcoq.Prim
open Pcoq.Constr
open Pcoq.Tactic

DECLARE PLUGIN "newring_plugin"

TACTIC EXTEND protect_fv
  [ "protect_fv" string(map) "in" ident(id) ] ->
    [ Proofview.V82.tactic (protect_tac_in map id) ]
| [ "protect_fv" string(map) ] ->
    [ Proofview.V82.tactic (protect_tac map) ]
END

TACTIC EXTEND closed_term
  [ "closed_term" constr(t) "[" ne_reference_list(l) "]" ] ->
    [ Proofview.V82.tactic (closed_term t l) ]
END

open Pptactic
open Ppconstr

let pr_ring_mod = function
  | Ring_kind (Computational eq_test) -> str "decidable" ++ pr_arg pr_constr_expr eq_test
  | Ring_kind Abstract ->  str "abstract"
  | Ring_kind (Morphism morph) -> str "morphism" ++ pr_arg pr_constr_expr morph
  | Const_tac (CstTac cst_tac) -> str "constants" ++ spc () ++ str "[" ++ pr_raw_tactic cst_tac ++ str "]"
  | Const_tac (Closed l) -> str "closed" ++ spc () ++ str "[" ++ prlist_with_sep spc pr_reference l ++ str "]"
  | Pre_tac t -> str "preprocess" ++ spc () ++ str "[" ++ pr_raw_tactic t ++ str "]"
  | Post_tac t -> str "postprocess" ++ spc () ++ str "[" ++ pr_raw_tactic t ++ str "]"
  | Setoid(sth,ext) -> str "setoid" ++ pr_arg pr_constr_expr sth ++ pr_arg pr_constr_expr ext
  | Pow_spec(Closed l,spec) -> str "power_tac" ++ pr_arg pr_constr_expr spec ++ spc () ++ str "[" ++ prlist_with_sep spc pr_reference l ++ str "]"
  | Pow_spec(CstTac cst_tac,spec) -> str "power_tac" ++ pr_arg pr_constr_expr spec ++ spc () ++ str "[" ++ pr_raw_tactic cst_tac ++ str "]"
  | Sign_spec t -> str "sign" ++ pr_arg pr_constr_expr t
  | Div_spec t -> str "div" ++ pr_arg pr_constr_expr t

VERNAC ARGUMENT EXTEND ring_mod
  PRINTED BY pr_ring_mod
  | [ "decidable" constr(eq_test) ] -> [ Ring_kind(Computational eq_test) ]
  | [ "abstract" ] -> [ Ring_kind Abstract ]
  | [ "morphism" constr(morph) ] -> [ Ring_kind(Morphism morph) ]
  | [ "constants" "[" tactic(cst_tac) "]" ] -> [ Const_tac(CstTac cst_tac) ]
  | [ "closed" "[" ne_global_list(l) "]" ] -> [ Const_tac(Closed l) ]
  | [ "preprocess" "[" tactic(pre) "]" ] -> [ Pre_tac pre ]
  | [ "postprocess" "[" tactic(post) "]" ] -> [ Post_tac post ]
  | [ "setoid" constr(sth) constr(ext) ] -> [ Setoid(sth,ext) ]
  | [ "sign" constr(sign_spec) ] -> [ Sign_spec sign_spec ]
  | [ "power" constr(pow_spec) "[" ne_global_list(l) "]" ] ->
           [ Pow_spec (Closed l, pow_spec) ]
  | [ "power_tac" constr(pow_spec) "[" tactic(cst_tac) "]" ] ->
           [ Pow_spec (CstTac cst_tac, pow_spec) ]
  | [ "div" constr(div_spec) ] -> [ Div_spec div_spec ]
END

let pr_ring_mods l = surround (prlist_with_sep pr_comma pr_ring_mod l)

VERNAC ARGUMENT EXTEND ring_mods
  PRINTED BY pr_ring_mods
  | [ "(" ne_ring_mod_list_sep(mods, ",") ")" ] -> [ mods ]
END

VERNAC COMMAND EXTEND AddSetoidRing CLASSIFIED AS SIDEFF
  | [ "Add" "Ring" ident(id) ":" constr(t) ring_mods_opt(l) ] ->
    [ let l = match l with None -> [] | Some l -> l in
      let (k,set,cst,pre,post,power,sign, div) = process_ring_mods l in
      add_theory id (ic t) set k cst (pre,post) power sign div]
  | [ "Print" "Rings" ] => [Vernac_classifier.classify_as_query] -> [
    msg_notice (strbrk "The following ring structures have been declared:");
    Spmap.iter (fun fn fi ->
      msg_notice (hov 2
        (Ppconstr.pr_id (Libnames.basename fn)++spc()++
          str"with carrier "++ pr_constr fi.ring_carrier++spc()++
          str"and equivalence relation "++ pr_constr fi.ring_req))
    ) !from_name ]
END

TACTIC EXTEND ring_lookup
| [ "ring_lookup" tactic0(f) "[" constr_list(lH) "]" ne_constr_list(lrt) ] ->
    [ let (t,lr) = List.sep_last lrt in ring_lookup f lH lr t]
END

let pr_field_mod = function
  | Ring_mod m -> pr_ring_mod m
  | Inject inj -> str "completeness" ++ pr_arg pr_constr_expr inj

VERNAC ARGUMENT EXTEND field_mod
  PRINTED BY pr_field_mod
  | [ ring_mod(m) ] -> [ Ring_mod m ]
  | [ "completeness" constr(inj) ] -> [ Inject inj ]
END

let pr_field_mods l = surround (prlist_with_sep pr_comma pr_field_mod l)

VERNAC ARGUMENT EXTEND field_mods
  PRINTED BY pr_field_mods
  | [ "(" ne_field_mod_list_sep(mods, ",") ")" ] -> [ mods ]
END

VERNAC COMMAND EXTEND AddSetoidField CLASSIFIED AS SIDEFF
| [ "Add" "Field" ident(id) ":" constr(t) field_mods_opt(l) ] ->
  [ let l = match l with None -> [] | Some l -> l in
    let (k,set,inj,cst_tac,pre,post,power,sign,div) = process_field_mods l in
    add_field_theory id (ic t) set k cst_tac inj (pre,post) power sign div]
| [ "Print" "Fields" ] => [Vernac_classifier.classify_as_query] -> [
    msg_notice (strbrk "The following field structures have been declared:");
    Spmap.iter (fun fn fi ->
      msg_notice (hov 2
        (Ppconstr.pr_id (Libnames.basename fn)++spc()++
          str"with carrier "++ pr_constr fi.field_carrier++spc()++
          str"and equivalence relation "++ pr_constr fi.field_req))
    ) !field_from_name ]
END

TACTIC EXTEND field_lookup
| [ "field_lookup" tactic(f) "[" constr_list(lH) "]" ne_constr_list(lt) ] ->
      [ let (t,l) = List.sep_last lt in field_lookup f lH l t ]
END
