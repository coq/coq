(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Names
open Util
open Misctypes
open Tac2intern
open Tac2expr
open Tac2qexpr
open Tac2core

(** Syntactic quoting of expressions. *)

let control_prefix =
  MPfile (DirPath.make (List.map Id.of_string ["Control"; "Ltac2"]))

let kername prefix n = KerName.make2 prefix (Label.of_id (Id.of_string n))
let std_core n = kername Tac2env.std_prefix n
let coq_core n = kername Tac2env.coq_prefix n
let control_core n = kername control_prefix n

let dummy_loc = Loc.make_loc (-1, -1)

let constructor ?loc kn args =
  let loc = Option.default dummy_loc loc in
  let cst = CTacCst (loc, AbsKn (Other kn)) in
  if List.is_empty args then cst
  else CTacApp (loc, cst, args)

let std_constructor ?loc name args =
  constructor ?loc (std_core name) args

let std_proj ?loc name =
  AbsKn (std_core name)

let thunk e =
  let t_unit = coq_core "unit" in
  let loc = Tac2intern.loc_of_tacexpr e in
  let var = [CPatVar (Some loc, Anonymous), Some (CTypRef (loc, AbsKn (Other t_unit), []))] in
  CTacFun (loc, var, e)

let of_pair ?loc (e1, e2) =
  let loc = Option.default dummy_loc loc in
  CTacApp (loc, CTacCst (loc, AbsKn (Tuple 2)), [e1; e2])

let of_tuple ?loc el =
  let loc = Option.default dummy_loc loc in
  let len = List.length el in
  CTacApp (loc, CTacCst (loc, AbsKn (Tuple len)), el)

let of_int (loc, n) =
  CTacAtm (Loc.tag ?loc (AtmInt n))

let of_option ?loc opt = match opt with
| None -> constructor ?loc (coq_core "None") []
| Some e -> constructor ?loc (coq_core "Some") [e]

let inj_wit ?loc wit x =
  let loc = Option.default dummy_loc loc in
  CTacExt (loc, Genarg.in_gen (Genarg.rawwit wit) x)

let of_variable (loc, id) =
  let qid = Libnames.qualid_of_ident id in
  if Tac2env.is_constructor qid then
    CErrors.user_err ?loc (str "Invalid identifier")
  else CTacRef (RelId (Loc.tag ?loc qid))

let of_anti ?loc f = function
| QExpr x -> f x
| QAnti id -> of_variable id

let of_ident (loc, id) = inj_wit ?loc Stdarg.wit_ident id

let of_constr c =
  let loc = Constrexpr_ops.constr_loc c in
  inj_wit ?loc Stdarg.wit_constr c

let of_open_constr c =
  let loc = Constrexpr_ops.constr_loc c in
  inj_wit ?loc Stdarg.wit_open_constr c

let of_bool ?loc b =
  let c = if b then Core.c_true else Core.c_false in
  constructor ?loc c []

let rec of_list ?loc = function
| [] -> constructor Core.c_nil []
| e :: l ->
  constructor ?loc Core.c_cons [e; of_list ?loc l]

let of_qhyp (loc, h) = match h with
| QAnonHyp n -> constructor ?loc Core.c_anon_hyp [of_int n]
| QNamedHyp id -> constructor ?loc Core.c_named_hyp [of_ident id]

let of_bindings (loc, b) = match b with
| QNoBindings ->
  std_constructor ?loc "NoBindings" []
| QImplicitBindings tl ->
  let tl = List.map of_open_constr tl in
  std_constructor ?loc "ImplicitBindings" [of_list ?loc tl]
| QExplicitBindings tl ->
  let map (loc, (qhyp, e)) = of_pair ?loc (of_anti ?loc of_qhyp qhyp, of_open_constr e) in
  let tl = List.map map tl in
  std_constructor ?loc "ExplicitBindings" [of_list ?loc tl]

let rec of_intro_pattern (loc, pat) = match pat with
| QIntroForthcoming b ->
  std_constructor ?loc "IntroForthcoming" [of_bool b]
| QIntroNaming iname ->
  std_constructor ?loc "IntroNaming" [of_intro_pattern_naming iname]
| QIntroAction iact ->
  std_constructor ?loc "IntroAction" [of_intro_pattern_action iact]

and of_intro_pattern_naming (loc, pat) = match pat with
| QIntroIdentifier id ->
  std_constructor ?loc "IntroIdentifier" [of_anti of_ident id]
| QIntroFresh id ->
  std_constructor ?loc "IntroFresh" [of_anti ?loc of_ident id]
| QIntroAnonymous ->
  std_constructor ?loc "IntroAnonymous" []

and of_intro_pattern_action (loc, pat) = match pat with
| QIntroWildcard ->
  std_constructor ?loc "IntroWildcard" []
| QIntroOrAndPattern pat ->
  std_constructor ?loc "IntroOrAndPattern" [of_or_and_intro_pattern pat]
| QIntroInjection il ->
  std_constructor ?loc "IntroInjection" [of_intro_patterns il]
| QIntroRewrite b ->
  std_constructor ?loc "IntroRewrite" [of_bool ?loc b]

and of_or_and_intro_pattern (loc, pat) = match pat with
| QIntroOrPattern ill ->
  let ill = List.map of_intro_patterns ill in
  std_constructor ?loc "IntroOrPattern" [of_list ?loc ill]
| QIntroAndPattern il ->
  std_constructor ?loc "IntroAndPattern" [of_intro_patterns il]

and of_intro_patterns (loc, l) =
  of_list ?loc (List.map of_intro_pattern l)

let of_hyp_location_flag ?loc = function
| Locus.InHyp -> std_constructor ?loc "InHyp" []
| Locus.InHypTypeOnly -> std_constructor ?loc "InHypTypeOnly" []
| Locus.InHypValueOnly -> std_constructor ?loc "InHypValueOnly" []

let of_occurrences ?loc occ = match occ with
| QAllOccurrences -> std_constructor ?loc "AllOccurrences" []
| QAllOccurrencesBut occs ->
  let map occ = of_anti ?loc of_int occ in
  let occs = of_list ?loc (List.map map occs) in
  std_constructor ?loc "AllOccurrencesBut" [occs]
| QNoOccurrences -> std_constructor ?loc "NoOccurrences" []
| QOnlyOccurrences occs ->
  let map occ = of_anti ?loc of_int occ in
  let occs = of_list ?loc (List.map map occs) in
  std_constructor ?loc "OnlyOccurrences" [occs]

let of_hyp_location ?loc ((occs, id), flag) =
  of_tuple ?loc [
    of_anti ?loc of_ident id;
    of_occurrences ?loc occs;
    of_hyp_location_flag ?loc flag;
  ]

let of_clause ?loc cl =
  let loc = Option.default dummy_loc loc in
  let hyps = of_option ~loc (Option.map (fun l -> of_list ~loc (List.map of_hyp_location l)) cl.q_onhyps) in
  let concl = of_occurrences ~loc cl.q_concl_occs in
  CTacRec (loc, [
    std_proj "on_hyps", hyps;
    std_proj "on_concl", concl;
  ])

let of_destruction_arg ?loc = function
| QElimOnConstr (loc, (c, bnd)) ->
  let c = of_open_constr c in
  let bnd = of_bindings bnd in
  let arg = thunk (of_pair ?loc (c, bnd)) in
  std_constructor ?loc "ElimOnConstr" [arg]
| QElimOnIdent id -> std_constructor ?loc "ElimOnIdent" [of_ident id]
| QElimOnAnonHyp n -> std_constructor ?loc "ElimOnAnonHyp" [of_int n]

let of_induction_clause (loc, cl) =
  let arg = of_destruction_arg ?loc cl.indcl_arg in
  let eqn = of_option ?loc (Option.map of_intro_pattern_naming cl.indcl_eqn) in
  let as_ = of_option ?loc (Option.map of_or_and_intro_pattern cl.indcl_as) in
  let in_ = of_option ?loc (Option.map of_clause cl.indcl_in) in
  let loc = Option.default dummy_loc loc in
  CTacRec (loc, [
    std_proj "indcl_arg", arg;
    std_proj "indcl_eqn", eqn;
    std_proj "indcl_as", as_;
    std_proj "indcl_in", in_;
  ])

let of_hyp ?loc id =
  let loc = Option.default dummy_loc loc in
  let hyp = CTacRef (AbsKn (control_core "hyp")) in
  CTacApp (loc, hyp, [of_ident id])

let of_exact_hyp ?loc id =
  let loc = Option.default dummy_loc loc in
  let refine = CTacRef (AbsKn (control_core "refine")) in
  CTacApp (loc, refine, [thunk (of_hyp ~loc id)])
