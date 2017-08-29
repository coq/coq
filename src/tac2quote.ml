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
open Tac2expr
open Tac2qexpr

(** Syntactic quoting of expressions. *)

let control_prefix =
  MPfile (DirPath.make (List.map Id.of_string ["Control"; "Ltac2"]))

let kername prefix n = KerName.make2 prefix (Label.of_id (Id.of_string_soft n))
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

let of_pair f g (loc, (e1, e2)) =
  let loc = Option.default dummy_loc loc in
  CTacApp (loc, CTacCst (loc, AbsKn (Tuple 2)), [f e1; g e2])

let of_tuple ?loc el = match el with
| [] ->
  let loc = Option.default dummy_loc loc in
  CTacCst (loc, AbsKn (Tuple 0))
| [e] -> e
| el ->
  let loc = Option.default dummy_loc loc in
  let len = List.length el in
  CTacApp (loc, CTacCst (loc, AbsKn (Tuple len)), el)

let of_int (loc, n) =
  CTacAtm (Loc.tag ?loc (AtmInt n))

let of_option ?loc f opt = match opt with
| None -> constructor ?loc (coq_core "None") []
| Some e -> constructor ?loc (coq_core "Some") [f e]

let inj_wit ?loc wit x =
  let loc = Option.default dummy_loc loc in
  CTacExt (loc, wit, x)

let of_variable (loc, id) =
  let qid = Libnames.qualid_of_ident id in
  if Tac2env.is_constructor qid then
    CErrors.user_err ?loc (str "Invalid identifier")
  else CTacRef (RelId (Loc.tag ?loc qid))

let of_anti f = function
| QExpr x -> f x
| QAnti id -> of_variable id

let of_ident (loc, id) = inj_wit ?loc Tac2env.wit_ident id

let of_constr c =
  let loc = Constrexpr_ops.constr_loc c in
  inj_wit ?loc Tac2env.wit_constr c

let of_open_constr c =
  let loc = Constrexpr_ops.constr_loc c in
  inj_wit ?loc Tac2env.wit_open_constr c

let of_bool ?loc b =
  let c = if b then coq_core "true" else coq_core "false" in
  constructor ?loc c []

let rec of_list ?loc f = function
| [] -> constructor (coq_core "[]") []
| e :: l ->
  constructor ?loc (coq_core "::") [f e; of_list ?loc f l]

let of_qhyp (loc, h) = match h with
| QAnonHyp n -> std_constructor ?loc "AnonHyp" [of_int n]
| QNamedHyp id -> std_constructor ?loc "NamedHyp" [of_ident id]

let of_bindings (loc, b) = match b with
| QNoBindings ->
  std_constructor ?loc "NoBindings" []
| QImplicitBindings tl ->
  std_constructor ?loc "ImplicitBindings" [of_list ?loc of_open_constr tl]
| QExplicitBindings tl ->
  let map e = of_pair (fun q -> of_anti of_qhyp q) of_open_constr e in
  std_constructor ?loc "ExplicitBindings" [of_list ?loc map tl]

let of_constr_with_bindings c = of_pair of_open_constr of_bindings c

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
  std_constructor ?loc "IntroFresh" [of_anti of_ident id]
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
  std_constructor ?loc "IntroOrPattern" [of_list ?loc of_intro_patterns ill]
| QIntroAndPattern il ->
  std_constructor ?loc "IntroAndPattern" [of_intro_patterns il]

and of_intro_patterns (loc, l) =
  of_list ?loc of_intro_pattern l

let of_hyp_location_flag ?loc = function
| Locus.InHyp -> std_constructor ?loc "InHyp" []
| Locus.InHypTypeOnly -> std_constructor ?loc "InHypTypeOnly" []
| Locus.InHypValueOnly -> std_constructor ?loc "InHypValueOnly" []

let of_occurrences (loc, occ) = match occ with
| QAllOccurrences -> std_constructor ?loc "AllOccurrences" []
| QAllOccurrencesBut occs ->
  let map occ = of_anti of_int occ in
  let occs = of_list ?loc map occs in
  std_constructor ?loc "AllOccurrencesBut" [occs]
| QNoOccurrences -> std_constructor ?loc "NoOccurrences" []
| QOnlyOccurrences occs ->
  let map occ = of_anti of_int occ in
  let occs = of_list ?loc map occs in
  std_constructor ?loc "OnlyOccurrences" [occs]

let of_hyp_location ?loc ((occs, id), flag) =
  of_tuple ?loc [
    of_anti of_ident id;
    of_occurrences occs;
    of_hyp_location_flag ?loc flag;
  ]

let of_clause (loc, cl) =
  let loc = Option.default dummy_loc loc in
  let hyps = of_option ~loc (fun l -> of_list ~loc of_hyp_location l) cl.q_onhyps in
  let concl = of_occurrences cl.q_concl_occs in
  CTacRec (loc, [
    std_proj "on_hyps", hyps;
    std_proj "on_concl", concl;
  ])

let of_destruction_arg ?loc = function
| QElimOnConstr c ->
  let arg = thunk (of_constr_with_bindings c) in
  std_constructor ?loc "ElimOnConstr" [arg]
| QElimOnIdent id -> std_constructor ?loc "ElimOnIdent" [of_ident id]
| QElimOnAnonHyp n -> std_constructor ?loc "ElimOnAnonHyp" [of_int n]

let of_induction_clause (loc, cl) =
  let arg = of_destruction_arg ?loc cl.indcl_arg in
  let eqn = of_option ?loc of_intro_pattern_naming cl.indcl_eqn in
  let as_ = of_option ?loc of_or_and_intro_pattern cl.indcl_as in
  let in_ = of_option ?loc of_clause cl.indcl_in in
  let loc = Option.default dummy_loc loc in
  CTacRec (loc, [
    std_proj "indcl_arg", arg;
    std_proj "indcl_eqn", eqn;
    std_proj "indcl_as", as_;
    std_proj "indcl_in", in_;
  ])

let of_repeat (loc, r) = match r with
| QPrecisely n -> std_constructor ?loc "Precisely" [of_int n]
| QUpTo n -> std_constructor ?loc "UpTo" [of_int n]
| QRepeatStar -> std_constructor ?loc "RepeatStar" []
| QRepeatPlus -> std_constructor ?loc "RepeatPlus" []

let of_orient loc b =
  if b then std_constructor ?loc "LTR" []
  else std_constructor ?loc "RTL" []

let of_rewriting (loc, rew) =
  let orient =
    let (loc, orient) = rew.rew_orient in
    of_option ?loc (fun b -> of_orient loc b) orient
  in
  let repeat = of_repeat rew.rew_repeat in
  let equatn = thunk (of_constr_with_bindings rew.rew_equatn) in
  let loc = Option.default dummy_loc loc in
  CTacRec (loc, [
    std_proj "rew_orient", orient;
    std_proj "rew_repeat", repeat;
    std_proj "rew_equatn", equatn;
  ])

let of_hyp ?loc id =
  let loc = Option.default dummy_loc loc in
  let hyp = CTacRef (AbsKn (TacConstant (control_core "hyp"))) in
  CTacApp (loc, hyp, [of_ident id])

let of_exact_hyp ?loc id =
  let loc = Option.default dummy_loc loc in
  let refine = CTacRef (AbsKn (TacConstant (control_core "refine"))) in
  CTacApp (loc, refine, [thunk (of_hyp ~loc id)])

let of_exact_var ?loc id =
  let loc = Option.default dummy_loc loc in
  let refine = CTacRef (AbsKn (TacConstant (control_core "refine"))) in
  CTacApp (loc, refine, [thunk (of_variable id)])

let of_dispatch tacs =
  let loc = Option.default dummy_loc (fst tacs) in
  let default = function
  | Some e -> thunk e
  | None -> thunk (CTacCst (loc, AbsKn (Tuple 0)))
  in
  let map e = of_pair default (fun l -> of_list ~loc default l) (Loc.tag ~loc e) in
  of_pair (fun l -> of_list ~loc default l) (fun r -> of_option ~loc map r) tacs

let make_red_flag l =
  let open Genredexpr in
  let rec add_flag red = function
  | [] -> red
  | (_, flag) :: lf ->
    let red = match flag with
    | QBeta -> { red with rBeta = true }
    | QMatch -> { red with rMatch = true }
    | QFix -> { red with rFix = true }
    | QCofix -> { red with rCofix = true }
    | QZeta -> { red with rZeta = true }
    | QConst (loc, l) ->
        if red.rDelta then
          CErrors.user_err ?loc Pp.(str
            "Cannot set both constants to unfold and constants not to unfold");
        { red with rConst = red.rConst @ l }
    | QDeltaBut (loc, l) ->
        if red.rConst <> [] && not red.rDelta then
          CErrors.user_err ?loc Pp.(str
            "Cannot set both constants to unfold and constants not to unfold");
        { red with rConst = red.rConst @ l; rDelta = true }
    | QIota ->
      { red with rMatch = true; rFix = true; rCofix = true }
    in
    add_flag red lf
  in
  add_flag
    {rBeta = false; rMatch = false; rFix = false; rCofix = false;
     rZeta = false; rDelta = false; rConst = []}
    l

let of_reference r =
  let of_ref ref =
    let loc = Libnames.loc_of_reference ref in
    inj_wit ?loc Tac2env.wit_reference ref
  in
  of_anti of_ref r

let of_strategy_flag (loc, flag) =
  let open Genredexpr in
  let loc = Option.default dummy_loc loc in
  let flag = make_red_flag flag in
  CTacRec (loc, [
    std_proj "rBeta", of_bool ~loc flag.rBeta;
    std_proj "rMatch", of_bool ~loc flag.rMatch;
    std_proj "rFix", of_bool ~loc flag.rFix;
    std_proj "rCofix", of_bool ~loc flag.rCofix;
    std_proj "rZeta", of_bool ~loc flag.rZeta;
    std_proj "rDelta", of_bool ~loc flag.rDelta;
    std_proj "rConst", of_list ~loc of_reference flag.rConst;
  ])
