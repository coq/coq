(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Created by Hugo Herbelin from contents related to inductive schemes
   initially developed by Christine Paulin (induction schemes), Vincent
   Siles (decidable equality and boolean equality) and Matthieu Sozeau
   (combined scheme) in file command.ml, Sep 2009 *)

(* This file builds schemes related to case analysis and recursion schemes *)

open Sorts
open Constr
open Indrec
open Declarations
open Typeops
open Ind_tables

(* Induction/recursion schemes *)

let build_induction_scheme_in_type env dep sort ind =
  let sigma = Evd.from_env env in
  let sigma, pind = Evd.fresh_inductive_instance ~rigid:UState.univ_rigid env sigma ind in
  let sigma, c = build_induction_scheme env sigma pind dep sort in
    c, Evd.evar_universe_context sigma

(**********************************************************************)
(* [modify_sort_scheme s rec] replaces the sort of the scheme
   [rec] by [s] *)

let change_sort_arity sort =
  let rec drec a = match kind a with
    | Cast (c,_,_) -> drec c
    | Prod (n,t,c) -> let s, c' = drec c in s, mkProd (n, t, c')
    | LetIn (n,b,t,c) -> let s, c' = drec c in s, mkLetIn (n,b,t,c')
    | Sort s -> s, mkSort sort
    | _ -> assert false
  in
    drec


(** [weaken_sort_scheme env sigma s n c t] derives by subtyping from [c:t]
   whose conclusion is quantified on [Type i] at position [n] of [t] a
   scheme quantified on sort [s]. [s] is declared less or equal to [i]. *)
let weaken_sort_scheme env evd sort npars term ty =
  let open Context.Rel.Declaration in
  let evdref = ref evd in
  let rec drec ctx np elim =
    match kind elim with
      | Prod (n,t,c) ->
          let ctx = LocalAssum (n, t) :: ctx in
          if Int.equal np 0 then
            let osort, t' = change_sort_arity (EConstr.ESorts.kind !evdref sort) t in
              evdref := (if false then Evd.set_eq_sort else Evd.set_leq_sort) env !evdref sort (EConstr.ESorts.make osort);
              mkProd (n, t', c),
              mkLambda (n, t', mkApp(term, Context.Rel.instance mkRel 0 ctx))
          else
            let c',term' = drec ctx (np-1) c in
            mkProd (n, t, c'), mkLambda (n, t, term')
      | LetIn (n,b,t,c) ->
        let ctx = LocalDef (n, b, t) :: ctx in
        let c',term' = drec ctx np c in
        mkLetIn (n,b,t,c'), mkLetIn (n,b,t,term')
      | _ -> CErrors.anomaly ~label:"weaken_sort_scheme" (Pp.str "wrong elimination type.")
  in
  let ty, term = drec [] npars ty in
    !evdref, ty, term

let optimize_non_type_induction_scheme kind dep sort env _handle ind =
  (* This non-local call to [lookup_scheme] is fine since we do not use it on a
     dependency generated on the fly. *)
  match lookup_scheme kind ind with
  | Some cte ->
    let sigma = Evd.from_env env in
    (* in case the inductive has a type elimination, generates only one
       induction scheme, the other ones share the same code with the
       appropriate type *)
    let sigma, cte = Evd.fresh_constant_instance env sigma cte in
    let c = mkConstU cte in
    let t = type_of_constant_in env cte in
    let (mib,mip) = Inductive.lookup_mind_specif env ind in
    let npars =
      (* if a constructor of [ind] contains a recursive call, the scheme
         is generalized only wrt recursively uniform parameters *)
      if (Inductiveops.mis_is_recursive_subset [ind] mip.mind_recargs)
      then
        mib.mind_nparams_rec
      else
        mib.mind_nparams in
    let sigma, sort = Evd.fresh_sort_in_family sigma sort in
    let sigma, t', c' = weaken_sort_scheme env sigma sort npars c t in
    let sigma = Evd.minimize_universes sigma in
    (Evarutil.nf_evars_universes sigma c', Evd.evar_universe_context sigma)
  | None ->
    build_induction_scheme_in_type env dep sort ind

let rect_scheme_kind_from_type =
  declare_individual_scheme_object "_rect_nodep"
    (fun env _ x -> build_induction_scheme_in_type env false InType x)

let rect_scheme_kind_from_prop =
  declare_individual_scheme_object "_rect" ~aux:"_rect_from_prop"
    (fun env _ x -> build_induction_scheme_in_type env false InType x)

let rect_dep_scheme_kind_from_type =
  declare_individual_scheme_object "_rect" ~aux:"_rect_from_type"
    (fun env _ x -> build_induction_scheme_in_type env true InType x)

let rec_scheme_kind_from_type =
  declare_individual_scheme_object "_rec_nodep" ~aux:"_rec_nodep_from_type"
  (optimize_non_type_induction_scheme rect_scheme_kind_from_type false InSet)

let rec_scheme_kind_from_prop =
  declare_individual_scheme_object "_rec" ~aux:"_rec_from_prop"
  (optimize_non_type_induction_scheme rect_scheme_kind_from_prop false InSet)

let rec_dep_scheme_kind_from_type =
  declare_individual_scheme_object "_rec" ~aux:"_rec_from_type"
  (optimize_non_type_induction_scheme rect_dep_scheme_kind_from_type true InSet)

let ind_scheme_kind_from_type =
  declare_individual_scheme_object "_ind_nodep"
  (optimize_non_type_induction_scheme rec_scheme_kind_from_type false InProp)

let sind_scheme_kind_from_type =
  declare_individual_scheme_object "_sind_nodep"
  (fun env _ x -> build_induction_scheme_in_type env false InSProp x)

let ind_dep_scheme_kind_from_type =
  declare_individual_scheme_object "_ind" ~aux:"_ind_from_type"
  (optimize_non_type_induction_scheme rec_dep_scheme_kind_from_type true InProp)

let sind_dep_scheme_kind_from_type =
  declare_individual_scheme_object "_sind" ~aux:"_sind_from_type"
  (fun env _ x -> build_induction_scheme_in_type env true InSProp x)

let ind_scheme_kind_from_prop =
  declare_individual_scheme_object "_ind" ~aux:"_ind_from_prop"
  (optimize_non_type_induction_scheme rec_scheme_kind_from_prop false InProp)

let sind_scheme_kind_from_prop =
  declare_individual_scheme_object "_sind" ~aux:"_sind_from_prop"
  (fun env _ x -> build_induction_scheme_in_type env false InSProp x)

let nondep_elim_scheme from_kind to_kind =
  match from_kind, to_kind with
  | InProp, InProp  -> ind_scheme_kind_from_prop
  | InProp, InSProp -> sind_scheme_kind_from_prop
  | InProp, InSet   -> rec_scheme_kind_from_prop
  | InProp, (InType | InQSort) -> rect_scheme_kind_from_prop
  | _     , InProp  -> ind_scheme_kind_from_type
  | _     , InSProp -> sind_scheme_kind_from_type
  | _     , InSet   -> rec_scheme_kind_from_type
  | _     , (InType | InQSort) -> rect_scheme_kind_from_type

(* Case analysis *)

let build_case_analysis_scheme_in_type env dep sort ind =
  let sigma = Evd.from_env env in
  let (sigma, indu) = Evd.fresh_inductive_instance env sigma ind in
  let (sigma, c) = build_case_analysis_scheme env sigma indu dep sort in
  let (c, _) = Indrec.eval_case_analysis c in
  EConstr.Unsafe.to_constr c, Evd.evar_universe_context sigma

let case_scheme_kind_from_type =
  declare_individual_scheme_object "_case_nodep"
  (fun env _ x -> build_case_analysis_scheme_in_type env false InType x)

let case_scheme_kind_from_prop =
  declare_individual_scheme_object "_case" ~aux:"_case_from_prop"
  (fun env _ x -> build_case_analysis_scheme_in_type env false InType x)

let case_dep_scheme_kind_from_type =
  declare_individual_scheme_object "_case" ~aux:"_case_from_type"
  (fun env _ x -> build_case_analysis_scheme_in_type env true InType x)

let case_dep_scheme_kind_from_type_in_prop =
  declare_individual_scheme_object "_casep_dep"
  (fun env _ x -> build_case_analysis_scheme_in_type env true InProp x)

let case_dep_scheme_kind_from_prop =
  declare_individual_scheme_object "_case_dep"
  (fun env _ x -> build_case_analysis_scheme_in_type env true InType x)

let case_dep_scheme_kind_from_prop_in_prop =
  declare_individual_scheme_object "_casep"
  (fun env _ x -> build_case_analysis_scheme_in_type env true InProp x)
