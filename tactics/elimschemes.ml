(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
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

open Names
open Indrec
open Declarations
open Ind_tables
open UnivGen

let prop_but_default_dependent_elim =
  Summary.ref ~name:"PROP-BUT-DEFAULT-DEPENDENT-ELIM" Indset.empty

let inPropButDefaultDepElim : inductive -> Libobject.obj =
  let open Summary.Ref in
  Libobject.declare_object @@
  Libobject.superglobal_object "prop_but_default_dependent_elim"
    ~cache:(fun i ->
        prop_but_default_dependent_elim := Indset.add i !prop_but_default_dependent_elim)
    ~subst:(Some (fun (subst,i) -> Mod_subst.subst_ind subst i))
    ~discharge:(fun i -> Some i)

let declare_prop_but_default_dependent_elim i =
  Lib.add_leaf (inPropButDefaultDepElim i)

let is_prop_but_default_dependent_elim i =
  let open Summary.Ref in
  Indset.mem i !prop_but_default_dependent_elim

let pseudo_sort_quality_for_elim ind mip =
  let s = mip.mind_sort in
  if Sorts.is_prop s && is_prop_but_default_dependent_elim ind
  then Sorts.Quality.qtype
  else Sorts.quality s

let default_case_analysis_dependence env ind =
  let _, mip as specif = Inductive.lookup_mind_specif env ind in
  Inductiveops.always_dependent_elim specif
  && (not (Sorts.is_prop mip.mind_sort) || is_prop_but_default_dependent_elim ind)


(* **************************************************** *)
(*             Induction/recursion schemes              *)
(* **************************************************** *)

let build_induction_scheme_in_type env dep sort ind =
  let sigma = Evd.from_env env in
  let sigma, pind = Evd.fresh_inductive_instance ~rigid:UState.univ_rigid env sigma ind in
  let sigma, sort = Evd.fresh_sort_in_quality ~rigid:UnivRigid sigma sort in
  let sigma, c = build_induction_scheme env sigma pind dep sort in
  EConstr.to_constr sigma c, Evd.ustate sigma

let rect_dep =
  declare_individual_scheme_object "rect_dep"
    (fun env _ x -> build_induction_scheme_in_type env true QualityOrSet.qtype x)

let rec_dep =
  declare_individual_scheme_object "rec_dep"
    (fun env _ x -> build_induction_scheme_in_type env true QualityOrSet.set x)

let ind_dep =
  declare_individual_scheme_object "ind_dep"
    (fun env _ x -> build_induction_scheme_in_type env true QualityOrSet.prop x)

let sind_dep =
  declare_individual_scheme_object "sind_dep"
    (fun env _ x -> build_induction_scheme_in_type env true QualityOrSet.sprop x)

let rect_nodep =
  declare_individual_scheme_object "rect_nodep"
    (fun env _ x -> build_induction_scheme_in_type env false QualityOrSet.qtype x)

let rec_nodep =
  declare_individual_scheme_object "rec_nodep"
    (fun env _ x -> build_induction_scheme_in_type env false QualityOrSet.set x)

let ind_nodep =
  declare_individual_scheme_object "ind_nodep"
    (fun env _ x -> build_induction_scheme_in_type env false QualityOrSet.prop x)

let sind_nodep =
  declare_individual_scheme_object "sind_nodep"
    (fun env _ x -> build_induction_scheme_in_type env false QualityOrSet.sprop x)

let elim_scheme ~dep ~to_kind =
  let open QualityOrSet in
  match to_kind with
  | Qual q ->
     begin
       match q with
       | QConstant QSProp when dep -> sind_dep
       | QConstant QProp when dep -> ind_dep
       | (QConstant QType | QVar _) when dep -> rect_dep
       | QConstant QSProp -> sind_nodep
       | QConstant QProp -> ind_nodep
       | QConstant QType | QVar _ -> rect_nodep
       | QGlobal _ ->
         CErrors.user_err Pp.(str "Cannot automatically lookup elimination scheme for global sort.")
     end
  | Set -> if dep then rec_dep else rec_nodep

let elimination_suffix =
  let open UnivGen.QualityOrSet in
  let open Sorts.Quality in
  function
  | Qual (QConstant QSProp) -> "_sind"
  | Qual (QConstant QProp) -> "_ind"
  | Qual (QConstant QType) | Qual (QVar _) -> "_rect"
  | Set -> "_rec"
  | Qual (QGlobal _) ->
    CErrors.user_err Pp.(str "Cannot automatically lookup elimination scheme for global sort.")

let make_elimination_ident id s = Nameops.add_suffix id (elimination_suffix s)

(* Look up function for the default elimination constant *)

let lookup_eliminator_by_name env ind_sp s =
  let open Names in
  let open Environ in
  let kn,i = ind_sp in
  let mpu = KerName.modpath @@ MutInd.user kn in
  let mpc = KerName.modpath @@ MutInd.canonical kn in
  let ind_id = (lookup_mind kn env).mind_packets.(i).mind_typename in
  let id = make_elimination_ident ind_id s in
  let knu = KerName.make mpu id in
  let knc = KerName.make mpc id in
  (* Try first to get an eliminator defined in the same section as the *)
  (* inductive type *)
  let cst = Constant.make knu knc in
  if mem_constant cst env then GlobRef.ConstRef cst
  else
    (* Then try to get a user-defined eliminator in some other places *)
    (* using short name (e.g. for "eq_rec") *)
    try Nametab.locate (Libnames.qualid_of_ident id)
    with Not_found ->
      CErrors.user_err
        Pp.(strbrk "Cannot find the elimination combinator " ++
            Id.print id ++ strbrk ", the elimination of the inductive definition " ++
            Nametab.pr_global_env Id.Set.empty (GlobRef.IndRef ind_sp) ++
            strbrk " on sort " ++
            UnivGen.QualityOrSet.pr (UnivNames.quality_printer UnivNames.empty_binders) s ++
            strbrk " is probably not allowed.")

let deprecated_lookup_by_name =
  CWarnings.create ~name:"deprecated-lookup-elim-by-name" ~category:Deprecation.Version.v9_2
    Pp.(fun (env,ind,to_kind,r) ->
        let pp_scheme () s = str (scheme_kind_name s) in
        fmt "Found unregistered eliminator %t for %t by name.@ \
             Use \"Register Scheme\" with it instead@ \
             (\"as %a\" if dependent or \"as %a\" if non dependent)."
          (fun () -> Termops.pr_global_env env r)
          (fun () -> Termops.pr_global_env env (IndRef ind))
          pp_scheme (elim_scheme ~dep:true ~to_kind)
          pp_scheme (elim_scheme ~dep:false ~to_kind))

let lookup_eliminator_by_name env ind s =
  let r = lookup_eliminator_by_name env ind s in
  deprecated_lookup_by_name (env,ind,s,r);
  r

let lookup_eliminator env ind s =
  let nodep_scheme_first =
    (* compat, add an option to control this and remove someday *)
    let _, mip = Inductive.lookup_mind_specif env ind in
    Sorts.is_prop mip.mind_sort && not (is_prop_but_default_dependent_elim ind)
  in
  let schemes =
    List.map (fun dep -> elim_scheme ~dep ~to_kind:s)
      (if nodep_scheme_first then [false;true] else [true;false])
  in
  match List.find_map (fun scheme -> lookup_scheme scheme ind) schemes with
  | Some c -> c
  | None ->
    (* XXX also lookup_scheme at less precise sort? eg if s=set try to_kind:qtype *)
    lookup_eliminator_by_name env ind s


(* **************************************************** *)
(*                    Case Analysis                     *)
(* **************************************************** *)

let build_case_analysis_scheme_in_type env dep sort ind =
  let sigma = Evd.from_env env in
  let (sigma, indu) = Evd.fresh_inductive_instance ~rigid:UnivRigid env sigma ind in
  let sigma, sort = Evd.fresh_sort_in_quality ~rigid:UnivRigid sigma sort in
  let (sigma, c, _) = build_case_analysis_scheme env sigma indu dep sort in
  EConstr.Unsafe.to_constr c, Evd.ustate sigma

let case_dep =
  declare_individual_scheme_object "case_dep"
    (fun env _ x -> build_case_analysis_scheme_in_type env true QualityOrSet.qtype x)

let case_nodep =
  declare_individual_scheme_object "case_nodep"
    (fun env _ x -> build_case_analysis_scheme_in_type env false QualityOrSet.qtype x)

let casep_dep =
  declare_individual_scheme_object "casep_dep"
    (fun env _ x -> build_case_analysis_scheme_in_type env true QualityOrSet.prop x)

let casep_nodep =
  declare_individual_scheme_object "casep_nodep"
    (fun env _ x -> build_case_analysis_scheme_in_type env false QualityOrSet.prop x)

let scase_dep =
  declare_individual_scheme_object "scase_dep"
    (fun env _ x -> build_case_analysis_scheme_in_type env true QualityOrSet.sprop x)

let scase_nodep =
  declare_individual_scheme_object "scase_nodep"
    (fun env _ x -> build_case_analysis_scheme_in_type env false QualityOrSet.sprop x)
