(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open CErrors
open Util
open Names
open Context
open Constr
open Environ
open Evd
open Termops
open Namegen

module ERelevance = EConstr.ERelevance

module RelDecl = Context.Rel.Declaration
module NamedDecl = Context.Named.Declaration

let create_clos_infos env sigma flags =
  let open CClosure in
  let evars = Evd.evar_handler sigma in
  create_clos_infos ~univs:(Evd.universes sigma) ~evars flags env


(****************************************************)
(* Expanding/testing/exposing existential variables *)
(****************************************************)

let finalize ?abort_on_undefined_evars sigma f =
  let sigma = minimize_universes sigma in
  let uvars = ref Univ.Level.Set.empty in
  let nf_constr c =
    let _, varsc = EConstr.universes_of_constr sigma c in
    let c = EConstr.to_constr ?abort_on_undefined_evars sigma c in
    uvars := Univ.Level.Set.union !uvars varsc;
    c
  in
  let v = f nf_constr in
  let sigma = restrict_universe_context sigma !uvars in
  sigma, v

(** Term exploration up to instantiation. *)
let kind_of_term_upto = EConstr.kind_upto

let nf_evars_universes sigma t = EConstr.to_constr ~abort_on_undefined_evars:false sigma (EConstr.of_constr t)
let whd_evar = EConstr.whd_evar

let nf_evar = Evd.MiniEConstr.nf_evar

let j_nf_evar sigma j =
  { uj_val = nf_evar sigma j.uj_val;
    uj_type = nf_evar sigma j.uj_type }
let jl_nf_evar sigma jl = List.map (j_nf_evar sigma) jl
let jv_nf_evar sigma = Array.map (j_nf_evar sigma)
let tj_nf_evar sigma {utj_val=v;utj_type=t} =
  {utj_val=nf_evar sigma v;utj_type=t}

let nf_relevance sigma r =
  UState.nf_relevance (Evd.ustate sigma) r

let nf_named_context_evar sigma ctx =
  Context.Named.map_with_relevance (nf_relevance sigma) (nf_evars_universes sigma) ctx

let nf_rel_context_evar sigma ctx =
  let nf_relevance r = ERelevance.make (ERelevance.kind sigma r) in
  Context.Rel.map_with_relevance nf_relevance (nf_evar sigma) ctx

let nf_env_evar sigma env =
  let nc' = nf_named_context_evar sigma (Environ.named_context env) in
  let rel' = nf_rel_context_evar sigma (EConstr.rel_context env) in
    EConstr.push_rel_context rel' (reset_with_named_context (val_of_named_context nc') env)

let nf_evar_info evc info = map_evar_info (nf_evar evc) info

let nf_evar_map evm =
  Evd.raw_map { map = fun _ evi -> nf_evar_info evm evi } evm

let nf_evar_map_undefined evm =
  Evd.raw_map_undefined (fun _ evi -> nf_evar_info evm evi) evm

(*-------------------*)
(* Auxiliary functions for the conversion algorithms modulo evars
 *)

let has_undefined_evars evd t =
  let rec f h t =
    let (h, knd) = EConstr.Expand.kind evd h t in
    match knd with
    | Evar _ -> raise NotInstantiatedEvar
    | _ -> EConstr.Expand.iter evd f h knd
  in
  let h, t = EConstr.Expand.make t in
  try let _ = f h t in false
  with (Not_found | NotInstantiatedEvar) -> true

let has_undefined_evars_or_metas evd t =
  let rec has_ev t =
    match EConstr.kind evd t with
    | Evar _ | Meta _ -> raise NotInstantiatedEvar
    | _ -> EConstr.iter evd has_ev t in
  try let _ = has_ev t in false
  with (Not_found | NotInstantiatedEvar) -> true

let is_ground_term evd t =
  not (has_undefined_evars evd t)

let is_ground_env evd env =
  let is_ground_rel_decl = function
    | RelDecl.LocalDef (_,b,_) -> is_ground_term evd (EConstr.of_constr b)
    | _ -> true in
  let is_ground_named_decl = function
    | NamedDecl.LocalDef (_,b,_) -> is_ground_term evd (EConstr.of_constr b)
    | _ -> true in
  List.for_all is_ground_rel_decl (rel_context env) &&
  List.for_all is_ground_named_decl (named_context env)

(* Expand head evar if any (currently consider only applications but I
   guess it should consider Case too) *)

let whd_head_evar_stack sigma c =
  let rec whrec (c, l) =
    match EConstr.kind sigma c with
      | Cast (c,_,_) -> whrec (c, l)
      | App (f,args) -> whrec (f, args :: l)
      | c -> (EConstr.of_kind c, l)
  in
  whrec (c, [])

let whd_head_evar sigma c =
  let open EConstr in
  let (f, args) = whd_head_evar_stack sigma c in
  match args with
  | [arg] -> mkApp (f, arg)
  | _ -> mkApp (f, Array.concat args)

(**********************)
(* Creating new metas *)
(**********************)

let meta_counter_summary_name = "meta counter"

(* Generator of metavariables *)
let meta_ctr, meta_counter_summary_tag =
  Summary.ref_tag 0 ~name:meta_counter_summary_name

let new_meta () = incr meta_ctr; !meta_ctr

(* The list of non-instantiated existential declarations (order is important) *)

(*------------------------------------*
 * functional operations on evar sets *
 *------------------------------------*)

(* [push_rel_context_to_named_context] builds the defining context and the
 * initial instance of an evar. If the evar is to be used in context
 *
 * Gamma =  a1     ...    an xp      ...       x1
 *          \- named part -/ \- de Bruijn part -/
 *
 * then the x1...xp are turned into variables so that the evar is declared in
 * context
 *
 *          a1     ...    an xp      ...       x1
 *          \----------- named part ------------/
 *
 * but used applied to the initial instance "a1 ... an Rel(p) ... Rel(1)"
 * so that ev[a1:=a1 ... an:=an xp:=Rel(p) ... x1:=Rel(1)] is correctly typed
 * in context Gamma.
 *
 * Remark 1: The instance is reverted in practice (i.e. Rel(1) comes first)
 * Remark 2: If some of the ai or xj are definitions, we keep them in the
 *   instance. This is necessary so that no unfolding of local definitions
 *   happens when inferring implicit arguments (consider e.g. the problem
 *   "x:nat; x':=x; f:forall y, y=y -> Prop |- f _ (refl_equal x')" which
 *   produces the equation "?y[x,x']=?y[x,x']" =? "x'=x'": we want
 *   the hole to be instantiated by x', not by x (which would have been
 *   the case in [invert_definition] if x' had disappeared from the instance).
 *   Note that at any time, if, in some context env, the instance of
 *   declaration x:A is t and the instance of definition x':=phi(x) is u, then
 *   we have the property that u and phi(t) are convertible in env.
 *)

let next_ident_away id avoid =
  let avoid id = Id.Set.mem id avoid in
  next_ident_away_from id avoid

type subst_val =
| SRel of int
| SVar of Id.t

type csubst = {
  csubst_len : int;
  (** Cardinal of [csubst_rel] *)
  csubst_var : Constr.t Id.Map.t;
  (** A mapping of variables to variables. We use the more general
      [Constr.t] to share allocations, but all values are of shape [Var _]. *)
  csubst_rel : Constr.t Int.Map.t;
  (** A contiguous mapping of integers to variables. Same remark for values. *)
  csubst_rev : subst_val Id.Map.t;
  (** Reverse mapping of the substitution *)
}
(** This type represents a name substitution for the named and De Bruijn parts of
    an environment. For efficiency we also store the reverse substitution.
    Invariant: all identifiers in the codomain of [csubst_var] and [csubst_rel]
    must be pairwise distinct. *)

let empty_csubst = {
  csubst_len = 0;
  csubst_rel = Int.Map.empty;
  csubst_var = Id.Map.empty;
  csubst_rev = Id.Map.empty;
}

let csubst_subst sigma { csubst_len = k; csubst_var = v; csubst_rel = s } c =
  (* Safe because this is a substitution *)
  let c = EConstr.Unsafe.to_constr c in
  let rec subst n c = match Constr.kind c with
  | Rel m ->
    if m <= n then c
    else if m - n <= k then Int.Map.find (k - m + n) s
    else mkRel (m - k)
  | Var id ->
    begin try Id.Map.find id v with Not_found -> c end
  | Evar (evk, args) ->
    let EvarInfo evi = Evd.find sigma evk in
    let args' = subst_instance n (evar_filtered_context evi) args in
    if args' == args then c else Constr.mkEvar (evk, args') (* FIXME: preserve sharing *)
  | _ -> Constr.map_with_binders succ subst n c

  and subst_instance n ctx args = match ctx, SList.view args with
  | [], None -> SList.empty
  | decl :: ctx, Some (c, args) ->
    let c' = match c with
    | None -> begin try Some (Id.Map.find (NamedDecl.get_id decl) v) with Not_found -> c end
    | Some c ->
      let c' = subst n c in
      if isVarId (NamedDecl.get_id decl) c' then None else Some c'
    in
    SList.cons_opt c' (subst_instance n ctx args)
  | _ :: _, None | [], Some _ -> assert false
  in
  let c = if k = 0 && Id.Map.is_empty v then c else subst 0 c in
  EConstr.of_constr c

type ext_named_context =
  csubst * Id.Set.t * named_context_val

let push_var id { csubst_len = n; csubst_var = v; csubst_rel = s; csubst_rev = r } =
  let s = Int.Map.add n (Constr.mkVar id) s in
  let r = Id.Map.add id (SRel n) r in
  { csubst_len = succ n; csubst_var = v; csubst_rel = s; csubst_rev = r }

(** Post-compose the substitution with the generator [src ↦ tgt] *)
let update_var src tgt subst =
  let cur =
    try Some (Id.Map.find src subst.csubst_rev)
    with Not_found -> None
  in
  match cur with
  | None ->
    (* Missing keys stand for identity substitution [src ↦ src] *)
    let csubst_var = Id.Map.add src (Constr.mkVar tgt) subst.csubst_var in
    let csubst_rev = Id.Map.add tgt (SVar src) subst.csubst_rev in
    { subst with csubst_var; csubst_rev }
  | Some bnd ->
    let csubst_rev = Id.Map.add tgt bnd (Id.Map.remove src subst.csubst_rev) in
    match bnd with
    | SRel m ->
      let csubst_rel = Int.Map.add m (Constr.mkVar tgt) subst.csubst_rel in
      { subst with csubst_rel; csubst_rev }
    | SVar id ->
      let csubst_var = Id.Map.add id (Constr.mkVar tgt) subst.csubst_var in
      { subst with csubst_var; csubst_rev }

module VarSet =
struct
  type t = Id.t -> bool
  let empty _ = false
  let full _ = true
  let variables env id = is_section_variable env id
end

type naming_mode =
  | RenameExistingBut of VarSet.t
  | FailIfConflict
  | ProgramNaming of VarSet.t

let push_rel_decl_to_named_context
  ~hypnaming
  sigma decl ((subst, avoid, nc) : ext_named_context) =
  let open EConstr in
  let open Vars in
  let map_decl f d =
    NamedDecl.map_constr f d
  in
  let rec replace_var_named_declaration id0 id nc = match match_named_context_val nc with
  | None -> empty_named_context_val
  | Some (decl, nc) ->
    if Id.equal id0 (NamedDecl.get_id decl) then
      (* Stop here, the variable cannot occur before its definition *)
      push_named_context_val (NamedDecl.set_id id decl) nc
    else
      let nc = replace_var_named_declaration id0 id nc in
      let vsubst = [id0 , mkVar id] in
      push_named_context_val (map_decl (fun c -> replace_vars sigma vsubst c) decl) nc
  in
  let extract_if_neq id = function
    | Anonymous -> None
    | Name id' when Id.compare id id' = 0 -> None
    | Name id' -> Some id'
  in
  let na = RelDecl.get_name decl in
  let id =
    (* id_of_name_using_hdchar only depends on the rel context which is empty
        here *)
    next_ident_away (id_of_name_using_hdchar empty_env sigma (RelDecl.get_type decl) na) avoid
  in
  match extract_if_neq id na with
  | Some id0 ->
    begin match hypnaming with
    | RenameExistingBut f | ProgramNaming f ->
      if f id0 then
        (* spiwack: if [id0] is a section variable renaming it is
            incorrect. We revert to a less robust behaviour where
            the new binder has name [id]. Which amounts to the same
            behaviour than when [id=id0]. *)
        let d = decl |> NamedDecl.of_rel_decl (fun _ -> id) |> map_decl (csubst_subst sigma subst) in
        (push_var id subst, Id.Set.add id avoid, push_named_context_val d nc)
      else
        (* spiwack: if [id<>id0], rather than introducing a new
            binding named [id], we will keep [id0] (the name given
            by the user) and rename [id0] into [id] in the named
            context. Unless [id] is a section variable. *)
        let subst = update_var id0 id subst in
        let d = decl |> NamedDecl.of_rel_decl (fun _ -> id0) |> map_decl (csubst_subst sigma subst) in
        let nc = replace_var_named_declaration id0 id nc in
        let avoid = Id.Set.add id (Id.Set.add id0 avoid) in
        (push_var id0 subst, avoid, push_named_context_val d nc)
    | FailIfConflict ->
       user_err Pp.(Id.print id0 ++ str " is already used.")
    end
  | None ->
    let d = decl |> NamedDecl.of_rel_decl (fun _ -> id) |> map_decl (csubst_subst sigma subst) in
    (push_var id subst, Id.Set.add id avoid, push_named_context_val d nc)

let csubst_instance subst ctx =
  let fold decl accu = match Id.Map.find (NamedDecl.get_id decl) subst.csubst_rev with
  | SRel n -> SList.cons (EConstr.mkRel (subst.csubst_len - n)) accu
  | SVar id -> SList.cons (EConstr.mkVar id) accu
  | exception Not_found -> SList.default accu
  in
  List.fold_right fold ctx SList.empty

let default_ext_instance (subst, _, ctx) =
  csubst_instance subst (named_context_of_val ctx)

let push_rel_context_to_named_context ~hypnaming env sigma typ =
  (* compute the instances relative to the named context and rel_context *)
  let open EConstr in
  let ctx = named_context_val env in
  if List.is_empty (Environ.rel_context env) then
    let inst = SList.defaultn (List.length @@ named_context_of_val ctx) SList.empty in
    (ctx, typ, inst, empty_csubst)
  else
    let avoid = Environ.ids_of_named_context_val (named_context_val env) in
    (* move the rel context to a named context and extend the named instance *)
    (* with vars of the rel context *)
    (* We do keep the instances corresponding to local definition (see above) *)
    let (subst, _, env) as ext =
      Context.Rel.fold_outside (fun d acc -> push_rel_decl_to_named_context ~hypnaming sigma d acc)
        (rel_context env) ~init:(empty_csubst, avoid, ctx) in
    let inst = default_ext_instance ext in
    (env, csubst_subst sigma subst typ, inst, subst)

(*------------------------------------*
 * Entry points to define new evars   *
 *------------------------------------*)

let new_pure_evar = Evd.new_pure_evar

let next_evar_name sigma naming = match naming with
| IntroAnonymous -> None
| IntroIdentifier id -> Some id
| IntroFresh id ->
  let id = Nameops.Fresh.next id (Evd.evar_names sigma) in
  Some id

(* [new_evar] declares a new existential in an env env with type typ *)
(* Converting the env into the sign of the evar to define *)
let new_evar ?src ?filter ?relevance ?abstract_arguments ?candidates ?(naming = IntroAnonymous) ?typeclass_candidate
    ?hypnaming env evd typ =
  let name = next_evar_name evd naming in
  let hypnaming = match hypnaming with
  | Some n -> n
  | None -> RenameExistingBut (VarSet.variables (Global.env ()))
  in
  let sign,typ',instance,subst = push_rel_context_to_named_context ~hypnaming env evd typ in
  let map c = csubst_subst evd subst c in
  let candidates = Option.map (fun l -> List.map map l) candidates in
  let instance =
    match filter with
    | None -> instance
    | Some filter -> Filter.filter_slist filter instance in
  let relevance = match relevance with
  | Some r -> r
  | None -> ERelevance.relevant (* FIXME: relevant_of_type not defined yet *)
  in
  let (evd, evk) = new_pure_evar sign evd typ' ?src ?filter ~relevance ?abstract_arguments ?candidates ?name
    ?typeclass_candidate in
  (evd, EConstr.mkEvar (evk, instance))

let new_type_evar ?src ?filter ?naming ?hypnaming env evd rigid =
  let (evd', s) = new_sort_variable rigid evd in
  let relevance = EConstr.ESorts.relevance_of_sort s in
  let (evd', e) = new_evar env evd' ?src ?filter ~relevance ?naming ~typeclass_candidate:false ?hypnaming (EConstr.mkSort s) in
  evd', (e, s)

let new_Type ?(rigid=Evd.univ_flexible) evd =
  let open EConstr in
  let (evd, s) = new_sort_variable rigid evd in
  (evd, mkSort s)

(* Safe interface to unification problems *)
type unification_pb = conv_pb * env * EConstr.constr * EConstr.constr

let eq_unification_pb evd (pbty,env,t1,t2) (pbty',env',t1',t2') =
  pbty == pbty' && env == env' &&
    EConstr.eq_constr evd t1 t1' &&
    EConstr.eq_constr evd t2 t2'

let add_unification_pb ?(tail=false) pb evd =
  let conv_pbs = Evd.conv_pbs evd in
  if not (List.exists (eq_unification_pb evd pb) conv_pbs) then
    let (pbty,env,t1,t2) = pb in
    Evd.add_conv_pb ~tail (pbty,env,t1,t2) evd
  else evd

(* This assumes an evar with identity instance and generalizes it over only
   the de Bruijn part of the context *)
let generalize_evar_over_rels sigma (ev,args) =
  let open EConstr in
  let evi = Evd.find_undefined sigma ev in
  let args = Evd.expand_existential sigma (ev, args) in
  let sign = named_context_of_val (Evd.evar_hyps evi) in
  List.fold_left2
    (fun (c,inst as x) a d ->
      if isRel sigma a then (mkNamedProd_or_LetIn sigma d c,a::inst) else x)
     (Evd.evar_concl evi,[]) args sign

(************************************)
(* Removing a dependency in an evar *)
(************************************)

type clear_dependency_error =
| OccurHypInSimpleClause of Id.t option
| EvarTypingBreak of EConstr.existential
| NoCandidatesLeft of Evar.t

exception ClearDependencyError of Id.t * clear_dependency_error * GlobRef.t option

exception Depends of Id.t

let set_of_evctx l =
  List.fold_left (fun s decl -> Id.Set.add (NamedDecl.get_id decl) s) Id.Set.empty l

let filter_effective_candidates evd evi filter candidates =
  let ids = set_of_evctx (Filter.filter_list filter (evar_context evi)) in
  List.filter (fun a -> Id.Set.subset (collect_vars evd a) ids) candidates

let restrict_evar evd evk filter candidates =
  let evar_info = Evd.find_undefined evd evk in
  let candidates = Option.map (filter_effective_candidates evd evar_info filter) candidates in
  match candidates with
  | Some [] -> raise (ClearDependencyError (*FIXME*)(Id.of_string "blah", (NoCandidatesLeft evk), None))
  | _ -> Evd.restrict evk filter ?candidates evd

let rec check_and_clear_in_constr ~is_section_variable env evdref err ids ~global c =
  (* returns a new constr where all the evars have been 'cleaned'
     (ie the hypotheses ids have been removed from the contexts of
     evars). [global] should be true iff there is some variable of [ids] which
     is a section variable *)
    match EConstr.kind !evdref c with
      | Var id' ->
      if Id.Set.mem id' ids then raise (ClearDependencyError (id', err, None)) else c

      | ( Const _ | Ind _ | Construct _ ) as ref ->
        let () = if global then
          let r = match ref with
          | Const (c, _) -> GlobRef.ConstRef c
          | Ind (ind, _) -> IndRef ind
          | Construct (c, _) -> ConstructRef c
          | _ -> assert false
          in
          let check id' =
            if Id.Set.mem id' ids then
              raise (ClearDependencyError (id',err,Some r))
          in
          Id.Set.iter check (Environ.vars_of_global env r)
        in
        c

      | Evar (evk,l as ev) ->
            (* We check for dependencies to elements of ids in the
               evar_info corresponding to e and in the instance of
               arguments. Concurrently, we build a new evar
               corresponding to e where hypotheses of ids have been
               removed *)
            let evi = Evd.find_undefined !evdref evk in
            let ctxt = Evd.evar_filtered_context evi in
            let rec fold accu ctxt args = match ctxt, SList.view args with
            | [], Some _ | _ :: _, None -> assert false
            | [], None -> accu
            | h :: ctxt, Some (a, args) ->
              let (ri, filter) = fold accu ctxt args in
              try
              (* Check if some id to clear occurs in the instance
                  a of rid in ev and remember the dependency *)
                let check id = if Id.Set.mem id ids then raise (Depends id) in
                let a = match a with
                | None -> Id.Set.singleton (NamedDecl.get_id h)
                | Some a -> collect_vars !evdref a
                in
                let () = Id.Set.iter check a in
              (* Check if some rid to clear in the context of ev
                  has dependencies in another hyp of the context of ev
                  and transitively remember the dependency *)
                let check id _ =
                  if occur_var_in_decl env !evdref id h
                  then raise (Depends id)
                in
                let () = Id.Map.iter check ri in
              (* No dependency at all, we can keep this ev's context hyp *)
                (ri, true::filter)
              with Depends id -> (Id.Map.add (NamedDecl.get_id h) id ri, false::filter)
            in
            let (rids, filter) = fold (Id.Map.empty, []) ctxt l in
            (* Check if some rid to clear in the context of ev has dependencies
               in the type of ev and adjust the source of the dependency *)
            let _nconcl : EConstr.t =
              try
                let nids = Id.Map.domain rids in
                let global = Id.Set.exists is_section_variable nids in
                let concl = evar_concl evi in
                check_and_clear_in_constr ~is_section_variable env evdref (EvarTypingBreak ev) nids ~global concl
              with ClearDependencyError (rid,err,where) ->
                raise (ClearDependencyError (Id.Map.find rid rids,err,where)) in

            if Id.Map.is_empty rids then c
            else
              let origfilter = Evd.evar_filter evi in
              let filter = Evd.Filter.apply_subfilter origfilter filter in
              let evd = !evdref in
              let candidates = Evd.evar_candidates evi in
              let (evd,_) = restrict_evar evd evk filter candidates in
              evdref := evd;
              Evd.existential_value !evdref ev

      | _ -> EConstr.map !evdref (check_and_clear_in_constr ~is_section_variable env evdref err ids ~global) c

let clear_hyps_in_evi_main env sigma hyps terms ids =
  (* clear_hyps_in_evi erases hypotheses ids in hyps, checking if some
     hypothesis does not depend on a element of ids, and erases ids in
     the contexts of the evars occurring in evi *)
  let evdref = ref sigma in
  let is_section_variable id = is_section_variable (Global.env ()) id in
  let global = Id.Set.exists is_section_variable ids in
  let terms =
    List.map (check_and_clear_in_constr ~is_section_variable env evdref (OccurHypInSimpleClause None) ids ~global) terms in
  let nhyps =
    let check_context decl =
      let decl = EConstr.of_named_decl decl in
      let err = OccurHypInSimpleClause (Some (NamedDecl.get_id decl)) in
      EConstr.Unsafe.to_named_decl @@ NamedDecl.map_constr (check_and_clear_in_constr ~is_section_variable env evdref err ids ~global) decl
    in
    remove_hyps ids check_context hyps
  in
  (!evdref, nhyps, terms)

let check_and_clear_in_constr env evd err ids c =
  let evdref = ref evd in
  let _ : EConstr.constr = check_and_clear_in_constr
      ~is_section_variable:(fun _ -> true) ~global:true
      env evdref err ids c
  in
  !evdref

let clear_hyps_in_evi env sigma hyps concl ids =
  match clear_hyps_in_evi_main env sigma hyps [concl] ids with
  | (sigma,nhyps,[nconcl]) -> (sigma,nhyps,nconcl)
  | _ -> assert false

let clear_hyps2_in_evi env sigma hyps t concl ids =
  match clear_hyps_in_evi_main env sigma hyps [t;concl] ids with
  | (sigma,nhyps,[t;nconcl]) -> (sigma,nhyps,t,nconcl)
  | _ -> assert false

(** [advance sigma g] returns [Some g'] if [g'] is undefined and is
    the current avatar of [g] (for instance [g] was changed by [clear]
    into [g']). It returns [None] if [g] has been (partially)
    solved. *)
(* spiwack: [advance] is probably performance critical, and the good
   behaviour of its definition may depend sensitively to the actual
   definition of [Evd.find]. Currently, [Evd.find] starts looking for
   a value in the heap of undefined variable, which is small. Hence in
   the most common case, where [advance] is applied to an unsolved
   goal ([advance] is used to figure if a side effect has modified the
   goal) it terminates quickly. *)
let rec advance sigma evk =
  match Evd.find_defined sigma evk with
  | None -> Some evk
  | Some evi ->
    match Evd.evar_body evi with
    | Evar_defined v ->
      match is_aliased_evar sigma evk with
      | Some evk -> advance sigma evk
      | None -> None

let reachable_from_evars sigma evars =
  let aliased = Evd.get_aliased_evars sigma in
  let rec search evk visited =
    if Evar.Set.mem evk visited then visited
    else
      let visited = Evar.Set.add evk visited in
      match Evar.Map.find evk aliased with
      | evk' -> search evk' visited
      | exception Not_found -> visited
  in
  Evar.Set.fold (fun evk visited -> search evk visited) evars Evar.Set.empty

(** The following functions return the set of undefined evars
    contained in the object, the defined evars being traversed.
    This is roughly a combination of the previous functions and
    [nf_evar]. *)

let undefined_evars_of_term evd t =
  let rec evrec acc c =
    match EConstr.kind evd c with
      | Evar (n, l) ->
        let acc = Evar.Set.add n acc in
        SList.Skip.fold evrec acc l
      | _ -> EConstr.fold evd evrec acc c
  in
  evrec Evar.Set.empty t

let undefined_evars_of_named_context evd nc =
  Context.Named.fold_outside
    (NamedDecl.fold_constr (fun c s -> Evar.Set.union s (undefined_evars_of_term evd (EConstr.of_constr c))))
    nc
    ~init:Evar.Set.empty

type undefined_evars_cache = {
  mutable cache : (EConstr.named_declaration * Evar.Set.t) ref Id.Map.t;
}

let create_undefined_evars_cache () = { cache = Id.Map.empty; }

let cached_evar_of_hyp cache sigma decl accu = match cache with
| None ->
  let fold c acc =
    let evs = undefined_evars_of_term sigma c in
    Evar.Set.union evs acc
  in
  NamedDecl.fold_constr fold decl accu
| Some cache ->
  let id = NamedDecl.get_annot decl in
  let r =
    try Id.Map.find id.binder_name cache.cache
    with Not_found ->
      (* Dummy value *)
      let r = ref (NamedDecl.LocalAssum (id, EConstr.mkProp), Evar.Set.empty) in
      let () = cache.cache <- Id.Map.add id.binder_name r cache.cache in
      r
  in
  let (decl', evs) = !r in
  let evs =
    if NamedDecl.equal (==) (==) decl decl' then snd !r
    else
      let fold c acc =
        let evs = undefined_evars_of_term sigma c in
        Evar.Set.union evs acc
      in
      let evs = NamedDecl.fold_constr fold decl Evar.Set.empty in
      let () = r := (decl, evs) in
      evs
  in
  Evar.Set.fold Evar.Set.add evs accu

let filtered_undefined_evars_of_evar_info (type a) ?cache sigma (evi : a evar_info) =
  let evars_of_named_context cache accu nc =
    let fold decl accu = cached_evar_of_hyp cache sigma (EConstr.of_named_decl decl) accu in
    Context.Named.fold_outside fold nc ~init:accu
  in
  let accu = match Evd.evar_body evi with
  | Evar_empty -> undefined_evars_of_term sigma (Evd.evar_concl evi)
  | Evar_defined b -> evars_of_term sigma b
  in
  let ctxt = EConstr.Unsafe.to_named_context (evar_filtered_context evi) in
  evars_of_named_context cache accu ctxt

(* spiwack: this is a more complete version of
   {!Termops.occur_evar}. The latter does not look recursively into an
   [evar_map]. If unification only need to check superficially, tactics
   do not have this luxury, and need the more complete version. *)
let occur_evar_upto sigma n c =
  let rec occur_rec c = match EConstr.kind sigma c with
    | Evar (evk, _) -> if Evar.equal evk n then raise Occur
    | _ -> EConstr.iter sigma occur_rec c
  in
  try occur_rec c; false with Occur -> true

(* We don't try to guess in which sort the type should be defined, since
   any type has type Type. May cause some trouble, but not so far... *)

let judge_of_new_Type evd =
  let open EConstr in
  let (evd', s) = new_sort_variable univ_rigid evd in
  (evd', { uj_val = mkSort s; uj_type = mkSort (ESorts.super evd s) })

let subterm_source evk ?where (loc,k) =
  let evk = match k with
    | Evar_kinds.SubEvar (None,evk) when where = None -> evk
    | _ -> evk in
  (loc,Evar_kinds.SubEvar (where,evk))

(* Add equality constraints for covariant/invariant positions. For
   irrelevant positions, unify universes when flexible. *)
let compare_cumulative_instances cv_pb variances u u' sigma =
  let open UnivProblem in
  let cstrs = Univ.Constraints.empty in
  let soft = Set.empty in
  let qs, us = UVars.Instance.to_array u
  and qs', us' = UVars.Instance.to_array u' in
  let qcstrs = enforce_eq_qualities qs qs' Set.empty in
  match Evd.add_universe_constraints sigma qcstrs with
  | exception UGraph.UniverseInconsistency p -> Inr p
  | sigma ->
  let cstrs, soft = Array.fold_left3 (fun (cstrs, soft) v u u' ->
      let open UVars.Variance in
      match v with
      | Irrelevant -> cstrs, Set.add (UWeak (u,u')) soft
      | Covariant when cv_pb == Conversion.CUMUL ->
        Univ.Constraints.add (u,Univ.Le,u') cstrs, soft
      | Covariant | Invariant -> Univ.Constraints.add (u,Univ.Eq,u') cstrs, soft)
      (cstrs,soft) variances us us'
  in
  match Evd.add_constraints sigma cstrs with
  | sigma ->
    Inl (Evd.add_universe_constraints sigma soft)
  | exception UGraph.UniverseInconsistency p -> Inr p

let compare_constructor_instances evd u u' =
  let open UnivProblem in
  let qs, us = UVars.Instance.to_array u
  and qs', us' = UVars.Instance.to_array u' in
  let qcstrs = enforce_eq_qualities qs qs' Set.empty in
  match Evd.add_universe_constraints evd qcstrs with
  | exception UGraph.UniverseInconsistency p -> Inr p
  | evd ->
    let soft =
      Array.fold_left2 (fun cs u u' -> Set.add (UWeak (u,u')) cs)
        Set.empty us us'
    in
    Inl (Evd.add_universe_constraints evd soft)

(** [eq_constr_univs_test ~evd ~extended_evd t u] tests equality of
    [t] and [u] up to existential variable instantiation and
    equalisable universes. The term [t] is interpreted in [evd] while
    [u] is interpreted in [extended_evd]. The universe constraints in
    [extended_evd] are assumed to be an extension of those in [evd]. *)
let eq_constr_univs_test ~evd ~extended_evd t u =
  (* spiwack: mild code duplication with {!Evd.eq_constr_univs}. *)
  let open Evd in
  let t = EConstr.Unsafe.to_constr t
  and u = EConstr.Unsafe.to_constr u in
  let sigma = ref extended_evd in
  let eq_universes _ u1 u2 =
    let u1 = normalize_universe_instance !sigma u1 in
    let u2 = normalize_universe_instance !sigma u2 in
    UGraph.check_eq_instances (universes !sigma) u1 u2
  in
  let eq_sorts s1 s2 =
    if Sorts.equal s1 s2 then true
    else
      try sigma := add_universe_constraints !sigma UnivProblem.(Set.singleton (UEq (s1, s2))); true
      with UGraph.UniverseInconsistency _ | UniversesDiffer -> false
  in
  let eq_existential eq e1 e2 =
    let eq c1 c2 = eq 0 (EConstr.Unsafe.to_constr c1) (EConstr.Unsafe.to_constr c2) in
    EConstr.eq_existential evd eq (EConstr.of_existential e1) (EConstr.of_existential e2)
  in
  let kind1 = kind_of_term_upto evd in
  let kind2 = kind_of_term_upto extended_evd in
  let rec eq_constr' nargs m n =
    Constr.compare_head_gen_with kind1 kind2 eq_universes eq_sorts (eq_existential eq_constr') eq_constr' nargs m n
  in
  Constr.compare_head_gen_with kind1 kind2 eq_universes eq_sorts (eq_existential eq_constr') eq_constr' 0 t u
