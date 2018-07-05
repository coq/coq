(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open CErrors
open Util
open Names
open Term
open Constr
open Environ
open Evd
open Termops
open Namegen

module RelDecl = Context.Rel.Declaration
module NamedDecl = Context.Named.Declaration

let safe_evar_value sigma ev =
  let ev = EConstr.of_existential ev in
  try Some (EConstr.Unsafe.to_constr @@ Evd.existential_value sigma ev)
  with NotInstantiatedEvar | Not_found -> None

(** Combinators *)

let evd_comb0 f evdref =
  let (evd',x) = f !evdref in
    evdref := evd';
    x

let evd_comb1 f evdref x =
  let (evd',y) = f !evdref x in
    evdref := evd';
    y

let evd_comb2 f evdref x y =
  let (evd',z) = f !evdref x y in
    evdref := evd';
    z

let e_new_global evdref x = 
  evd_comb1 (Evd.fresh_global (Global.env())) evdref x

let new_global evd x = 
  let (evd, c) = Evd.fresh_global (Global.env()) evd x in
  (evd, c)

(****************************************************)
(* Expanding/testing/exposing existential variables *)
(****************************************************)

(* flush_and_check_evars fails if an existential is undefined *)

exception Uninstantiated_evar of Evar.t

let rec flush_and_check_evars sigma c =
  match kind c with
  | Evar (evk,_ as ev) ->
      (match existential_opt_value0 sigma ev with
       | None -> raise (Uninstantiated_evar evk)
       | Some c -> flush_and_check_evars sigma c)
  | _ -> Constr.map (flush_and_check_evars sigma) c

let flush_and_check_evars sigma c =
  flush_and_check_evars sigma (EConstr.Unsafe.to_constr c)

(** Term exploration up to instantiation. *)
let kind_of_term_upto = EConstr.kind_upto

let nf_evar0 sigma t = EConstr.to_constr ~abort_on_undefined_evars:false sigma (EConstr.of_constr t)
let whd_evar = EConstr.whd_evar
let nf_evar sigma c = EConstr.of_constr (EConstr.to_constr ~abort_on_undefined_evars:false sigma c)

let j_nf_evar sigma j =
  { uj_val = nf_evar sigma j.uj_val;
    uj_type = nf_evar sigma j.uj_type }
let jl_nf_evar sigma jl = List.map (j_nf_evar sigma) jl
let jv_nf_evar sigma = Array.map (j_nf_evar sigma)
let tj_nf_evar sigma {utj_val=v;utj_type=t} =
  {utj_val=nf_evar sigma v;utj_type=t}

let nf_evars_universes evm =
  UnivSubst.nf_evars_and_universes_opt_subst (safe_evar_value evm)
    (Evd.universe_subst evm)
    
let nf_evars_and_universes evm =
  let evm = Evd.minimize_universes evm in
    evm, nf_evars_universes evm

let e_nf_evars_and_universes evdref =
  evdref := Evd.minimize_universes !evdref;
  nf_evars_universes !evdref, Evd.universe_subst !evdref

let nf_evar_map_universes evm =
  let evm = Evd.minimize_universes evm in
  let subst = Evd.universe_subst evm in
    if Univ.LMap.is_empty subst then evm, nf_evar0 evm
    else
      let f = nf_evars_universes evm in
      let f' c = EConstr.of_constr (f (EConstr.Unsafe.to_constr c)) in
        Evd.raw_map (fun _ -> map_evar_info f') evm, f

let nf_named_context_evar sigma ctx =
  Context.Named.map (nf_evar0 sigma) ctx

let nf_rel_context_evar sigma ctx =
  Context.Rel.map (nf_evar sigma) ctx

let nf_env_evar sigma env =
  let nc' = nf_named_context_evar sigma (Environ.named_context env) in
  let rel' = nf_rel_context_evar sigma (EConstr.rel_context env) in
    EConstr.push_rel_context rel' (reset_with_named_context (val_of_named_context nc') env)

let nf_evar_info evc info = map_evar_info (nf_evar evc) info

let nf_evar_map evm =
  Evd.raw_map (fun _ evi -> nf_evar_info evm evi) evm

let nf_evar_map_undefined evm =
  Evd.raw_map_undefined (fun _ evi -> nf_evar_info evm evi) evm

(*-------------------*)
(* Auxiliary functions for the conversion algorithms modulo evars
 *)

let has_undefined_evars evd t =
  let rec has_ev t =
    match EConstr.kind evd t with
    | Evar _ -> raise NotInstantiatedEvar
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

(* Memoization is safe since evar_map and environ are applicative
   structures *)
let memo f =
  let m = ref None in
  fun x y -> match !m with
  | Some (x', y', r) when x == x' && y == y' -> r
  | _ -> let r = f x y in m := Some (x, y, r); r

let is_ground_env = memo is_ground_env

(* Return the head evar if any *)

exception NoHeadEvar

let head_evar sigma c =
  (** FIXME: this breaks if using evar-insensitive code *)
  let c = EConstr.Unsafe.to_constr c in
  let rec hrec c = match kind c with
    | Evar (evk,_)   -> evk
    | Case (_,_,c,_) -> hrec c
    | App (c,_)      -> hrec c
    | Cast (c,_,_)   -> hrec c
    | Proj (p, c)    -> hrec c
    | _              -> raise NoHeadEvar
  in
  hrec c

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

let mk_new_meta () = EConstr.mkMeta(new_meta())

(* The list of non-instantiated existential declarations (order is important) *)

let non_instantiated sigma =
  let listev = Evd.undefined_map sigma in
  Evar.Map.Smart.map (fun evi -> nf_evar_info sigma evi) listev

(************************)
(* Manipulating filters *)
(************************)

let make_pure_subst evi args =
  snd (List.fold_right
    (fun decl (args,l) ->
      match args with
        | a::rest -> (rest, (NamedDecl.get_id decl, a)::l)
        | _ -> anomaly (Pp.str "Instance does not match its signature."))
    (evar_filtered_context evi) (Array.rev_to_list args,[]))

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

let next_name_away na avoid =
  let avoid id = Id.Set.mem id avoid in
  let id = match na with Name id -> id | Anonymous -> default_non_dependent_ident in
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
(** This type represent a name substitution for the named and De Bruijn parts of
    a environment. For efficiency we also store the reverse substitution.
    Invariant: all identifiers in the codomain of [csubst_var] and [csubst_rel]
    must be pairwise distinct. *)

let empty_csubst = {
  csubst_len = 0;
  csubst_rel = Int.Map.empty;
  csubst_var = Id.Map.empty;
  csubst_rev = Id.Map.empty;
}

let csubst_subst { csubst_len = k; csubst_var = v; csubst_rel = s } c =
  (** Safe because this is a substitution *)
  let c = EConstr.Unsafe.to_constr c in
  let rec subst n c = match Constr.kind c with
  | Rel m ->
    if m <= n then c
    else if m - n <= k then Int.Map.find (k - m + n) s
    else mkRel (m - k)
  | Var id ->
    begin try Id.Map.find id v with Not_found -> c end
  | _ -> Constr.map_with_binders succ subst n c
  in
  let c = if k = 0 && Id.Map.is_empty v then c else subst 0 c in
  EConstr.of_constr c

type ext_named_context =
  csubst * Id.Set.t * EConstr.named_context

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
    (** Missing keys stand for identity substitution [src ↦ src] *)
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

type naming_mode =
  | KeepUserNameAndRenameExistingButSectionNames
  | KeepUserNameAndRenameExistingEvenSectionNames
  | KeepExistingNames
  | FailIfConflict

let push_rel_decl_to_named_context
  ?(hypnaming=KeepUserNameAndRenameExistingButSectionNames)
  sigma decl (subst, avoid, nc) =
  let open EConstr in
  let open Vars in
  let map_decl f d =
    NamedDecl.map_constr f d
  in
  let replace_var_named_declaration id0 id decl =
    let id' = NamedDecl.get_id decl in
    let id' = if Id.equal id0 id' then id else id' in
    let vsubst = [id0 , mkVar id] in
    decl |> NamedDecl.set_id id' |> map_decl (replace_vars vsubst)
  in
  let extract_if_neq id = function
    | Anonymous -> None
    | Name id' when Id.compare id id' = 0 -> None
    | Name id' -> Some id'
  in
  let na = RelDecl.get_name decl in
  let id =
    (* ppedrot: we want to infer nicer names for the refine tactic, but
        keeping at the same time backward compatibility in other code
        using this function. For now, we only attempt to preserve the
        old behaviour of Program, but ultimately, one should do something
        about this whole name generation problem. *)
    if Flags.is_program_mode () then next_name_away na avoid
    else
      (** id_of_name_using_hdchar only depends on the rel context which is empty
          here *)
      next_ident_away (id_of_name_using_hdchar empty_env sigma (RelDecl.get_type decl) na) avoid
  in
  match extract_if_neq id na with
  | Some id0 when hypnaming = KeepUserNameAndRenameExistingEvenSectionNames ||
                  hypnaming = KeepUserNameAndRenameExistingButSectionNames &&
                  not (is_section_variable id0) ->
      (* spiwack: if [id<>id0], rather than introducing a new
          binding named [id], we will keep [id0] (the name given
          by the user) and rename [id0] into [id] in the named
          context. Unless [id] is a section variable. *)
      let subst = update_var id0 id subst in
      let d = decl |> NamedDecl.of_rel_decl (fun _ -> id0) |> map_decl (csubst_subst subst) in
      let nc = List.map (replace_var_named_declaration id0 id) nc in
      (push_var id0 subst, Id.Set.add id avoid, d :: nc)
  | Some id0 when hypnaming = FailIfConflict ->
       user_err Pp.(Id.print id0 ++ str " is already used.")
  | _ ->
      (* spiwack: if [id0] is a section variable renaming it is
          incorrect. We revert to a less robust behaviour where
          the new binder has name [id]. Which amounts to the same
          behaviour than when [id=id0]. *)
      let d = decl |> NamedDecl.of_rel_decl (fun _ -> id) |> map_decl (csubst_subst subst) in
      (push_var id subst, Id.Set.add id avoid, d :: nc)

let push_rel_context_to_named_context ?hypnaming env sigma typ =
  (* compute the instances relative to the named context and rel_context *)
  let open Context.Named.Declaration in
  let open EConstr in
  let ids = List.map get_id (named_context env) in
  let inst_vars = List.map mkVar ids in
  if List.is_empty (Environ.rel_context env) then
    (named_context_val env, typ, inst_vars, empty_csubst)
  else
    let avoid = List.fold_right Id.Set.add ids Id.Set.empty in
    let inst_rels = List.rev (rel_list 0 (nb_rel env)) in
    (* move the rel context to a named context and extend the named instance *)
    (* with vars of the rel context *)
    (* We do keep the instances corresponding to local definition (see above) *)
    let (subst, _, env) =
      Context.Rel.fold_outside (fun d acc -> push_rel_decl_to_named_context ?hypnaming sigma d acc)
        (rel_context env) ~init:(empty_csubst, avoid, named_context env) in
    (val_of_named_context env, csubst_subst subst typ, inst_rels@inst_vars, subst)

(*------------------------------------*
 * Entry points to define new evars   *
 *------------------------------------*)

let default_source = Loc.tag @@ Evar_kinds.InternalHole

let new_pure_evar_full evd evi =
  let (evd, evk) = Evd.new_evar evd evi in
  let evd = Evd.declare_future_goal evk evd in
  (evd, evk)

let new_pure_evar?(src=default_source) ?(filter = Filter.identity) ?candidates ?(store = Store.empty) ?naming ?(principal=false) sign evd typ =
  let default_naming = IntroAnonymous in
  let naming = Option.default default_naming naming in
  let name = match naming with
  | IntroAnonymous -> None
  | IntroIdentifier id -> Some id
  | IntroFresh id ->
    let has_name id = try let _ = Evd.evar_key id evd in true with Not_found -> false in
    let id = Namegen.next_ident_away_from id has_name in
    Some id
  in
  let evi = {
    evar_hyps = sign;
    evar_concl = typ;
    evar_body = Evar_empty;
    evar_filter = filter;
    evar_source = src;
    evar_candidates = candidates;
    evar_extra = store; }
  in
  let (evd, newevk) = Evd.new_evar evd ?name evi in
  let evd =
    if principal then Evd.declare_principal_goal newevk evd
    else Evd.declare_future_goal newevk evd
  in
  (evd, newevk)

let new_evar_instance ?src ?filter ?candidates ?store ?naming ?principal sign evd typ instance =
  let open EConstr in
  assert (not !Flags.debug ||
            List.distinct (ids_of_named_context (named_context_of_val sign)));
  let (evd, newevk) = new_pure_evar sign evd ?src ?filter ?candidates ?store ?naming ?principal typ in
  evd, mkEvar (newevk,Array.of_list instance)

let new_evar_from_context ?src ?filter ?candidates ?store ?naming ?principal sign evd typ =
  let instance = List.map (NamedDecl.get_id %> EConstr.mkVar) (named_context_of_val sign) in
  let instance =
    match filter with
    | None -> instance
    | Some filter -> Filter.filter_list filter instance in
  new_evar_instance sign evd typ ?src ?filter ?candidates ?store ?naming ?principal instance

(* [new_evar] declares a new existential in an env env with type typ *)
(* Converting the env into the sign of the evar to define *)
let new_evar ?src ?filter ?candidates ?store ?naming ?principal ?hypnaming env evd typ =
  let sign,typ',instance,subst = push_rel_context_to_named_context ?hypnaming env evd typ in
  let map c = csubst_subst subst c in
  let candidates = Option.map (fun l -> List.map map l) candidates in
  let instance =
    match filter with
    | None -> instance
    | Some filter -> Filter.filter_list filter instance in
  new_evar_instance sign evd typ' ?src ?filter ?candidates ?store ?naming ?principal instance

let new_type_evar ?src ?filter ?naming ?principal ?hypnaming env evd rigid =
  let (evd', s) = new_sort_variable rigid evd in
  let (evd', e) = new_evar env evd' ?src ?filter ?naming ?principal ?hypnaming (EConstr.mkSort s) in
  evd', (e, s)

let e_new_type_evar env evdref ?src ?filter ?naming ?principal ?hypnaming rigid =
  let (evd, c) = new_type_evar env !evdref ?src ?filter ?naming ?principal ?hypnaming rigid in
    evdref := evd;
    c

let new_Type ?(rigid=Evd.univ_flexible) evd =
  let open EConstr in
  let (evd, s) = new_sort_variable rigid evd in
  (evd, mkSort s)

let e_new_Type ?(rigid=Evd.univ_flexible) evdref =
  let evd', s = new_sort_variable rigid !evdref in
    evdref := evd'; EConstr.mkSort s

  (* The same using side-effect *)
let e_new_evar env evdref ?(src=default_source) ?filter ?candidates ?store ?naming ?principal ?hypnaming ty =
  let (evd',ev) = new_evar env !evdref ~src:src ?filter ?candidates ?store ?naming ?principal ?hypnaming ty in
  evdref := evd';
  ev

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
  let evi = Evd.find sigma ev in
  let sign = named_context_of_val evi.evar_hyps in
  List.fold_left2
    (fun (c,inst as x) a d ->
      if isRel sigma a then (mkNamedProd_or_LetIn d c,a::inst) else x)
     (evi.evar_concl,[]) (Array.to_list args) sign

(************************************)
(* Removing a dependency in an evar *)
(************************************)

type clear_dependency_error =
| OccurHypInSimpleClause of Id.t option
| EvarTypingBreak of existential
| NoCandidatesLeft of Evar.t

exception ClearDependencyError of Id.t * clear_dependency_error * GlobRef.t option

exception Depends of Id.t

let set_of_evctx l =
  List.fold_left (fun s decl -> Id.Set.add (NamedDecl.get_id decl) s) Id.Set.empty l

let filter_effective_candidates evd evi filter candidates =
  let ids = set_of_evctx (Filter.filter_list filter (evar_context evi)) in
  List.filter (fun a -> Id.Set.subset (collect_vars evd a) ids) candidates

let restrict_evar evd evk filter ?src candidates =
  let evar_info = Evd.find_undefined evd evk in
  let candidates = Option.map (filter_effective_candidates evd evar_info filter) candidates in
  match candidates with
  | Some [] -> raise (ClearDependencyError (*FIXME*)(Id.of_string "blah", (NoCandidatesLeft evk), None))
  | _ ->
     let evd, evk' = Evd.restrict evk filter ?candidates ?src evd in
     (** Mark new evar as future goal, removing previous one,
         circumventing Proofview.advance but making Proof.run_tactic catch these. *)
     let future_goals = Evd.save_future_goals evd in
     let future_goals = Evd.filter_future_goals (fun evk' -> not (Evar.equal evk evk')) future_goals in
     let evd = Evd.restore_future_goals evd future_goals in
     (Evd.declare_future_goal evk' evd, evk')

let rec check_and_clear_in_constr env evdref err ids global c =
  (* returns a new constr where all the evars have been 'cleaned'
     (ie the hypotheses ids have been removed from the contexts of
     evars). [global] should be true iff there is some variable of [ids] which
     is a section variable *)
    match kind c with
      | Var id' ->
      if Id.Set.mem id' ids then raise (ClearDependencyError (id', err, None)) else c

      | ( Const _ | Ind _ | Construct _ ) ->
        let () = if global then
          let check id' =
            if Id.Set.mem id' ids then
              raise (ClearDependencyError (id',err,Some (Globnames.global_of_constr c)))
          in
          Id.Set.iter check (Environ.vars_of_global env c)
        in
        c

      | Evar (evk,l as ev) ->
	  if Evd.is_defined !evdref evk then
	    (* If evk is already defined we replace it by its definition *)
            let nc = Evd.existential_value !evdref (EConstr.of_existential ev) in
            let nc = EConstr.Unsafe.to_constr nc in
	      (check_and_clear_in_constr env evdref err ids global nc)
	  else
	    (* We check for dependencies to elements of ids in the
	       evar_info corresponding to e and in the instance of
	       arguments. Concurrently, we build a new evar
	       corresponding to e where hypotheses of ids have been
	       removed *)
	    let evi = Evd.find_undefined !evdref evk in
	    let ctxt = Evd.evar_filtered_context evi in
            let (rids,filter) =
              List.fold_right2
                (fun h a (ri,filter) ->
                  try
                  (* Check if some id to clear occurs in the instance
                     a of rid in ev and remember the dependency *)
                    let check id = if Id.Set.mem id ids then raise (Depends id) in
                    let () = Id.Set.iter check (collect_vars !evdref (EConstr.of_constr a)) in
                  (* Check if some rid to clear in the context of ev
                     has dependencies in another hyp of the context of ev
                     and transitively remember the dependency *)
                    let check id _ =
                      if occur_var_in_decl (Global.env ()) !evdref id h
                      then raise (Depends id)
                    in
                    let () = Id.Map.iter check ri in
                  (* No dependency at all, we can keep this ev's context hyp *)
                    (ri, true::filter)
                  with Depends id -> (Id.Map.add (NamedDecl.get_id h) id ri, false::filter))
		ctxt (Array.to_list l) (Id.Map.empty,[]) in
	    (* Check if some rid to clear in the context of ev has dependencies
	       in the type of ev and adjust the source of the dependency *)
	    let _nconcl =
	      try
                let nids = Id.Map.domain rids in
                let global = Id.Set.exists is_section_variable nids in
                let concl = EConstr.Unsafe.to_constr (evar_concl evi) in
                check_and_clear_in_constr env evdref (EvarTypingBreak ev) nids global concl
              with ClearDependencyError (rid,err,where) ->
                raise (ClearDependencyError (Id.Map.find rid rids,err,where)) in

            if Id.Map.is_empty rids then c
            else
              let origfilter = Evd.evar_filter evi in
              let filter = Evd.Filter.apply_subfilter origfilter filter in
              let evd = !evdref in
              let candidates = Evd.evar_candidates evi in
              let candidates = Option.map (List.map EConstr.of_constr) candidates in
              let (evd,_) = restrict_evar evd evk filter candidates in
              evdref := evd;
              Evd.existential_value0 !evdref ev

      | _ -> Constr.map (check_and_clear_in_constr env evdref err ids global) c

let clear_hyps_in_evi_main env sigma hyps terms ids =
  (* clear_hyps_in_evi erases hypotheses ids in hyps, checking if some
     hypothesis does not depend on a element of ids, and erases ids in
     the contexts of the evars occurring in evi *)
  let evdref = ref sigma in
  let terms = List.map EConstr.Unsafe.to_constr terms in
  let global = Id.Set.exists is_section_variable ids in
  let terms =
    List.map (check_and_clear_in_constr env evdref (OccurHypInSimpleClause None) ids global) terms in
  let nhyps =
    let check_context decl =
      let err = OccurHypInSimpleClause (Some (NamedDecl.get_id decl)) in
      NamedDecl.map_constr (check_and_clear_in_constr env evdref err ids global) decl
    in
    let check_value vk = match force_lazy_val vk with
    | None -> vk
    | Some (_, d) ->
      if (Id.Set.for_all (fun e -> not (Id.Set.mem e d)) ids) then
        (* v does depend on any of ids, it's ok *)
        vk
      else
        (* v depends on one of the cleared hyps:
            we forget the computed value *)
        dummy_lazy_val ()
    in
      remove_hyps ids check_context check_value hyps
  in
  (!evdref, nhyps,List.map EConstr.of_constr terms)

let clear_hyps_in_evi env sigma hyps concl ids =
  match clear_hyps_in_evi_main env sigma hyps [concl] ids with
  | (sigma,nhyps,[nconcl]) -> (sigma,nhyps,nconcl)
  | _ -> assert false

let clear_hyps2_in_evi env sigma hyps t concl ids =
  match clear_hyps_in_evi_main env sigma hyps [t;concl] ids with
  | (sigma,nhyps,[t;nconcl]) -> (sigma,nhyps,t,nconcl)
  | _ -> assert false

(* spiwack: a few functions to gather evars on which goals depend. *)
let queue_set q is_dependent set =
  Evar.Set.iter (fun a -> Queue.push (is_dependent,a) q) set
let queue_term q is_dependent c =
  queue_set q is_dependent (evars_of_term (EConstr.Unsafe.to_constr c))

let process_dependent_evar q acc evm is_dependent e =
  let evi = Evd.find evm e in
  (* Queues evars appearing in the types of the goal (conclusion, then
     hypotheses), they are all dependent. *)
  queue_term q true evi.evar_concl;
  List.iter begin fun decl ->
    let open NamedDecl in
    queue_term q true (NamedDecl.get_type decl);
    match decl with
    | LocalAssum _ -> ()
    | LocalDef (_,b,_) -> queue_term q true b
  end (EConstr.named_context_of_val evi.evar_hyps);
  match evi.evar_body with
  | Evar_empty ->
      if is_dependent then Evar.Map.add e None acc else acc
  | Evar_defined b ->
      let subevars = evars_of_term (EConstr.Unsafe.to_constr b) in
      (* evars appearing in the definition of an evar [e] are marked
         as dependent when [e] is dependent itself: if [e] is a
         non-dependent goal, then, unless they are reach from another
         path, these evars are just other non-dependent goals. *)
      queue_set q is_dependent subevars;
      if is_dependent then Evar.Map.add e (Some subevars) acc else acc

let gather_dependent_evars q evm =
  let acc = ref Evar.Map.empty in
  while not (Queue.is_empty q) do
    let (is_dependent,e) = Queue.pop q in
    (* checks if [e] has already been added to [!acc] *)
    begin if not (Evar.Map.mem e !acc) then
        acc := process_dependent_evar q !acc evm is_dependent e  
    end
  done;
  !acc

let gather_dependent_evars evm l =
  let q = Queue.create () in
  List.iter (fun a -> Queue.add (false,a) q) l;
  gather_dependent_evars q evm

(* /spiwack *)

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
  let evi = Evd.find sigma evk in
  match evi.evar_body with
  | Evar_empty -> Some evk
  | Evar_defined v ->
      match is_restricted_evar evi with
      | Some evk -> advance sigma evk
      | None -> None

(** The following functions return the set of undefined evars
    contained in the object, the defined evars being traversed.
    This is roughly a combination of the previous functions and
    [nf_evar]. *)

let undefined_evars_of_term evd t =
  let rec evrec acc c =
    match EConstr.kind evd c with
      | Evar (n, l) ->
        let acc = Evar.Set.add n acc in
	Array.fold_left evrec acc l
      | _ -> EConstr.fold evd evrec acc c
  in
  evrec Evar.Set.empty t

let undefined_evars_of_named_context evd nc =
  Context.Named.fold_outside
    (NamedDecl.fold_constr (fun c s -> Evar.Set.union s (undefined_evars_of_term evd (EConstr.of_constr c))))
    nc
    ~init:Evar.Set.empty

let undefined_evars_of_evar_info evd evi =
  Evar.Set.union (undefined_evars_of_term evd evi.evar_concl)
    (Evar.Set.union
       (match evi.evar_body with
	 | Evar_empty -> Evar.Set.empty
         | Evar_defined b -> undefined_evars_of_term evd b)
       (undefined_evars_of_named_context evd
	  (named_context_of_val evi.evar_hyps)))

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
  let id = NamedDecl.get_id decl in
  let r =
    try Id.Map.find id cache.cache
    with Not_found ->
      (** Dummy value *)
      let r = ref (NamedDecl.LocalAssum (id, EConstr.mkProp), Evar.Set.empty) in
      let () = cache.cache <- Id.Map.add id r cache.cache in
      r
  in
  let (decl', evs) = !r in
  let evs =
    if NamedDecl.equal (==) decl decl' then snd !r
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

let filtered_undefined_evars_of_evar_info ?cache sigma evi =
  let evars_of_named_context cache accu nc =
    let fold decl accu = cached_evar_of_hyp cache sigma (EConstr.of_named_decl decl) accu in
    Context.Named.fold_outside fold nc ~init:accu
  in
  let accu = match evi.evar_body with
  | Evar_empty -> Evar.Set.empty
  | Evar_defined b -> evars_of_term (EConstr.Unsafe.to_constr b)
  in
  let accu = Evar.Set.union (undefined_evars_of_term sigma evi.evar_concl) accu in
  let ctxt = EConstr.Unsafe.to_named_context (evar_filtered_context evi) in
  evars_of_named_context cache accu ctxt

(* spiwack: this is a more complete version of
   {!Termops.occur_evar}. The latter does not look recursively into an
   [evar_map]. If unification only need to check superficially, tactics
   do not have this luxury, and need the more complete version. *)
let occur_evar_upto sigma n c =
  let c = EConstr.Unsafe.to_constr c in
  let rec occur_rec c = match kind c with
    | Evar (sp,_) when Evar.equal sp n -> raise Occur
    | Evar e -> Option.iter occur_rec (existential_opt_value0 sigma e)
    | _ -> Constr.iter occur_rec c
  in
  try occur_rec c; false with Occur -> true

(* We don't try to guess in which sort the type should be defined, since
   any type has type Type. May cause some trouble, but not so far... *)

let judge_of_new_Type evd =
  let open EConstr in
  let (evd', s) = new_univ_variable univ_rigid evd in
  (evd', { uj_val = mkSort (Type s); uj_type = mkSort (Type (Univ.super s)) })

let subterm_source evk ?where (loc,k) =
  let evk = match k with
    | Evar_kinds.SubEvar (None,evk) when where = None -> evk
    | _ -> evk in
  (loc,Evar_kinds.SubEvar (where,evk))

(* Add equality constraints for covariant/invariant positions. For
   irrelevant positions, unify universes when flexible. *)
let compare_cumulative_instances cv_pb variances u u' sigma =
  let open UnivProblem in
  let cstrs = Univ.Constraint.empty in
  let soft = Set.empty in
  let cstrs, soft = Array.fold_left3 (fun (cstrs, soft) v u u' ->
      let open Univ.Variance in
      match v with
      | Irrelevant -> cstrs, Set.add (UWeak (u,u')) soft
      | Covariant when cv_pb == Reduction.CUMUL ->
        Univ.Constraint.add (u,Univ.Le,u') cstrs, soft
      | Covariant | Invariant -> Univ.Constraint.add (u,Univ.Eq,u') cstrs, soft)
      (cstrs,soft) variances (Univ.Instance.to_array u) (Univ.Instance.to_array u')
  in
  match Evd.add_constraints sigma cstrs with
  | sigma ->
    Inl (Evd.add_universe_constraints sigma soft)
  | exception Univ.UniverseInconsistency p -> Inr p

let compare_constructor_instances evd u u' =
  let open UnivProblem in
  let soft =
    Array.fold_left2 (fun cs u u' -> Set.add (UWeak (u,u')) cs)
      Set.empty (Univ.Instance.to_array u) (Univ.Instance.to_array u')
  in
  Evd.add_universe_constraints evd soft

(** [eq_constr_univs_test sigma1 sigma2 t u] tests equality of [t] and
    [u] up to existential variable instantiation and equalisable
    universes. The term [t] is interpreted in [sigma1] while [u] is
    interpreted in [sigma2]. The universe constraints in [sigma2] are
    assumed to be an extention of those in [sigma1]. *)
let eq_constr_univs_test sigma1 sigma2 t u =
  (* spiwack: mild code duplication with {!Evd.eq_constr_univs}. *)
  let open Evd in
  let t = EConstr.Unsafe.to_constr t
  and u = EConstr.Unsafe.to_constr u in
  let fold cstr sigma =
    try Some (add_universe_constraints sigma cstr)
    with Univ.UniverseInconsistency _ | UniversesDiffer -> None
  in
  let ans =
    UnivProblem.eq_constr_univs_infer_with
      (fun t -> kind_of_term_upto sigma1 t)
      (fun u -> kind_of_term_upto sigma2 u)
      (universes sigma2) fold t u sigma2
  in
  match ans with None -> false | Some _ -> true
