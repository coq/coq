(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util
open Pp
open Term
open Vars
open Context

(* This module implements the abstract interface to goals *)
(* A general invariant of the module, is that a goal whose associated
   evar is defined in the current evar_map, should not be accessed. *)

(* type of the goals *)
type goal = {
  content : Evd.evar;      (* Corresponding evar. Allows to retrieve
			      logical information once put together
			      with an evar_map. *)
  tags : string list;
  (** Heriditary? tags to be displayed *)
  cache : Evd.evar_map;
  (** Invariant: for all sigma, if gl.cache == sigma and gl.content is actually
      pertaining to sigma, then gl is nf-evarized in sigma. We use this not to
      nf-evar goals too often. *)
}
(* spiwack: I don't deal with the tags, yet. It is a worthy discussion
   whether we do want some tags displayed besides the goal or not. *)


let pr_goal {content = e} = str "GOAL:" ++ Pp.int (Evar.repr e)

(* access primitive *)
(* invariant : [e] must exist in [em] *)
let content evars { content = e } = Evd.find evars e


(* Builds a new (empty) goal with evar [e] *)
let build e =
  { content = e ;
    tags = [];
    cache = Evd.empty;
  }


let uid {content = e} = string_of_int (Evar.repr e)
let get_by_uid u =
  (* this necessarily forget about tags.
     when tags are to be implemented, they
     should be done another way.
     We could use the store in evar_extra,
     for instance. *)
  build (Evar.unsafe_of_int (int_of_string u))

(* Builds a new goal with content evar [e] and
   inheriting from goal [gl]*)
let descendent gl e =
  { gl with content = e; cache = Evd.empty }

(* [advance sigma g] returns [Some g'] if [g'] is undefined and
    is the current avatar of [g] (for instance [g] was changed by [clear]
    into [g']). It returns [None] if [g] has been (partially) solved. *)
(* spiwack: [advance] is probably performance critical, and the good
   behaviour of its definition may depend sensitively to the actual
   definition of [Evd.find]. Currently, [Evd.find] starts looking for
   a value in the heap of undefined variable, which is small. Hence in
   the most common case, where [advance] is applied to an unsolved
   goal ([advance] is used to figure if a side effect has modified the
   goal) it terminates quickly. *)
let rec advance sigma g =
  let evi = Evd.find sigma g.content in
  match evi.Evd.evar_body with
  | Evd.Evar_empty -> Some g
  | Evd.Evar_defined v ->
      if Option.default false (Evd.Store.get evi.Evd.evar_extra Evarutil.cleared) then
        let (e,_) = Term.destEvar v in
        let g' = descendent g e in
        advance sigma g'
      else
        None

let solution sigma g =
  let evi = Evd.find sigma g.content in
  match evi.Evd.evar_body with
  | Evd.Evar_empty -> None
  | Evd.Evar_defined v -> Some v

(* Equality function on goals *)
let equal evars1 gl1 evars2 gl2 =
  let evi1 = content evars1 gl1 in
  let evi2 = content evars2 gl2 in
  Evd.eq_evar_info evi1 evi2

(* [contained_in_info e evi] checks whether the evar [e] appears in
   the hypotheses, the conclusion or the body of the evar_info
   [evi]. Note: since we want to use it on goals, the body is actually
   supposed to be empty. *)
let contained_in_info sigma e evi =
  Evar.Set.mem e (Evarutil.(evars_of_evar_info (nf_evar_info sigma evi)))

(* [depends_on sigma src tgt] checks whether the goal [src] appears as an
   existential variable in the definition of the goal [tgt] in [sigma]. *)
let depends_on sigma src tgt =
  let evi = Evd.find sigma tgt.content in
  contained_in_info sigma src.content evi

(* [unifiable sigma g l] checks whether [g] appears in another subgoal
   of [l]. The list [l] may contain [g], but it does not affect the
   result. *)
let unifiable sigma g l =
  List.exists (fun tgt -> g != tgt && depends_on sigma g tgt) l

(* [partition_unifiable sigma l] partitions [l] into a pair [(u,n)]
   where [u] is composed of the unifiable goals, i.e. the goals on
   whose definition other goals of [l] depend, and [n] are the
   non-unifiable goals. *)
let partition_unifiable sigma l =
  List.partition (fun g -> unifiable sigma g l) l

(*** Goal tactics ***)


(* Goal tactics are [subgoal sensitive]-s *)
type subgoals = { subgoals: goal list }

(* type of the base elements of the goal API.*)
(* it has an extra evar_info with respect to what would be expected,
   it is supposed to be the evar_info of the goal in the evar_map.
   The idea is that it is computed by the [run] function as an
   optimisation, since it will generaly not change during the
   evaluation. *)
type 'a sensitive =
    Environ.env -> Evd.evar_map ref -> goal -> Evd.evar_info -> 'a

(* evaluates a goal sensitive value in a given goal (knowing the current evar_map). *)
(* the evar_info corresponding to the goal is computed at once
   as an optimisation (it shouldn't change during the evaluation). *)
let eval t env defs gl =
  let info = content defs gl in
  let env = Environ.reset_with_named_context (Evd.evar_hyps info) env in
  let rdefs = ref defs in
  let r = t env rdefs gl info in
  ( r , !rdefs )

(* monadic bind on sensitive expressions *)
let bind e f = (); fun env rdefs goal info ->
  let a = e env rdefs goal info in
  let r = f a in
  r env rdefs goal info

(* Type of constr with holes used by refine. *)
(* The list of evars doesn't necessarily contain all the evars in the constr,
    only those the constr has introduced. *)
(* The variables in [myevars] are supposed to be stored
   in decreasing order. Breaking this invariant might cause
   many things to go wrong. *)
type refinable = {
  me: constr;
  my_evars: Evd.evar list
}

module Refinable = struct

  let make t = (); fun env rdefs gl info ->
    let r = ref [] in
    let me = t r in
    let me = me env rdefs gl info in
    { me = me; my_evars = !r }

  (* [with_type c typ] constrains term [c] to have type [typ].  *)
  let with_type t typ = (); fun env rdefs _ _ ->
    (* spiwack: this function assumes that no evars can be created during
        this sort of coercion.
        If it is not the case it could produce bugs. We would need to add a handle
        and add the new evars to it. *)
    let my_type = Retyping.get_type_of env !rdefs t in
    let j = Environ.make_judge t my_type in
    let (new_defs,j') =
      Coercion.inh_conv_coerce_to true (Loc.ghost) env !rdefs j typ
    in
    rdefs := new_defs;
    j'.Environ.uj_val

  (* a pessimistic (i.e : there won't be many positive answers) filter
     over evar_maps, acting only on undefined evars *)
  let evar_map_filter_undefined f evm =
    let fold ev evi accu = if f ev evi then ev :: accu else accu in
    (** We rely on the LTR order of fold here... *)
    Evar.Map.fold fold (Evd.undefined_map evm) []

  (* Union, sorted in decreasing order, of two lists of evars in decreasing order. *)
  let rec fusion l1 l2 = match l1 , l2 with
    | [] , _ -> l2
    | _ , [] -> l1
    | a::l1 , b::_ when a > b -> a::(fusion l1 l2)
    | a::l1 , b::l2 when Evar.equal a b -> a::(fusion l1 l2)
    | _ , b::l2 -> b::(fusion l1 l2)

  let update_handle handle init_defs post_defs =
    (* [delta_list] holds the evars that have been introduced by this
       refinement (but not immediatly solved) *)
    let filter ev _ = not (Evd.mem init_defs ev) in
    (* spiwack: this is the hackish part, don't know how to do any better though. *)
    let delta_list = evar_map_filter_undefined filter post_defs in
    (* The variables in [myevars] are supposed to be stored
       in decreasing order. Breaking this invariant might cause
       many things to go wrong. *)
    handle := fusion delta_list !handle

  let constr_of_open_constr handle check_type (evars, c) = (); fun env rdefs gl info ->
    let () = update_handle handle !rdefs evars in
    rdefs := Evd.fold (fun ev evi evd -> if not (Evd.mem !rdefs ev) then Evd.add evd ev evi else evd) evars !rdefs;
    if check_type then with_type c (Evd.evar_concl (content !rdefs gl)) env rdefs gl info
    else c

end

(* [refine t] takes a refinable term and use it as a partial proof for current
    goal. *)
let refine step = (); fun env rdefs gl info ->
  (* subgoals to return *)
  (* The evars in [my_evars] are stored in reverse order.
     It is expectingly better however to display the goal
     in increasing order. *)
  rdefs := Evarconv.consider_remaining_unif_problems env !rdefs ;
  let subgoals = List.map (descendent gl) (List.rev step.my_evars) in
  (* creates the new [evar_map] by defining the evar of the current goal
     as being [refine_step]. *)
  let new_defs = Evd.define gl.content (step.me) !rdefs in
  rdefs := new_defs;
  (* Filtering the [subgoals] for uninstanciated (=unsolved) goals. *)
  let subgoals =
    Option.List.flatten (List.map (advance !rdefs) subgoals)
  in
  { subgoals = subgoals }

let refine_open_constr c =
  let pf h = Refinable.constr_of_open_constr h true c in
  bind (Refinable.make pf) refine

let enter f = (); fun env rdefs gl info ->
  let sigma = !rdefs in
  f env sigma (Evd.evar_hyps info) (Evd.evar_concl info) gl

let nf_enter f = (); fun env rdefs gl info ->
  let sigma = !rdefs in
  if gl.cache == sigma then
    f env sigma (Evd.evar_hyps info) (Evd.evar_concl info) gl
  else
    let info = Evarutil.nf_evar_info sigma info in
    let sigma = Evd.add sigma gl.content info in
    let gl = { gl with cache = sigma } in
    let () = rdefs := sigma in
    let hyps = Evd.evar_hyps info in
    let env = Environ.reset_with_named_context hyps env in
    f env sigma hyps (Evd.evar_concl info) gl

(* Layer to implement v8.2 tactic engine ontop of the new architecture.
   Types are different from what they used to be due to a change of the
   internal types. *)
module V82 = struct

  (* Old style env primitive *)
  let env evars gl =
    let evi = content evars gl in
    Evd.evar_filtered_env evi

  (* same as [env], but ensures that existential variables are
     normalised *)
  let nf_env evars gl =
    Evarutil.nf_env_evar evars (env evars gl)

  (* Old style hyps primitive *)
  let hyps evars gl =
    let evi = content evars gl in
    Evd.evar_filtered_hyps evi

  (* same as [hyps], but ensures that existential variables are
     normalised. *)
  let nf_hyps evars gl =
    let hyps = Environ.named_context_of_val (hyps evars gl) in
    Environ.val_of_named_context (Evarutil.nf_named_context_evar evars hyps)

  (* Access to ".evar_concl" *)
  let concl evars gl =
    let evi = content evars gl in
    evi.Evd.evar_concl

  (* same as [concl] but ensures that existential variables are
     normalised. *)
  let nf_concl evars gl =
    Evarutil.nf_evar evars (concl evars gl)

  (* Access to ".evar_extra" *)
  let extra evars gl =
    let evi = content evars gl in
    evi.Evd.evar_extra

  (* Old style filtered_context primitive *)
  let filtered_context evars gl =
    let evi = content evars gl in
    Evd.evar_filtered_context evi

  (* Old style mk_goal primitive *)
  let mk_goal evars hyps concl extra =
    let evi = { Evd.evar_hyps = hyps;
		Evd.evar_concl = concl;
		Evd.evar_filter = Evd.Filter.identity;
		Evd.evar_body = Evd.Evar_empty;
		Evd.evar_source = (Loc.ghost,Evar_kinds.GoalEvar);
		Evd.evar_candidates = None;
		Evd.evar_extra = extra }
    in
    let evi = Typeclasses.mark_unresolvable evi in
    let (evars, evk) = Evarutil.new_pure_evar_full evars evi in
    let ctxt = Environ.named_context_of_val hyps in
    let inst = Array.map_of_list (fun (id, _, _) -> mkVar id) ctxt in
    let ev = Term.mkEvar (evk,inst) in
    (build evk, ev, evars)

  (* Creates a dummy [goal sigma] for use in auto *)
  let dummy_goal =
    (* This goal seems to be marshalled somewhere. Therefore it cannot be
       marked unresolvable for typeclasses, as non-empty Store.t-s happen
       to have functional content. *)
    let evi = Evd.make_evar Environ.empty_named_context_val Term.mkProp in
    let (sigma, evk) = Evarutil.new_pure_evar_full Evd.empty evi in
    { Evd.it = build evk ; Evd.sigma = sigma; }

  (* Makes a goal out of an evar *)
  let build = build

  (* Instantiates a goal with an open term *)
  let partial_solution sigma { content=evk } c =
    Evd.define evk c sigma

  (* Parts of the progress tactical *)
  let same_goal evars1 gl1 evars2 gl2 =
    let evi1 = content evars1 gl1 in
    let evi2 = content evars2 gl2 in
    Term.eq_constr evi1.Evd.evar_concl evi2.Evd.evar_concl &&
    Environ.eq_named_context_val evi1.Evd.evar_hyps evi2.Evd.evar_hyps

  let weak_progress glss gls =
    match glss.Evd.it with
    | [ g ] -> not (same_goal glss.Evd.sigma g gls.Evd.sigma gls.Evd.it)
    | _ -> true

  let progress glss gls =
    weak_progress glss gls
    (* spiwack: progress normally goes like this:
    (Evd.progress_evar_map gls.Evd.sigma glss.Evd.sigma) || (weak_progress glss gls)
       This is immensly slow in the current implementation. Maybe we could
       reimplement progress_evar_map with restricted folds like "fold_undefined",
       with a good implementation of them.
    *)

  (* Used for congruence closure and change *)
  let new_goal_with sigma gl extra_hyps =
    let evi = content sigma gl in
    let hyps = evi.Evd.evar_hyps in
    let new_hyps =
      List.fold_right Environ.push_named_context_val extra_hyps hyps in
    let filter = evi.Evd.evar_filter in
    let new_filter = Evd.Filter.extend (List.length extra_hyps) filter in
    let new_evi =
      { evi with Evd.evar_hyps = new_hyps; Evd.evar_filter = new_filter } in
    let new_evi = Typeclasses.mark_unresolvable new_evi in
    let (new_sigma, evk) = Evarutil.new_pure_evar_full Evd.empty new_evi in
    { Evd.it = build evk ; sigma = new_sigma; }

  (* Used by the compatibility layer and typeclasses *)
  let nf_evar sigma gl =
    if sigma == gl.cache then (gl, sigma)
    else
      let evi = content sigma gl in
      let evi = Evarutil.nf_evar_info sigma evi in
      let sigma = Evd.add sigma gl.content evi in
      ({ gl with cache = sigma }, sigma)

  (* Goal represented as a type, doesn't take into account section variables *)
  let abstract_type sigma gl =
    let (gl,sigma) = nf_evar sigma gl in
    let env = env sigma gl in
    let genv = Global.env () in
    let is_proof_var decl =
      try ignore (Environ.lookup_named (Util.pi1 decl) genv); false
      with Not_found -> true in
    Environ.fold_named_context_reverse (fun t decl ->
					  if is_proof_var decl then
					    mkNamedProd_or_LetIn decl t
					  else
					    t
				       ) ~init:(concl sigma gl) env

end
