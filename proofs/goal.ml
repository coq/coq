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
  tags : string list       (* Heriditary? tags to be displayed *)
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
    tags = []
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
  { gl with content = e}

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
        let g' = { g with content = e } in
        advance sigma g'
      else
        None


(* Equality function on goals *)
let equal evars1 gl1 evars2 gl2 =
  let evi1 = content evars1 gl1 in
  let evi2 = content evars2 gl2 in
  Evd.eq_evar_info evi1 evi2

(* [contained_in_info e evi] checks whether the evar [e] appears in
   the hypotheses, the conclusion or the body of the evar_info
   [evi]. Note: since we want to use it on goals, the body is actually
   supposed to be empty. *)
let contained_in_info e evi =
  Evar.Set.mem e (Evarutil.evars_of_evar_info evi)

(* [depends_on sigma src tgt] checks whether the goal [src] appears as an
   existential variable in the definition of the goal [tgt] in [sigma]. *)
let depends_on sigma src tgt =
  let evi = Evd.find sigma tgt.content in
  contained_in_info src.content evi

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

(* monadic return on sensitive expressions *)
let return v = () ; fun _ _ _ _ -> v

(* interpretation of "open" constr *)
(* spiwack: it is a wrapper around [Constrintern.interp_open_constr].
    In an ideal world, this could/should be the other way round.
    As of now, though, it seems at least quite useful to build tactics. *)
let interp_constr cexpr = (); fun env rdefs _ _ ->
  Constrintern.interp_constr_evars rdefs env cexpr

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
  type t = refinable

  type handle = Evd.evar list ref

  let make t = (); fun env rdefs gl info ->
    let r = ref [] in
    let me = t r in
    let me = me env rdefs gl info in
    { me = me; my_evars = !r }
  let make_with t = (); fun env rdefs gl info ->
    let r = ref [] in
    let t = t r in
    let (me,side) = t env rdefs gl info in
    ({ me = me ; my_evars = !r }, side)

  let mkEvar handle env typ = (); fun _ rdefs _ _ ->
    let ev = Evarutil.e_new_evar rdefs env typ in
    let (e,_) = destEvar ev in
    handle := e::!handle;
    ev

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

  (* spiwack: it is not very fine grain since it solves all typeclasses holes,
      not only those containing the current goal, or a given term. But it
      seems to fit our needs so far. *)
  let resolve_typeclasses ?filter ?split ?(fail=false) () = (); fun env rdefs _ _ ->
    rdefs:=Typeclasses.resolve_typeclasses ?filter ?split ~fail env !rdefs



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

  (* [constr_of_raw h tycon flags] is a pretyping function.
      The [tycon] argument allows to put a type constraint on the returned term.
      The [flags] argument is passed to the pretyper.
      The principal argument is a [glob_constr] which is then pretyped in the
      context of a term, the remaining evars are registered to the handle.
      It is the main component of the toplevel refine tactic.*)
  (* spiwack: it is not entirely satisfactory to have this function here. Plus it is
      a bit hackish. However it does not seem possible to move it out until
      pretyping is defined as some proof procedure. *)
  let constr_of_raw handle tycon flags lvar rawc = (); fun env rdefs gl info ->
    (* We need to keep trace of what [rdefs] was originally*)
    let init_defs = !rdefs in
    (* call to [understand_tcc_evars] returns a constr with undefined evars
       these evars will be our new goals *)
    let (sigma, open_constr) =
      Pretyping.understand_ltac flags !rdefs env lvar tycon rawc
    in
    let () = rdefs := sigma in
    let () = update_handle handle init_defs !rdefs in
    open_constr

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


(*** Cleaning  goals ***)

let clear ids = (); fun env rdefs gl info ->
  let hyps = Evd.evar_hyps info in
  let concl = Evd.evar_concl info in
  let (hyps,concl) = Evarutil.clear_hyps_in_evi rdefs hyps concl ids in
  let cleared_env = Environ.reset_with_named_context hyps env in
  let cleared_concl = Evarutil.e_new_evar rdefs cleared_env concl in
  let (cleared_evar,_) = destEvar cleared_concl in
  let cleared_goal = descendent gl cleared_evar in
  rdefs := Evd.define gl.content cleared_concl !rdefs;
  { subgoals = [cleared_goal] }

let wrap_apply_to_hyp_and_dependent_on sign id f g =
  try Environ.apply_to_hyp_and_dependent_on sign id f g
  with Environ.Hyp_not_found ->
    Errors.error "No such assumption"

let check_typability env sigma c =
  let _ = Typing.type_of env sigma c in ()

let recheck_typability (what,id) env sigma t =
  try check_typability env sigma t
  with e when Errors.noncritical e ->
    let s = match what with
      | None -> "the conclusion"
      | Some id -> "hypothesis "^(Names.Id.to_string id) in
    Errors.error
      ("The correctness of "^s^" relies on the body of "^(Names.Id.to_string id))

let remove_hyp_body env sigma id =
  let sign =
    wrap_apply_to_hyp_and_dependent_on (Environ.named_context_val env) id
      (fun (_,c,t) _ ->
	match c with
	| None -> Errors.error ((Names.Id.to_string id)^" is not a local definition")
	| Some c ->(id,None,t))
      (fun (id',c,t as d) sign ->
	(
	  begin
	    let env = Environ.reset_with_named_context sign env in
	    match c with
	    | None ->  recheck_typability (Some id',id) env sigma t
	    | Some b ->
		let b' = mkCast (b,DEFAULTcast, t) in
		recheck_typability (Some id',id) env sigma b'
	  end;d))
  in
  Environ.reset_with_named_context sign env


let clear_body idents = (); fun env rdefs gl info ->
  let info = content !rdefs gl in
  let full_env = Environ.reset_with_named_context (Evd.evar_hyps info) env in
  let aux env id =
     let env' = remove_hyp_body env !rdefs id in
       recheck_typability (None,id) env' !rdefs (Evd.evar_concl info);
       env'
  in
  let new_env =
    List.fold_left aux full_env idents
  in
  let concl = Evd.evar_concl info in
  let (defs',new_constr) = Evarutil.new_evar !rdefs new_env concl in
  let (new_evar,_) = destEvar new_constr in
  let new_goal = descendent gl new_evar in
  rdefs := Evd.define gl.content new_constr defs';
  { subgoals = [new_goal] }


(*** Sensitive primitives ***)

(* representation of the goal in form of an {!Evd.evar_info} *)
let info _ _ _ info = info

(* [concl] is the conclusion of the current goal *)
let concl _ _ _ info =
  Evd.evar_concl info

(* [hyps] is the [named_context_val] representing the hypotheses
   of the current goal *)
let hyps _ _ _ info =
  Evd.evar_hyps info

(* [env] is the current [Environ.env] containing both the
   environment in which the proof is ran, and the goal hypotheses *)
let env env _ _ _ = env

(* [defs] is the [Evd.evar_map] at the current evaluation point *)
let defs _ rdefs _ _ =
  !rdefs

let enter f = (); fun env rdefs gl info ->
  let sigma = !rdefs in
  f env sigma (Evd.evar_hyps info) (Evd.evar_concl info) gl

(*** Conversion in goals ***)

let convert_hyp check (id,b,bt as d) = (); fun env rdefs gl info ->
  let sigma = !rdefs in
  (* This function substitutes the new type and body definitions
     in the appropriate variable when used with {!Environ.apply_hyps}. *)
  let replace_function =
    (fun _ (_,c,ct) _ ->
       if check && not (Reductionops.is_conv env sigma bt ct) then
	 Errors.error ("Incorrect change of the type of "^(Names.Id.to_string id));
       if check && not (Option.equal (Reductionops.is_conv env sigma) b c) then
	 Errors.error ("Incorrect change of the body of "^(Names.Id.to_string id));
       d)
  in
  (* Modified named context. *)
  let new_hyps =
    let hyps = hyps env rdefs gl info in
    Environ.apply_to_hyp hyps id replace_function
  in
  let new_env = Environ.reset_with_named_context new_hyps env in
  let new_constr =
    let concl = concl env rdefs gl info in
    Evarutil.e_new_evar rdefs new_env concl
  in
  let (new_evar,_) = destEvar new_constr in
  let new_goal = descendent gl new_evar in
  rdefs := Evd.define gl.content new_constr !rdefs;
  { subgoals = [new_goal] }

let convert_concl check cl' = (); fun env rdefs gl info ->
  let sigma = !rdefs in
  let cl = concl env rdefs gl info in
  check_typability env sigma cl';
  if (not check) || Reductionops.is_conv_leq env sigma cl' cl then
    let new_constr =
      Evarutil.e_new_evar rdefs env cl'
    in
    let (new_evar,_) = destEvar new_constr in
    let new_goal = descendent gl new_evar in
    rdefs := Evd.define gl.content new_constr !rdefs;
    { subgoals = [new_goal] }
  else
    Errors.error "convert-concl rule passed non-converting term"


(*** Bureaucracy in hypotheses ***)

(* Renames a hypothesis. *)
let rename_hyp_sign id1 id2 sign =
  let subst = [id1,mkVar id2] in
  let replace_vars c = replace_vars subst c in
  Environ.apply_to_hyp_and_dependent_on sign id1
    (fun (_,b,t) _ -> (id2,b,t))
    (fun d _ -> map_named_declaration replace_vars d)

let rename_hyp id1 id2 = (); fun env rdefs gl info ->
  let hyps = hyps env rdefs gl info in
  if not (Names.Id.equal id1 id2) &&
    Names.Id.List.mem id2
      (Termops.ids_of_named_context (Environ.named_context_of_val hyps))
  then
    Errors.error ((Names.Id.to_string id2)^" is already used.");
  let new_hyps = rename_hyp_sign id1 id2 hyps in
  let new_env = Environ.reset_with_named_context new_hyps env in
  let old_concl = concl env rdefs gl info in
  let new_concl = Vars.replace_vars [id1,mkVar id2] old_concl in
  let new_subproof = Evarutil.e_new_evar rdefs new_env new_concl in
  let new_subproof = Vars.replace_vars [id2,mkVar id1] new_subproof in
  let (new_evar,_) = destEvar new_subproof in
  let new_goal = descendent gl new_evar in
  rdefs := Evd.define gl.content new_subproof !rdefs;
  { subgoals = [new_goal] }


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
    let evi = content sigma gl in
    let evi = Evarutil.nf_evar_info sigma evi in
    let sigma = Evd.add sigma gl.content evi in
    (gl,sigma)

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

  let to_sensitive f = (); fun _ rsigma g _ ->
    f { Evd.it = g ; sigma = !rsigma }
  let change_evar_map sigma = (); fun _ rsigma _ _ ->
    (rsigma := sigma)
end
