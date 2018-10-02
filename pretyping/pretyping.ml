(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* This file contains the syntax-directed part of the type inference
   algorithm introduced by Murthy in Coq V5.10, 1995; the type
   inference algorithm was initially developed in a file named trad.ml
   which formerly contained a simple concrete-to-abstract syntax
   translation function introduced in CoC V4.10 for implementing the
   "exact" tactic, 1989 *)
(* Support for typing term in Ltac environment by David Delahaye, 2000 *)
(* Type inference algorithm made a functor of the coercion and
   pattern-matching compilation by Matthieu Sozeau, March 2006 *)
(* Fixpoint guard index computation by Pierre Letouzey, July 2007 *)

(* Structural maintainer: Hugo Herbelin *)
(* Secondary maintenance: collective *)


open Pp
open CErrors
open Util
open Names
open Evd
open Constr
open Term
open Termops
open Environ
open EConstr
open Vars
open Reductionops
open Type_errors
open Typing
open Globnames
open Nameops
open Evarutil
open Evardefine
open Pretype_errors
open Glob_term
open Glob_ops
open Evarconv
open Ltac_pretype

module NamedDecl = Context.Named.Declaration

type typing_constraint = OfType of types | IsType | WithoutTypeConstraint

(************************************************************************)
(* This concerns Cases *)
open Inductive
open Inductiveops

(************************************************************************)

module ExtraEnv =
struct

type t = {
  env : Environ.env;
  extra : Evarutil.ext_named_context Lazy.t;
  (** Delay the computation of the evar extended environment *)
}

let get_extra env sigma =
  let open Context.Named.Declaration in
  let ids = List.map get_id (named_context env) in
  let avoid = List.fold_right Id.Set.add ids Id.Set.empty in
  Context.Rel.fold_outside (fun d acc -> push_rel_decl_to_named_context sigma d acc)
    (rel_context env) ~init:(empty_csubst, avoid, named_context env)

let make_env env sigma = { env = env; extra = lazy (get_extra env sigma) }
let rel_context env = rel_context env.env

let push_rel sigma d env = {
  env = push_rel d env.env;
  extra = lazy (push_rel_decl_to_named_context sigma d (Lazy.force env.extra));
}

let pop_rel_context n env sigma = make_env (pop_rel_context n env.env) sigma

let push_rel_context sigma ctx env = {
  env = push_rel_context ctx env.env;
  extra = lazy (List.fold_right (fun d acc -> push_rel_decl_to_named_context sigma d acc) ctx (Lazy.force env.extra));
}

let lookup_named id env = lookup_named id env.env

let e_new_evar env evdref ?src ?naming typ =
  let open Context.Named.Declaration in
  let inst_vars = List.map (get_id %> mkVar) (named_context env.env) in
  let inst_rels = List.rev (rel_list 0 (nb_rel env.env)) in
  let (subst, _, nc) = Lazy.force env.extra in
  let typ' = csubst_subst subst typ in
  let instance = inst_rels @ inst_vars in
  let sign = val_of_named_context nc in
  let sigma = !evdref in
  let (sigma, e) = new_evar_instance sign sigma typ' ?src ?naming instance in
  evdref := sigma;
  e

let push_rec_types sigma (lna,typarray,_) env =
  let ctxt = Array.map2_i (fun i na t -> Context.Rel.Declaration.LocalAssum (na, lift i t)) lna typarray in
  Array.fold_left (fun e assum -> push_rel sigma assum e) env ctxt

end

open ExtraEnv

(* An auxiliary function for searching for fixpoint guard indexes *)

exception Found of int array

let nf_fix sigma (nas, cs, ts) =
  let inj c = EConstr.to_constr ~abort_on_undefined_evars:false sigma c in
  (nas, Array.map inj cs, Array.map inj ts)

let search_guard ?loc env possible_indexes fixdefs =
  (* Standard situation with only one possibility for each fix. *)
  (* We treat it separately in order to get proper error msg. *)
  let is_singleton = function [_] -> true | _ -> false in
  if List.for_all is_singleton possible_indexes then
    let indexes = Array.of_list (List.map List.hd possible_indexes) in
    let fix = ((indexes, 0),fixdefs) in
    (try check_fix env fix
     with reraise ->
       let (e, info) = CErrors.push reraise in
       let info = Option.cata (fun loc -> Loc.add_loc info loc) info loc in
       iraise (e, info));
    indexes
  else
    (* we now search recursively among all combinations *)
    (try
       List.iter
	 (fun l ->
	    let indexes = Array.of_list l in
            let fix = ((indexes, 0),fixdefs) in
            (* spiwack: We search for a unspecified structural
               argument under the assumption that we need to check the
               guardedness condition (otherwise the first inductive argument
               will be chosen). A more robust solution may be to raise an
               error when totality is assumed but the strutural argument is
               not specified. *)
            try
              let flags = { (typing_flags env) with Declarations.check_guarded = true } in
              let env = Environ.set_typing_flags flags env in
              check_fix env fix; raise (Found indexes)
	    with TypeError _ -> ())
	 (List.combinations possible_indexes);
       let errmsg = "Cannot guess decreasing argument of fix." in
	 user_err ?loc ~hdr:"search_guard" (Pp.str errmsg)
     with Found indexes -> indexes)

(* To force universe name declaration before use *)

let strict_universe_declarations = ref true
let is_strict_universe_declarations () = !strict_universe_declarations

let _ =
  Goptions.(declare_bool_option
	  { optdepr  = false;
	    optname  = "strict universe declaration";
	    optkey   = ["Strict";"Universe";"Declaration"];
	    optread  = is_strict_universe_declarations;
	    optwrite = (:=) strict_universe_declarations })

(** Miscellaneous interpretation functions *)

let interp_known_universe_level evd qid =
  try
    let open Libnames in
    if qualid_is_ident qid then Evd.universe_of_name evd @@ qualid_basename qid
    else raise Not_found
  with Not_found ->
    let univ, k = Nametab.locate_universe qid in
    Univ.Level.make univ k

let interp_universe_level_name ~anon_rigidity evd qid =
  try evd, interp_known_universe_level evd qid
  with Not_found ->
    if Libnames.qualid_is_ident qid then (* Undeclared *)
      let id = Libnames.qualid_basename qid in
      if not (is_strict_universe_declarations ()) then
        new_univ_level_variable ?loc:qid.CAst.loc ~name:id univ_rigid evd
      else user_err ?loc:qid.CAst.loc ~hdr:"interp_universe_level_name"
          (Pp.(str "Undeclared universe: " ++ Id.print id))
    else
      let dp, i = Libnames.repr_qualid qid in
      let num =
        try int_of_string (Id.to_string i)
        with Failure _ ->
          user_err ?loc:qid.CAst.loc ~hdr:"interp_universe_level_name"
            (Pp.(str "Undeclared global universe: " ++ Libnames.pr_qualid qid))
      in
      let level = Univ.Level.make dp num in
      let evd =
        try Evd.add_global_univ evd level
        with UGraph.AlreadyDeclared -> evd
      in evd, level

let interp_universe ?loc evd = function
  | [] -> let evd, l = new_univ_level_variable ?loc univ_rigid evd in
	    evd, Univ.Universe.make l
  | l ->
    List.fold_left (fun (evd, u) l ->
      let evd', u' =
        match l with
        | Some (l,n) ->
           (* [univ_flexible_alg] can produce algebraic universes in terms *)
           let anon_rigidity = univ_flexible in
           let evd', l = interp_universe_level_name ~anon_rigidity evd l in
           let u' = Univ.Universe.make l in
           (match n with
            | 0 -> evd', u'
            | 1 -> evd', Univ.Universe.super u'
            | _ ->
               user_err ?loc ~hdr:"interp_universe"
                        (Pp.(str "Cannot interpret universe increment +" ++ int n)))
        | None ->
           let evd, l = new_univ_level_variable ?loc univ_flexible evd in
           evd, Univ.Universe.make l
      in (evd', Univ.sup u u'))
    (evd, Univ.Universe.type0m) l

let interp_known_level_info ?loc evd = function
  | UUnknown | UAnonymous ->
    user_err ?loc ~hdr:"interp_known_level_info"
      (str "Anonymous universes not allowed here.")
  | UNamed qid ->
    try interp_known_universe_level evd qid
    with Not_found ->
      user_err ?loc ~hdr:"interp_known_level_info" (str "Undeclared universe " ++ Libnames.pr_qualid qid)

let interp_level_info ?loc evd : level_info -> _ = function
  | UUnknown -> new_univ_level_variable ?loc univ_rigid evd
  | UAnonymous -> new_univ_level_variable ?loc univ_flexible evd
  | UNamed s -> interp_universe_level_name ~anon_rigidity:univ_flexible evd s

type inference_hook = env -> evar_map -> Evar.t -> evar_map * constr

type inference_flags = {
  use_typeclasses : bool;
  solve_unification_constraints : bool;
  use_hook : inference_hook option;
  fail_evar : bool;
  expand_evars : bool
}

(* Compute the set of still-undefined initial evars up to restriction
   (e.g. clearing) and the set of yet-unsolved evars freshly created
   in the extension [sigma'] of [sigma] (excluding the restrictions of
   the undefined evars of [sigma] to be freshly created evars of
   [sigma']). Otherwise said, we partition the undefined evars of
   [sigma'] into those already in [sigma] or deriving from an evar in
   [sigma] by restriction, and the evars properly created in [sigma'] *)

type frozen =
| FrozenId of evar_info Evar.Map.t
  (** No pending evars. We do not put a set here not to reallocate like crazy,
      but the actual data of the map is not used, only keys matter. All
      functions operating on this type must have the same behaviour on
      [FrozenId map] and [FrozenProgress (Evar.Map.domain map, Evar.Set.empty)] *)
| FrozenProgress of (Evar.Set.t * Evar.Set.t) Lazy.t
  (** Proper partition of the evar map as described above. *)

let frozen_and_pending_holes (sigma, sigma') =
  let undefined0 = Evd.undefined_map sigma in
  (** Fast path when the undefined evars where not modified *)
  if undefined0 == Evd.undefined_map sigma' then
    FrozenId undefined0
  else
    let data = lazy begin
    let add_derivative_of evk evi acc =
      match advance sigma' evk with None -> acc | Some evk' -> Evar.Set.add evk' acc in
    let frozen = Evar.Map.fold add_derivative_of undefined0 Evar.Set.empty in
    let fold evk _ accu = if not (Evar.Set.mem evk frozen) then Evar.Set.add evk accu else accu in
    let pending = Evd.fold_undefined fold sigma' Evar.Set.empty in
    (frozen, pending)
    end in
    FrozenProgress data

let apply_typeclasses env evdref frozen fail_evar =
  let filter_frozen = match frozen with
  | FrozenId map -> fun evk -> Evar.Map.mem evk map
  | FrozenProgress (lazy (frozen, _)) -> fun evk -> Evar.Set.mem evk frozen
  in
  evdref := Typeclasses.resolve_typeclasses
     ~filter:(if Flags.is_program_mode () 
	      then (fun evk evi -> Typeclasses.no_goals_or_obligations evk evi && not (filter_frozen evk))
              else (fun evk evi -> Typeclasses.no_goals evk evi && not (filter_frozen evk)))
     ~split:true ~fail:fail_evar env !evdref;
  if Flags.is_program_mode () then (* Try optionally solving the obligations *)
    evdref := Typeclasses.resolve_typeclasses
      ~filter:(fun evk evi -> Typeclasses.all_evars evk evi && not (filter_frozen evk)) ~split:true ~fail:false env !evdref

let apply_inference_hook hook evdref frozen = match frozen with
| FrozenId _ -> ()
| FrozenProgress (lazy (_, pending)) ->
  evdref := Evar.Set.fold (fun evk sigma ->
    if Evd.is_undefined sigma evk (* in particular not defined by side-effect *)
    then
      try
        let sigma, c = hook sigma evk in
        Evd.define evk c sigma
      with Exit ->
        sigma
    else
      sigma) pending !evdref

let apply_heuristics env evdref fail_evar =
  (* Resolve eagerly, potentially making wrong choices *)
  try evdref := solve_unif_constraints_with_heuristics
	~ts:(Typeclasses.classes_transparent_state ()) env !evdref
  with e when CErrors.noncritical e ->
    let e = CErrors.push e in if fail_evar then iraise e

let check_typeclasses_instances_are_solved env current_sigma frozen =
  (* Naive way, call resolution again with failure flag *)
  apply_typeclasses env (ref current_sigma) frozen true

let check_extra_evars_are_solved env current_sigma frozen = match frozen with
| FrozenId _ -> ()
| FrozenProgress (lazy (_, pending)) ->
  Evar.Set.iter
    (fun evk ->
      if not (Evd.is_defined current_sigma evk) then
        let (loc,k) = evar_source evk current_sigma in
	match k with
	| Evar_kinds.ImplicitArg (gr, (i, id), false) -> ()
	| _ ->
	    error_unsolvable_implicit ?loc env current_sigma evk None) pending

(* [check_evars] fails if some unresolved evar remains *)

let check_evars env initial_sigma sigma c =
  let rec proc_rec c =
    match EConstr.kind sigma c with
    | Evar (evk, _) ->
      if not (Evd.mem initial_sigma evk) then
        let (loc,k) = evar_source evk sigma in
        begin match k with
          | Evar_kinds.ImplicitArg (gr, (i, id), false) -> ()
          | _ -> Pretype_errors.error_unsolvable_implicit ?loc env sigma evk None
        end
    | _ -> EConstr.iter sigma proc_rec c
  in proc_rec c

let check_evars_are_solved env current_sigma frozen =
  check_typeclasses_instances_are_solved env current_sigma frozen;
  check_problems_are_solved env current_sigma;
  check_extra_evars_are_solved env current_sigma frozen

(* Try typeclasses, hooks, unification heuristics ... *)

let solve_remaining_evars flags env current_sigma init_sigma =
  let frozen = frozen_and_pending_holes (init_sigma, current_sigma) in
  let evdref = ref current_sigma in
  if flags.use_typeclasses then apply_typeclasses env evdref frozen false;
  if Option.has_some flags.use_hook then
    apply_inference_hook (Option.get flags.use_hook env) evdref frozen;
  if flags.solve_unification_constraints then apply_heuristics env evdref false;
  if flags.fail_evar then check_evars_are_solved env !evdref frozen;
  !evdref

let check_evars_are_solved env current_sigma init_sigma =
  let frozen = frozen_and_pending_holes (init_sigma, current_sigma) in
  check_evars_are_solved env current_sigma frozen

let process_inference_flags flags env initial_sigma (sigma,c,cty) =
  let sigma = solve_remaining_evars flags env sigma initial_sigma in
  let c = if flags.expand_evars then nf_evar sigma c else c in
  sigma,c,cty

let adjust_evar_source evdref na c =
  match na, kind !evdref c with
  | Name id, Evar (evk,args) ->
     let evi = Evd.find !evdref evk in
     begin match evi.evar_source with
     | loc, Evar_kinds.QuestionMark {
         Evar_kinds.qm_obligation=b;
         Evar_kinds.qm_name=Anonymous;
         Evar_kinds.qm_record_field=recfieldname;
        } ->
        let src = (loc,Evar_kinds.QuestionMark {
            Evar_kinds.qm_obligation=b;
            Evar_kinds.qm_name=na;
            Evar_kinds.qm_record_field=recfieldname;
        }) in
        let (evd, evk') = restrict_evar !evdref evk (evar_filter evi) ~src None in
        evdref := evd;
        mkEvar (evk',args)
     | _ -> c
     end
  | _, _ -> c

(* coerce to tycon if any *)
let inh_conv_coerce_to_tycon ?loc resolve_tc env evdref j = function
  | None -> j
  | Some t ->
      evd_comb2 (Coercion.inh_conv_coerce_to ?loc resolve_tc env.ExtraEnv.env) evdref j t

let check_instance loc subst = function
  | [] -> ()
  | (id,_) :: _ ->
      if List.mem_assoc id subst then
        user_err ?loc  (Id.print id ++ str "appears more than once.")
      else
        user_err ?loc  (str "No such variable in the signature of the existential variable: " ++ Id.print id ++ str ".")

(* used to enforce a name in Lambda when the type constraints itself
   is named, hence possibly dependent *)

let orelse_name name name' = match name with
  | Anonymous -> name'
  | _ -> name

let ltac_interp_name_env k0 lvar env sigma =
  (* envhd is the initial part of the env when pretype was called first *)
  (* (in practice is is probably 0, but we have to grant the
     specification of pretype which accepts to start with a non empty
     rel_context) *)
  (* tail is the part of the env enriched by pretyping *)
  let n = Context.Rel.length (rel_context env) - k0 in
  let ctxt,_ = List.chop n (rel_context env) in
  let open Context.Rel.Declaration in
  let ctxt' = List.Smart.map (map_name (ltac_interp_name lvar)) ctxt in
  if List.equal (fun d1 d2 -> Name.equal (get_name d1) (get_name d2)) ctxt ctxt' then env
  else push_rel_context sigma ctxt' (pop_rel_context n env sigma)

let invert_ltac_bound_name lvar env id0 id =
  let id' = Id.Map.find id lvar.ltac_idents in
  try mkRel (pi1 (lookup_rel_id id' (rel_context env)))
  with Not_found ->
    user_err  (str "Ltac variable " ++ Id.print id0 ++
		       str " depends on pattern variable name " ++ Id.print id ++
		       str " which is not bound in current context.")

let protected_get_type_of env sigma c =
  try Retyping.get_type_of ~lax:true env.ExtraEnv.env sigma c
  with Retyping.RetypeError _ ->
    user_err 
      (str "Cannot reinterpret " ++ quote (Termops.Internal.print_constr_env env.ExtraEnv.env sigma c) ++
       str " in the current environment.")

let pretype_id pretype k0 loc env evdref lvar id =
  let sigma = !evdref in
  (* Look for the binder of [id] *)
  try
    let (n,_,typ) = lookup_rel_id id (rel_context env) in
      { uj_val  = mkRel n; uj_type = lift n typ }
  with Not_found ->
    let env = ltac_interp_name_env k0 lvar env !evdref in
    (* Check if [id] is an ltac variable *)
    try
      let (ids,c) = Id.Map.find id lvar.ltac_constrs in
      let subst = List.map (invert_ltac_bound_name lvar env id) ids in
      let c = substl subst c in
	{ uj_val = c; uj_type = protected_get_type_of env sigma c }
    with Not_found -> try
       let {closure;term} = Id.Map.find id lvar.ltac_uconstrs in
       let lvar = {
         ltac_constrs = closure.typed;
         ltac_uconstrs = closure.untyped;
         ltac_idents = closure.idents;
         ltac_genargs = Id.Map.empty; }
       in
       (* spiwack: I'm catching [Not_found] potentially too eagerly
          here, as the call to the main pretyping function is caught
          inside the try but I want to avoid refactoring this function
          too much for now. *)
       pretype env evdref lvar term
    with Not_found ->
        (* Check if [id] is a ltac variable not bound to a term *)
	(* and build a nice error message *)
      if Id.Map.mem id lvar.ltac_genargs then begin
        let Geninterp.Val.Dyn (typ, _) = Id.Map.find id lvar.ltac_genargs in
	user_err ?loc 
         (str "Variable " ++ Id.print id ++ str " should be bound to a term but is \
          bound to a " ++ Geninterp.Val.pr typ ++ str ".")
      end;
      (* Check if [id] is a section or goal variable *)
      try
	  { uj_val  = mkVar id; uj_type = NamedDecl.get_type (lookup_named id env) }
      with Not_found ->
	  (* [id] not found, standard error message *)
	  error_var_not_found ?loc id

(*************************************************************************)
(* Main pretyping function                                               *)

let interp_known_glob_level ?loc evd = function
  | GProp -> Univ.Level.prop
  | GSet -> Univ.Level.set
  | GType s -> interp_known_level_info ?loc evd s

let interp_glob_level ?loc evd : glob_level -> _ = function
  | GProp -> evd, Univ.Level.prop
  | GSet -> evd, Univ.Level.set
  | GType s -> interp_level_info ?loc evd s

let interp_instance ?loc evd ~len l =
  if len != List.length l then
    user_err ?loc ~hdr:"pretype"
      (str "Universe instance should have length " ++ int len)
  else
    let evd, l' =
      List.fold_left
        (fun (evd, univs) l ->
	  let evd, l = interp_glob_level ?loc evd l in
	  (evd, l :: univs)) (evd, [])
        l
    in
    if List.exists (fun l -> Univ.Level.is_prop l) l' then
      user_err ?loc ~hdr:"pretype"
	(str "Universe instances cannot contain Prop, polymorphic" ++
	   str " universe instances must be greater or equal to Set.");
    evd, Some (Univ.Instance.of_array (Array.of_list (List.rev l')))

let pretype_global ?loc rigid env evd gr us = 
  let evd, instance = 
    match us with
    | None -> evd, None
    | Some l -> 
       let _, ctx = Global.constr_of_global_in_context env.ExtraEnv.env gr in
       let len = Univ.AUContext.size ctx in
       interp_instance ?loc evd ~len l
  in
  let (sigma, c) = Evd.fresh_global ?loc ~rigid ?names:instance env.ExtraEnv.env evd gr in
  (sigma, c)

let pretype_ref ?loc evdref env ref us =
  match ref with
  | VarRef id ->
      (* Section variable *)
      (try make_judge (mkVar id) (NamedDecl.get_type (lookup_named id env))
       with Not_found ->
         (* This may happen if env is a goal env and section variables have
            been cleared - section variables should be different from goal
            variables *)
         Pretype_errors.error_var_not_found ?loc id)
  | ref ->
    let evd, c = pretype_global ?loc univ_flexible env !evdref ref us in
    let () = evdref := evd in
    let ty = unsafe_type_of env.ExtraEnv.env evd c in
      make_judge c ty

let judge_of_Type ?loc evd s =
  let evd, s = interp_universe ?loc evd s in
  let judge = 
    { uj_val = mkSort (Type s); uj_type = mkSort (Type (Univ.super s)) }
  in
    evd, judge

let pretype_sort ?loc evdref = function
  | GProp -> judge_of_prop
  | GSet -> judge_of_set
  | GType s -> evd_comb1 (judge_of_Type ?loc) evdref s

let new_type_evar env evdref loc =
  let sigma = !evdref in
  let (sigma, (e, _)) =
    Evarutil.new_type_evar env.ExtraEnv.env sigma
      univ_flexible_alg ~src:(loc,Evar_kinds.InternalHole)
  in
  evdref := sigma;
  e

module ConstrInterpObj =
struct
  type ('r, 'g, 't) obj =
    unbound_ltac_var_map -> env -> evar_map -> types -> 'g -> constr * evar_map
  let name = "constr_interp"
  let default _ = None
end

module ConstrInterp = Genarg.Register(ConstrInterpObj)

let register_constr_interp0 = ConstrInterp.register0

(* [pretype tycon env evdref lvar lmeta cstr] attempts to type [cstr] *)
(* in environment [env], with existential variables [evdref] and *)
(* the type constraint tycon *)

let rec pretype k0 resolve_tc (tycon : type_constraint) (env : ExtraEnv.t) evdref (lvar : ltac_var_map) t =
  let inh_conv_coerce_to_tycon ?loc = inh_conv_coerce_to_tycon ?loc resolve_tc in
  let pretype_type = pretype_type k0 resolve_tc in
  let pretype = pretype k0 resolve_tc in
  let open Context.Rel.Declaration in
  let loc = t.CAst.loc in
  match DAst.get t with
  | GRef (ref,u) ->
      inh_conv_coerce_to_tycon ?loc env evdref
	(pretype_ref ?loc evdref env ref u)
	tycon

  | GVar id ->
    inh_conv_coerce_to_tycon ?loc env evdref
      (pretype_id (fun e r l t -> pretype tycon e r l t) k0 loc env evdref lvar id)
      tycon

  | GEvar (id, inst) ->
      (* Ne faudrait-il pas s'assurer que hyps est bien un
	 sous-contexte du contexte courant, et qu'il n'y a pas de Rel "caché" *)
      let evk =
        try Evd.evar_key id !evdref
        with Not_found ->
          user_err ?loc  (str "Unknown existential variable.") in
      let hyps = evar_filtered_context (Evd.find !evdref evk) in
      let args = pretype_instance k0 resolve_tc env evdref lvar loc hyps evk inst in
      let c = mkEvar (evk, args) in
      let j = (Retyping.get_judgment_of env.ExtraEnv.env !evdref c) in
	inh_conv_coerce_to_tycon ?loc env evdref j tycon

  | GPatVar kind ->
    let env = ltac_interp_name_env k0 lvar env !evdref in
    let ty =
      match tycon with
      | Some ty -> ty
      | None -> new_type_evar env evdref loc in
    let k = Evar_kinds.MatchingVar kind in
      { uj_val = e_new_evar env evdref ~src:(loc,k) ty; uj_type = ty }

  | GHole (k, naming, None) ->
      let env = ltac_interp_name_env k0 lvar env !evdref in
      let ty =
        match tycon with
        | Some ty -> ty
        | None ->
          new_type_evar env evdref loc in
        { uj_val = e_new_evar env evdref ~src:(loc,k) ~naming ty; uj_type = ty }

  | GHole (k, _naming, Some arg) ->
      let env = ltac_interp_name_env k0 lvar env !evdref in
      let ty =
        match tycon with
        | Some ty -> ty
        | None ->
          new_type_evar env evdref loc in
      let open Genarg in
      let ist = lvar.ltac_genargs in
      let GenArg (Glbwit tag, arg) = arg in
      let interp = ConstrInterp.obj tag in
      let (c, sigma) = interp ist env.ExtraEnv.env !evdref ty arg in
      let () = evdref := sigma in
      { uj_val = c; uj_type = ty }

  | GRec (fixkind,names,bl,lar,vdef) ->
    let rec type_bl env ctxt = function
    [] -> ctxt
      | (na,bk,None,ty)::bl ->
        let ty' = pretype_type empty_valcon env evdref lvar ty in
	let dcl = LocalAssum (na, ty'.utj_val) in
        let dcl' = LocalAssum (ltac_interp_name lvar na,ty'.utj_val) in
	  type_bl (push_rel !evdref dcl env) (Context.Rel.add dcl' ctxt) bl
      | (na,bk,Some bd,ty)::bl ->
        let ty' = pretype_type empty_valcon env evdref lvar ty in
        let bd' = pretype (mk_tycon ty'.utj_val) env evdref lvar bd in
        let dcl = LocalDef (na, bd'.uj_val, ty'.utj_val) in
        let dcl' = LocalDef (ltac_interp_name lvar na, bd'.uj_val, ty'.utj_val) in
	  type_bl (push_rel !evdref dcl env) (Context.Rel.add dcl' ctxt) bl in
    let ctxtv = Array.map (type_bl env Context.Rel.empty) bl in
    let larj =
      Array.map2
        (fun e ar ->
          pretype_type empty_valcon (push_rel_context !evdref e env) evdref lvar ar)
        ctxtv lar in
    let lara = Array.map (fun a -> a.utj_val) larj in
    let ftys = Array.map2 (fun e a -> it_mkProd_or_LetIn a e) ctxtv lara in
    let nbfix = Array.length lar in
    let names = Array.map (fun id -> Name id) names in
    let () =
      match tycon with
      | Some t -> 
 	let fixi = match fixkind with
	  | GFix (vn,i) -> i
	  | GCoFix i -> i
        in
        begin match conv env.ExtraEnv.env !evdref ftys.(fixi) t with
          | None -> ()
          | Some sigma -> evdref := sigma
        end
      | None -> ()
    in
      (* Note: bodies are not used by push_rec_types, so [||] is safe *)
    let newenv = push_rec_types !evdref (names,ftys,[||]) env in
    let vdefj =
      Array.map2_i
	(fun i ctxt def ->
             (* we lift nbfix times the type in tycon, because of
	      * the nbfix variables pushed to newenv *)
          let (ctxt,ty) =
	    decompose_prod_n_assum !evdref (Context.Rel.length ctxt)
              (lift nbfix ftys.(i)) in
          let nenv = push_rel_context !evdref ctxt newenv in
          let j = pretype (mk_tycon ty) nenv evdref lvar def in
	    { uj_val = it_mkLambda_or_LetIn j.uj_val ctxt;
	      uj_type = it_mkProd_or_LetIn j.uj_type ctxt })
        ctxtv vdef in
      evdref := Typing.check_type_fixpoint ?loc env.ExtraEnv.env !evdref names ftys vdefj;
      let nf c = nf_evar !evdref c in
      let ftys = Array.map nf ftys in (** FIXME *)
      let fdefs = Array.map (fun x -> nf (j_val x)) vdefj in
      let fixj = match fixkind with
	| GFix (vn,i) ->
	      (* First, let's find the guard indexes. *)
	      (* If recursive argument was not given by user, we try all args.
	         An earlier approach was to look only for inductive arguments,
		 but doing it properly involves delta-reduction, and it finally
                 doesn't seem worth the effort (except for huge mutual
		 fixpoints ?) *)
	  let possible_indexes =
	    Array.to_list (Array.mapi
			     (fun i (n,_) -> match n with
			     | Some n -> [n]
			     | None -> List.map_i (fun i _ -> i) 0 ctxtv.(i))
			     vn)
	  in
	  let fixdecls = (names,ftys,fdefs) in
          let indexes =
            search_guard
              ?loc env.ExtraEnv.env possible_indexes (nf_fix !evdref fixdecls)
          in
	    make_judge (mkFix ((indexes,i),fixdecls)) ftys.(i)
	| GCoFix i ->
          let fixdecls = (names,ftys,fdefs) in
	  let cofix = (i, fixdecls) in
            (try check_cofix env.ExtraEnv.env (i, nf_fix !evdref fixdecls)
             with reraise ->
               let (e, info) = CErrors.push reraise in
               let info = Option.cata (Loc.add_loc info) info loc in
               iraise (e, info));
	    make_judge (mkCoFix cofix) ftys.(i)
      in
	inh_conv_coerce_to_tycon ?loc env evdref fixj tycon

  | GSort s ->
    let j = pretype_sort ?loc evdref s in
      inh_conv_coerce_to_tycon ?loc env evdref j tycon

  | GApp (f,args) ->
    let fj = pretype empty_tycon env evdref lvar f in
    let floc = loc_of_glob_constr f in
    let length = List.length args in
    let candargs =
	(* Bidirectional typechecking hint: 
	   parameters of a constructor are completely determined
	   by a typing constraint *)
      if Flags.is_program_mode () && length > 0 && isConstruct !evdref fj.uj_val then
	match tycon with
	| None -> []
	| Some ty ->
	  let ((ind, i), u) = destConstruct !evdref fj.uj_val in
	  let npars = inductive_nparams ind in
	    if Int.equal npars 0 then []
	    else
	      try
	  	let IndType (indf, args) = find_rectype env.ExtraEnv.env !evdref ty in
	  	let ((ind',u'),pars) = dest_ind_family indf in
	  	  if eq_ind ind ind' then List.map EConstr.of_constr pars
	  	  else (* Let the usual code throw an error *) []
	      with Not_found -> []
      else []
    in
    let app_f = 
      match EConstr.kind !evdref fj.uj_val with
      | Const (p, u) when Recordops.is_primitive_projection p ->
        let p = Option.get @@ Recordops.find_primitive_projection p in
	let p = Projection.make p false in
        let npars = Projection.npars p in
          fun n ->
	    if n == npars + 1 then fun _ v -> mkProj (p, v)
	    else fun f v -> applist (f, [v])
      | _ -> fun _ f v -> applist (f, [v])
    in
    let rec apply_rec env n resj candargs = function
      | [] -> resj
      | c::rest ->
	let argloc = loc_of_glob_constr c in
	let resj = evd_comb1 (Coercion.inh_app_fun resolve_tc env.ExtraEnv.env) evdref resj in
        let resty = whd_all env.ExtraEnv.env !evdref resj.uj_type in
      	  match EConstr.kind !evdref resty with
	  | Prod (na,c1,c2) ->
	    let tycon = Some c1 in
	    let hj = pretype tycon env evdref lvar c in
	    let candargs, ujval =
	      match candargs with
	      | [] -> [], j_val hj
	      | arg :: args -> 
                begin match conv env.ExtraEnv.env !evdref (j_val hj) arg with
                  | Some sigma -> evdref := sigma;
                    args, nf_evar !evdref (j_val hj)
                  | None ->
                    [], j_val hj
                end
	    in
            let ujval = adjust_evar_source evdref na ujval in
	    let value, typ = app_f n (j_val resj) ujval, subst1 ujval c2 in
	    let j = { uj_val = value; uj_type = typ } in
	      apply_rec env (n+1) j candargs rest
		
	  | _ ->
	    let hj = pretype empty_tycon env evdref lvar c in
	      error_cant_apply_not_functional
                ?loc:(Loc.merge_opt floc argloc) env.ExtraEnv.env !evdref
                resj [|hj|]
    in
    let resj = apply_rec env 1 fj candargs args in
    let resj =
      match EConstr.kind !evdref resj.uj_val with
      | App (f,args) ->
          if is_template_polymorphic env.ExtraEnv.env !evdref f then
	    (* Special case for inductive type applications that must be 
	       refreshed right away. *)
	    let c = mkApp (f, args) in
	    let c = evd_comb1 (Evarsolve.refresh_universes (Some true) env.ExtraEnv.env) evdref c in
	    let t = Retyping.get_type_of env.ExtraEnv.env !evdref c in
	      make_judge c (* use this for keeping evars: resj.uj_val *) t
	  else resj
      | _ -> resj 
    in
      inh_conv_coerce_to_tycon ?loc env evdref resj tycon

  | GLambda(name,bk,c1,c2)      ->
    let tycon' = evd_comb1
      (fun evd tycon ->
	match tycon with
	| None -> evd, tycon
	| Some ty ->
	  let evd, ty' = Coercion.inh_coerce_to_prod ?loc env.ExtraEnv.env evd ty in
	    evd, Some ty')
      evdref tycon
    in
    let (name',dom,rng) = evd_comb1 (split_tycon ?loc env.ExtraEnv.env) evdref tycon' in
    let dom_valcon = valcon_of_tycon dom in
    let j = pretype_type dom_valcon env evdref lvar c1 in
    (* The name specified by ltac is used also to create bindings. So
       the substitution must also be applied on variables before they are
       looked up in the rel context. *)
    let var = LocalAssum (name, j.utj_val) in
    let j' = pretype rng (push_rel !evdref var env) evdref lvar c2 in
    let name = ltac_interp_name lvar name in
    let resj = judge_of_abstraction env.ExtraEnv.env (orelse_name name name') j j' in
      inh_conv_coerce_to_tycon ?loc env evdref resj tycon

  | GProd(name,bk,c1,c2)        ->
    let j = pretype_type empty_valcon env evdref lvar c1 in
    (* The name specified by ltac is used also to create bindings. So
       the substitution must also be applied on variables before they are
       looked up in the rel context. *)
    let j' = match name with
      | Anonymous ->
        let j = pretype_type empty_valcon env evdref lvar c2 in
          { j with utj_val = lift 1 j.utj_val }
      | Name _ ->
        let var = LocalAssum (name, j.utj_val) in
        let env' = push_rel !evdref var env in
          pretype_type empty_valcon env' evdref lvar c2
    in
    let name = ltac_interp_name lvar name in
    let resj =
      try
        judge_of_product env.ExtraEnv.env name j j'
      with TypeError _ as e ->
        let (e, info) = CErrors.push e in
        let info = Option.cata (Loc.add_loc info) info loc in
        iraise (e, info) in
      inh_conv_coerce_to_tycon ?loc env evdref resj tycon

  | GLetIn(name,c1,t,c2)      ->
    let tycon1 =
      match t with
      | Some t ->
	 mk_tycon (pretype_type empty_valcon env evdref lvar t).utj_val
      | None ->
         empty_tycon in
    let j = pretype tycon1 env evdref lvar c1 in
    let t = evd_comb1 (Evarsolve.refresh_universes
      ~onlyalg:true ~status:Evd.univ_flexible (Some false) env.ExtraEnv.env)
      evdref j.uj_type in
    (* The name specified by ltac is used also to create bindings. So
       the substitution must also be applied on variables before they are
       looked up in the rel context. *)
    let var = LocalDef (name, j.uj_val, t) in
    let tycon = lift_tycon 1 tycon in
    let j' = pretype tycon (push_rel !evdref var env) evdref lvar c2 in
    let name = ltac_interp_name lvar name in
      { uj_val = mkLetIn (name, j.uj_val, t, j'.uj_val) ;
	uj_type = subst1 j.uj_val j'.uj_type }

  | GLetTuple (nal,(na,po),c,d) ->
    let cj = pretype empty_tycon env evdref lvar c in
    let (IndType (indf,realargs)) =
      try find_rectype env.ExtraEnv.env !evdref cj.uj_type
      with Not_found ->
	let cloc = loc_of_glob_constr c in
	  error_case_not_inductive ?loc:cloc env.ExtraEnv.env !evdref cj
    in
    let ind = fst (fst (dest_ind_family indf)) in
    let cstrs = get_constructors env.ExtraEnv.env indf in
    if not (Int.equal (Array.length cstrs) 1) then
      user_err ?loc  (str "Destructing let is only for inductive types" ++
	str " with one constructor.");
    let cs = cstrs.(0) in
    if not (Int.equal (List.length nal) cs.cs_nargs) then
      user_err ?loc:loc (str "Destructing let on this type expects " ++ 
	int cs.cs_nargs ++ str " variables.");
    let fsign, record = 
      let set_name na d = set_name na (map_rel_decl EConstr.of_constr d) in
      match Environ.get_projections env.ExtraEnv.env ind with
      | None ->
	 List.map2 set_name (List.rev nal) cs.cs_args, false
      | Some ps ->
	let rec aux n k names l =
	  match names, l with
	  | na :: names, (LocalAssum (_,t) :: l) ->
            let t = EConstr.of_constr t in
	    let proj = Projection.make ps.(cs.cs_nargs - k) true in
	    LocalDef (na, lift (cs.cs_nargs - n) (mkProj (proj, cj.uj_val)), t)
	    :: aux (n+1) (k + 1) names l
	  | na :: names, (decl :: l) ->
	    set_name na decl :: aux (n+1) k names l
	  | [], [] -> []
	  | _ -> assert false
	in aux 1 1 (List.rev nal) cs.cs_args, true in
    let fsign = Context.Rel.map (whd_betaiota !evdref) fsign in
    let obj ind p v f =
      if not record then 
        let nal = List.map (fun na -> ltac_interp_name lvar na) nal in
        let nal = List.rev nal in
        let fsign = List.map2 set_name nal fsign in
	let f = it_mkLambda_or_LetIn f fsign in
	let ci = make_case_info env.ExtraEnv.env (fst ind) LetStyle in
	  mkCase (ci, p, cj.uj_val,[|f|]) 
      else it_mkLambda_or_LetIn f fsign
    in
    let env_f = push_rel_context !evdref fsign env in
      (* Make dependencies from arity signature impossible *)
    let arsgn =
      let arsgn,_ = get_arity env.ExtraEnv.env indf in
      List.map (set_name Anonymous) arsgn
    in
      let indt = build_dependent_inductive env.ExtraEnv.env indf in
      let psign = LocalAssum (na, indt) :: arsgn in (* For locating names in [po] *)
      let predlvar = Cases.make_return_predicate_ltac_lvar !evdref na c cj.uj_val lvar in
      let psign' = LocalAssum (ltac_interp_name predlvar na, indt) :: arsgn in
      let psign' = List.map (fun d -> map_rel_decl EConstr.of_constr d) psign' in
      let psign' = Namegen.name_context env.ExtraEnv.env !evdref psign' in (* For naming abstractions in [po] *)
      let psign = List.map (fun d -> map_rel_decl EConstr.of_constr d) psign in
      let nar = List.length arsgn in
	  (match po with
	  | Some p ->
	    let env_p = push_rel_context !evdref psign env in
	    let pj = pretype_type empty_valcon env_p evdref predlvar p in
	    let ccl = nf_evar !evdref pj.utj_val in
	    let p = it_mkLambda_or_LetIn ccl psign' in
	    let inst =
	      (Array.map_to_list EConstr.of_constr cs.cs_concl_realargs)
	      @[EConstr.of_constr (build_dependent_constructor cs)] in
	    let lp = lift cs.cs_nargs p in
	    let fty = hnf_lam_applist env.ExtraEnv.env !evdref lp inst in
	    let fj = pretype (mk_tycon fty) env_f evdref lvar d in
	    let v =
	      let ind,_ = dest_ind_family indf in
		Typing.check_allowed_sort env.ExtraEnv.env !evdref ind cj.uj_val p;
		obj ind p cj.uj_val fj.uj_val
	    in
	      { uj_val = v; uj_type = (substl (realargs@[cj.uj_val]) ccl) }

	  | None ->
	    let tycon = lift_tycon cs.cs_nargs tycon in
	    let fj = pretype tycon env_f evdref predlvar d in
	    let ccl = nf_evar !evdref fj.uj_type in
	    let ccl =
	      if noccur_between !evdref 1 cs.cs_nargs ccl then
		lift (- cs.cs_nargs) ccl
	      else
		error_cant_find_case_type ?loc env.ExtraEnv.env !evdref
		  cj.uj_val in
		 (* let ccl = refresh_universes ccl in *)
	    let p = it_mkLambda_or_LetIn (lift (nar+1) ccl) psign' in
	    let v =
	      let ind,_ = dest_ind_family indf in
		Typing.check_allowed_sort env.ExtraEnv.env !evdref ind cj.uj_val p;
		obj ind p cj.uj_val fj.uj_val
	    in { uj_val = v; uj_type = ccl })

  | GIf (c,(na,po),b1,b2) ->
    let cj = pretype empty_tycon env evdref lvar c in
    let (IndType (indf,realargs)) =
      try find_rectype env.ExtraEnv.env !evdref cj.uj_type
      with Not_found ->
	let cloc = loc_of_glob_constr c in
	  error_case_not_inductive ?loc:cloc env.ExtraEnv.env !evdref cj in
    let cstrs = get_constructors env.ExtraEnv.env indf in
      if not (Int.equal (Array.length cstrs) 2) then
        user_err ?loc 
		      (str "If is only for inductive types with two constructors.");

      let arsgn =
	let arsgn,_ = get_arity env.ExtraEnv.env indf in
        (* Make dependencies from arity signature impossible *)
        List.map (set_name Anonymous) arsgn
      in
      let nar = List.length arsgn in
      let indt = build_dependent_inductive env.ExtraEnv.env indf in
      let psign = LocalAssum (na, indt) :: arsgn in (* For locating names in [po] *)
      let predlvar = Cases.make_return_predicate_ltac_lvar !evdref na c cj.uj_val lvar in
      let psign' = LocalAssum (ltac_interp_name predlvar na, indt) :: arsgn in
      let psign' = List.map (fun d -> map_rel_decl EConstr.of_constr d) psign' in
      let psign' = Namegen.name_context env.ExtraEnv.env !evdref psign' in (* For naming abstractions in [po] *)
      let psign = List.map (fun d -> map_rel_decl EConstr.of_constr d) psign in
      let pred,p = match po with
	| Some p ->
	  let env_p = push_rel_context !evdref psign env in
	  let pj = pretype_type empty_valcon env_p evdref predlvar p in
	  let ccl = nf_evar !evdref pj.utj_val in
	  let pred = it_mkLambda_or_LetIn ccl psign' in
	  let typ = lift (- nar) (beta_applist !evdref (pred,[cj.uj_val])) in
	    pred, typ
	| None ->
	  let p = match tycon with
	    | Some ty -> ty
	    | None ->
              let env = ltac_interp_name_env k0 lvar env !evdref in
              new_type_evar env evdref loc
	  in
	    it_mkLambda_or_LetIn (lift (nar+1) p) psign', p in
      let pred = nf_evar !evdref pred in
      let p = nf_evar !evdref p in
      let f cs b =
	let n = Context.Rel.length cs.cs_args in
	let pi = lift n pred in (* liftn n 2 pred ? *)
	let pi = beta_applist !evdref (pi, [EConstr.of_constr (build_dependent_constructor cs)]) in
        let cs_args = List.map (fun d -> map_rel_decl EConstr.of_constr d) cs.cs_args in
        let cs_args = Context.Rel.map (whd_betaiota !evdref) cs_args in
	let csgn =
          List.map (set_name Anonymous) cs_args
        in
	let env_c = push_rel_context !evdref csgn env in
	let bj = pretype (mk_tycon pi) env_c evdref lvar b in
	  it_mkLambda_or_LetIn bj.uj_val cs_args in
      let b1 = f cstrs.(0) b1 in
      let b2 = f cstrs.(1) b2 in
      let v =
	let ind,_ = dest_ind_family indf in
	let ci = make_case_info env.ExtraEnv.env (fst ind) IfStyle in
	let pred = nf_evar !evdref pred in
	  Typing.check_allowed_sort env.ExtraEnv.env !evdref ind cj.uj_val pred;
	  mkCase (ci, pred, cj.uj_val, [|b1;b2|])
      in
      let cj = { uj_val = v; uj_type = p } in
      inh_conv_coerce_to_tycon ?loc env evdref cj tycon

  | GCases (sty,po,tml,eqns) ->
    Cases.compile_cases ?loc sty
      ((fun vtyc env evdref -> pretype vtyc (make_env env !evdref) evdref),evdref)
      tycon env.ExtraEnv.env (* loc *) lvar (po,tml,eqns)

  | GCast (c,k) ->
    let cj =
      match k with
      | CastCoerce ->
	let cj = pretype empty_tycon env evdref lvar c in
	  evd_comb1 (Coercion.inh_coerce_to_base ?loc env.ExtraEnv.env) evdref cj
      | CastConv t | CastVM t | CastNative t ->
	let k = (match k with CastVM _ -> VMcast | CastNative _ -> NATIVEcast | _ -> DEFAULTcast) in
	let tj = pretype_type empty_valcon env evdref lvar t in
        let tval = evd_comb1 (Evarsolve.refresh_universes
                             ~onlyalg:true ~status:Evd.univ_flexible (Some false) env.ExtraEnv.env)
                          evdref tj.utj_val in
	let tval = nf_evar !evdref tval in
	let cj, tval = match k with
	  | VMcast ->
 	    let cj = pretype empty_tycon env evdref lvar c in
	    let cty = nf_evar !evdref cj.uj_type and tval = nf_evar !evdref tval in
	      if not (occur_existential !evdref cty || occur_existential !evdref tval) then
                match Reductionops.vm_infer_conv env.ExtraEnv.env !evdref cty tval with
                | Some evd -> (evdref := evd; cj, tval)
                | None ->
		  error_actual_type ?loc env.ExtraEnv.env !evdref cj tval 
                      (ConversionFailed (env.ExtraEnv.env,cty,tval))
	      else user_err ?loc  (str "Cannot check cast with vm: " ++
		str "unresolved arguments remain.")
	  | NATIVEcast ->
 	    let cj = pretype empty_tycon env evdref lvar c in
	    let cty = nf_evar !evdref cj.uj_type and tval = nf_evar !evdref tval in
            begin
              match Nativenorm.native_infer_conv env.ExtraEnv.env !evdref cty tval with
              | Some evd -> (evdref := evd; cj, tval)
              | None ->
                error_actual_type ?loc env.ExtraEnv.env !evdref cj tval
                  (ConversionFailed (env.ExtraEnv.env,cty,tval))
            end
	  | _ -> 
 	    pretype (mk_tycon tval) env evdref lvar c, tval
	in
	let v = mkCast (cj.uj_val, k, tval) in
	  { uj_val = v; uj_type = tval }
    in inh_conv_coerce_to_tycon ?loc env evdref cj tycon

and pretype_instance k0 resolve_tc env evdref lvar loc hyps evk update =
  let f decl (subst,update) =
    let id = NamedDecl.get_id decl in
    let t = replace_vars subst (NamedDecl.get_type decl) in
    let c, update =
      try
        let c = List.assoc id update in
        let c = pretype k0 resolve_tc (mk_tycon t) env evdref lvar c in
        c.uj_val, List.remove_assoc id update
      with Not_found ->
      try
        let (n,_,t') = lookup_rel_id id (rel_context env) in
        if is_conv env.ExtraEnv.env !evdref t (lift n t') then mkRel n, update else raise Not_found
      with Not_found ->
      try
        let t' = env |> lookup_named id |> NamedDecl.get_type in
        if is_conv env.ExtraEnv.env !evdref t t' then mkVar id, update else raise Not_found
      with Not_found ->
        user_err ?loc  (str "Cannot interpret " ++
          pr_existential_key !evdref evk ++
          str " in current context: no binding for " ++ Id.print id ++ str ".") in
    ((id,c)::subst, update) in
  let subst,inst = List.fold_right f hyps ([],update) in
  check_instance loc subst inst;
  Array.map_of_list snd subst

(* [pretype_type valcon env evdref lvar c] coerces [c] into a type *)
and pretype_type k0 resolve_tc valcon (env : ExtraEnv.t) evdref lvar c = match DAst.get c with
  | GHole (knd, naming, None) ->
      let loc = loc_of_glob_constr c in
      (match valcon with
       | Some v ->
           let s =
	     let sigma =  !evdref in
	     let t = Retyping.get_type_of env.ExtraEnv.env sigma v in
	       match EConstr.kind sigma (whd_all env.ExtraEnv.env sigma t) with
               | Sort s -> ESorts.kind sigma s
               | Evar ev when is_Type sigma (existential_type sigma ev) ->
		   evd_comb1 (define_evar_as_sort env.ExtraEnv.env) evdref ev
               | _ -> anomaly (Pp.str "Found a type constraint which is not a type.")
           in
           (* Correction of bug #5315 : we need to define an evar for *all* holes *)
           let evkt = e_new_evar env evdref ~src:(loc, knd) ~naming (mkSort s) in
           let ev,_ = destEvar !evdref evkt in
           evdref := Evd.define ev (nf_evar !evdref v) !evdref;
           (* End of correction of bug #5315 *)
           { utj_val = v;
	     utj_type = s }
       | None ->
           let env = ltac_interp_name_env k0 lvar env !evdref in
	   let s = evd_comb0 (new_sort_variable univ_flexible_alg) evdref in
	     { utj_val = e_new_evar env evdref ~src:(loc, knd) ~naming (mkSort s);
	       utj_type = s})
  | _ ->
      let j = pretype k0 resolve_tc empty_tycon env evdref lvar c in
      let loc = loc_of_glob_constr c in
      let tj = evd_comb1 (Coercion.inh_coerce_to_sort ?loc env.ExtraEnv.env) evdref j in
	match valcon with
	| None -> tj
	| Some v ->
          begin match cumul env.ExtraEnv.env !evdref v tj.utj_val with
            | Some sigma -> evdref := sigma; tj
            | None ->
	      error_unexpected_type
                ?loc:(loc_of_glob_constr c) env.ExtraEnv.env !evdref tj.utj_val v
          end

let ise_pretype_gen flags env sigma lvar kind c =
  let env = make_env env sigma in
  let evdref = ref sigma in
  let k0 = Context.Rel.length (rel_context env) in
  let c', c'_ty = match kind with
    | WithoutTypeConstraint ->
        let j = pretype k0 flags.use_typeclasses empty_tycon env evdref lvar c in
        j.uj_val, j.uj_type
    | OfType exptyp ->
        let j = pretype k0 flags.use_typeclasses (mk_tycon exptyp) env evdref lvar c in
        j.uj_val, j.uj_type
    | IsType ->
        let tj = pretype_type k0 flags.use_typeclasses empty_valcon env evdref lvar c in
        tj.utj_val, mkSort tj.utj_type
  in
  process_inference_flags flags env.ExtraEnv.env sigma (!evdref,c',c'_ty)

let default_inference_flags fail = {
  use_typeclasses = true;
  solve_unification_constraints = true;
  use_hook = None;
  fail_evar = fail;
  expand_evars = true }

let no_classes_no_fail_inference_flags = {
  use_typeclasses = false;
  solve_unification_constraints = true;
  use_hook = None;
  fail_evar = false;
  expand_evars = true }

let all_and_fail_flags = default_inference_flags true
let all_no_fail_flags = default_inference_flags false

let ise_pretype_gen_ctx flags env sigma lvar kind c =
  let evd, c, _ = ise_pretype_gen flags env sigma lvar kind c in
  c, Evd.evar_universe_context evd

(** Entry points of the high-level type synthesis algorithm *)

let understand
    ?(flags=all_and_fail_flags)
    ?(expected_type=WithoutTypeConstraint)
    env sigma c =
  ise_pretype_gen_ctx flags env sigma empty_lvar expected_type c

let understand_tcc_ty ?(flags=all_no_fail_flags) env sigma ?(expected_type=WithoutTypeConstraint) c =
  ise_pretype_gen flags env sigma empty_lvar expected_type c

let understand_tcc ?flags env sigma ?expected_type c =
  let sigma, c, _ = understand_tcc_ty ?flags env sigma ?expected_type c in
  sigma, c

let understand_ltac flags env sigma lvar kind c =
  let (sigma, c, _) = ise_pretype_gen flags env sigma lvar kind c in
  (sigma, c)

let pretype k0 resolve_tc typcon env evdref lvar t =
  pretype k0 resolve_tc typcon (make_env env !evdref) evdref lvar t

let pretype_type k0 resolve_tc valcon env evdref lvar t =
  pretype_type k0 resolve_tc valcon (make_env env !evdref) evdref lvar t
