(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
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
open Term
open Termops
open EConstr
open Vars
open Reductionops
open Environ
open Type_errors
open Typeops
open Typing
open Globnames
open Nameops
open Evarutil
open Evardefine
open Pretype_errors
open Glob_term
open Glob_ops
open Evarconv
open Pattern
open Misctypes
open Tactypes
open Sigma.Notations

module NamedDecl = Context.Named.Declaration

type typing_constraint = OfType of types | IsType | WithoutTypeConstraint
type var_map = constr_under_binders Id.Map.t
type uconstr_var_map = Glob_term.closed_glob_constr Id.Map.t
type unbound_ltac_var_map = Geninterp.Val.t Id.Map.t
type ltac_var_map = {
  ltac_constrs : var_map;
  ltac_uconstrs : uconstr_var_map;
  ltac_idents: Id.t Id.Map.t;
  ltac_genargs : unbound_ltac_var_map;
}
type glob_constr_ltac_closure = ltac_var_map * glob_constr
type pure_open_constr = evar_map * Constr.constr

(************************************************************************)
(* This concerns Cases *)
open Inductive
open Inductiveops

(************************************************************************)

let local_assum (na, t) =
  let open Context.Rel.Declaration in
  let inj = EConstr.Unsafe.to_constr in
  LocalAssum (na, inj t)

let local_def (na, b, t) =
  let open Context.Rel.Declaration in
  let inj = EConstr.Unsafe.to_constr in
  LocalDef (na, inj b, inj t)

module ExtraEnv =
struct

type t = {
  env : Environ.env;
  extra : Evarutil.ext_named_context Lazy.t;
  (** Delay the computation of the evar extended environment *)
}

let get_extra env =
  let open Context.Named.Declaration in
  let ids = List.map get_id (named_context env) in
  let avoid = List.fold_right Id.Set.add ids Id.Set.empty in
  Context.Rel.fold_outside push_rel_decl_to_named_context
    (Environ.rel_context env) ~init:(empty_csubst, [], avoid, named_context env)

let make_env env = { env = env; extra = lazy (get_extra env) }
let rel_context env = rel_context env.env

let push_rel d env = {
  env = push_rel d env.env;
  extra = lazy (push_rel_decl_to_named_context d (Lazy.force env.extra));
}

let pop_rel_context n env = make_env (pop_rel_context n env.env)

let push_rel_context ctx env = {
  env = push_rel_context ctx env.env;
  extra = lazy (List.fold_right push_rel_decl_to_named_context ctx (Lazy.force env.extra));
}

let lookup_named id env = lookup_named id env.env

let e_new_evar env evdref ?src ?naming typ =
  let subst2 subst vsubst c = csubst_subst subst (replace_vars vsubst c) in
  let open Context.Named.Declaration in
  let inst_vars = List.map (get_id %> EConstr.mkVar) (named_context env.env) in
  let inst_rels = List.rev (rel_list 0 (nb_rel env.env)) in
  let (subst, vsubst, _, nc) = Lazy.force env.extra in
  let typ' = subst2 subst vsubst typ in
  let instance = inst_rels @ inst_vars in
  let sign = val_of_named_context nc in
  let sigma = Sigma.Unsafe.of_evar_map !evdref in
  let Sigma (e, sigma, _) = new_evar_instance sign sigma typ' ?src ?naming instance in
  evdref := Sigma.to_evar_map sigma;
  e

let push_rec_types (lna,typarray,_) env =
  let ctxt = Array.map2_i (fun i na t -> local_assum (na, lift i t)) lna typarray in
  Array.fold_left (fun e assum -> push_rel assum e) env ctxt

end

open ExtraEnv

(* An auxiliary function for searching for fixpoint guard indexes *)

exception Found of int array

let nf_fix sigma (nas, cs, ts) =
  let inj c = EConstr.to_constr sigma c in
  (nas, Array.map inj cs, Array.map inj ts)

let nf_evar sigma c =
  EConstr.of_constr (nf_evar sigma (EConstr.Unsafe.to_constr c))

let search_guard loc env possible_indexes fixdefs =
  (* Standard situation with only one possibility for each fix. *)
  (* We treat it separately in order to get proper error msg. *)
  let is_singleton = function [_] -> true | _ -> false in
  if List.for_all is_singleton possible_indexes then
    let indexes = Array.of_list (List.map List.hd possible_indexes) in
    let fix = ((indexes, 0),fixdefs) in
    (try check_fix env fix
     with reraise ->
       let (e, info) = CErrors.push reraise in
       let info = Loc.add_loc info loc in
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
	 user_err ~loc ~hdr:"search_guard" (Pp.str errmsg)
     with Found indexes -> indexes)

(* To force universe name declaration before use *)

let strict_universe_declarations = ref true
let is_strict_universe_declarations () = !strict_universe_declarations

let _ =
  Goptions.(declare_bool_option
	  { optsync  = true;
            optdepr  = false;
	    optname  = "strict universe declaration";
	    optkey   = ["Strict";"Universe";"Declaration"];
	    optread  = is_strict_universe_declarations;
	    optwrite = (:=) strict_universe_declarations })

let _ =
  Goptions.(declare_bool_option
	  { optsync  = true;
            optdepr  = false;
	    optname  = "minimization to Set";
	    optkey   = ["Universe";"Minimization";"ToSet"];
	    optread  = Universes.is_set_minimization;
	    optwrite = (:=) Universes.set_minimization })
						  
(** Miscellaneous interpretation functions *)
let interp_universe_level_name evd (loc,s) =
  let names, _ = Global.global_universe_names () in
    if CString.string_contains s "." then
      match List.rev (CString.split '.' s) with
      | [] -> anomaly (str"Invalid universe name " ++ str s)
      | n :: dp -> 
	 let num = int_of_string n in
	 let dp = DirPath.make (List.map Id.of_string dp) in
	 let level = Univ.Level.make dp num in
	 let evd =
	   try Evd.add_global_univ evd level
	   with UGraph.AlreadyDeclared -> evd
	 in evd, level
    else 
      try
	let level = Evd.universe_of_name evd s in
	evd, level
      with Not_found ->
	try 
	  let id = try Id.of_string s with _ -> raise Not_found in
          evd, snd (Idmap.find id names)
	with Not_found -> 
	  if not (is_strict_universe_declarations ()) then
  	    new_univ_level_variable ~loc ~name:s univ_rigid evd
	  else user_err ~loc ~hdr:"interp_universe_level_name"
			     (Pp.(str "Undeclared universe: " ++ str s))

let interp_universe ?loc evd = function
  | [] -> let evd, l = new_univ_level_variable ?loc univ_rigid evd in
	    evd, Univ.Universe.make l
  | l ->
    List.fold_left (fun (evd, u) l -> 
      let evd', l = interp_universe_level_name evd l in
	(evd', Univ.sup u (Univ.Universe.make l)))
    (evd, Univ.Universe.type0m) l

let interp_universe_level loc evd = function
  | None -> new_univ_level_variable ~loc univ_rigid evd
  | Some (loc,s) -> interp_universe_level_name evd (loc,s)

let interp_sort ?loc evd = function
  | GProp -> evd, Prop Null
  | GSet -> evd, Prop Pos
  | GType n -> 
    let evd, u = interp_universe ?loc evd n in
      evd, Type u

let interp_elimination_sort = function
  | GProp -> InProp
  | GSet  -> InSet
  | GType _ -> InType

type inference_hook = env -> evar_map -> evar -> evar_map * constr

type inference_flags = {
  use_typeclasses : bool;
  use_unif_heuristics : bool;
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

let frozen_and_pending_holes (sigma, sigma') =
  let add_derivative_of evk evi acc =
    match advance sigma' evk with None -> acc | Some evk' -> Evar.Set.add evk' acc in
  let frozen = Evd.fold_undefined add_derivative_of sigma Evar.Set.empty in
  let fold evk _ accu = if not (Evar.Set.mem evk frozen) then Evar.Set.add evk accu else accu in
  let pending = Evd.fold_undefined fold sigma' Evar.Set.empty in
  (frozen,pending)

let apply_typeclasses env evdref frozen fail_evar =
  let filter_frozen evk = Evar.Set.mem evk frozen in
  evdref := Typeclasses.resolve_typeclasses
     ~filter:(if Flags.is_program_mode () 
	      then (fun evk evi -> Typeclasses.no_goals_or_obligations evk evi && not (filter_frozen evk))
              else (fun evk evi -> Typeclasses.no_goals evk evi && not (filter_frozen evk)))
     ~split:true ~fail:fail_evar env !evdref;
  if Flags.is_program_mode () then (* Try optionally solving the obligations *)
    evdref := Typeclasses.resolve_typeclasses
      ~filter:(fun evk evi -> Typeclasses.all_evars evk evi && not (filter_frozen evk)) ~split:true ~fail:false env !evdref

let apply_inference_hook hook evdref pending =
  evdref := Evar.Set.fold (fun evk sigma ->
    if Evd.is_undefined sigma evk (* in particular not defined by side-effect *)
    then
      try
        let sigma, c = hook sigma evk in
        Evd.define evk (EConstr.Unsafe.to_constr c) sigma
      with Exit ->
        sigma
    else
      sigma) pending !evdref

let apply_heuristics env evdref fail_evar =
  (* Resolve eagerly, potentially making wrong choices *)
  try evdref := consider_remaining_unif_problems
	~ts:(Typeclasses.classes_transparent_state ()) env !evdref
  with e when CErrors.noncritical e ->
    let e = CErrors.push e in if fail_evar then iraise e

let check_typeclasses_instances_are_solved env current_sigma frozen =
  (* Naive way, call resolution again with failure flag *)
  apply_typeclasses env (ref current_sigma) frozen true

let check_extra_evars_are_solved env current_sigma pending =
  Evar.Set.iter
    (fun evk ->
      if not (Evd.is_defined current_sigma evk) then
        let (loc,k) = evar_source evk current_sigma in
	match k with
	| Evar_kinds.ImplicitArg (gr, (i, id), false) -> ()
	| _ ->
	    error_unsolvable_implicit ~loc env current_sigma evk None) pending

(* [check_evars] fails if some unresolved evar remains *)

let check_evars env initial_sigma sigma c =
  let rec proc_rec c =
    match EConstr.kind sigma c with
    | Evar (evk, _) ->
      if not (Evd.mem initial_sigma evk) then
        let (loc,k) = evar_source evk sigma in
        begin match k with
          | Evar_kinds.ImplicitArg (gr, (i, id), false) -> ()
          | _ -> Pretype_errors.error_unsolvable_implicit ~loc env sigma evk None
        end
    | _ -> EConstr.iter sigma proc_rec c
  in proc_rec c

let check_evars_are_solved env current_sigma frozen pending =
  check_typeclasses_instances_are_solved env current_sigma frozen;
  check_problems_are_solved env current_sigma;
  check_extra_evars_are_solved env current_sigma pending

(* Try typeclasses, hooks, unification heuristics ... *)

let solve_remaining_evars flags env current_sigma pending =
  let frozen,pending = frozen_and_pending_holes pending in
  let evdref = ref current_sigma in
  if flags.use_typeclasses then apply_typeclasses env evdref frozen false;
  if Option.has_some flags.use_hook then
    apply_inference_hook (Option.get flags.use_hook env) evdref pending;
  if flags.use_unif_heuristics then apply_heuristics env evdref false;
  if flags.fail_evar then check_evars_are_solved env !evdref frozen pending;
  !evdref

let check_evars_are_solved env current_sigma pending =
  let frozen,pending = frozen_and_pending_holes pending in
  check_evars_are_solved env current_sigma frozen pending

let process_inference_flags flags env initial_sigma (sigma,c) =
  let sigma = solve_remaining_evars flags env sigma (initial_sigma, sigma) in
  let c = if flags.expand_evars then nf_evar sigma c else c in
  sigma,c

(* Allow references to syntactically nonexistent variables (i.e., if applied on an inductive) *)
let allow_anonymous_refs = ref false

(* coerce to tycon if any *)
let inh_conv_coerce_to_tycon resolve_tc loc env evdref j = function
  | None -> j
  | Some t ->
      evd_comb2 (Coercion.inh_conv_coerce_to resolve_tc loc env.ExtraEnv.env) evdref j t

let check_instance loc subst = function
  | [] -> ()
  | (id,_) :: _ ->
      if List.mem_assoc id subst then
        user_err ~loc  (pr_id id ++ str "appears more than once.")
      else
        user_err ~loc  (str "No such variable in the signature of the existential variable: " ++ pr_id id ++ str ".")

(* used to enforce a name in Lambda when the type constraints itself
   is named, hence possibly dependent *)

let orelse_name name name' = match name with
  | Anonymous -> name'
  | _ -> name

let ltac_interp_name { ltac_idents ; ltac_genargs } = function
  | Anonymous -> Anonymous
  | Name id as n ->
      try Name (Id.Map.find id ltac_idents)
      with Not_found ->
        if Id.Map.mem id ltac_genargs then
          user_err  (str"Ltac variable"++spc()++ pr_id id ++
                           spc()++str"is not bound to an identifier."++spc()++
                           str"It cannot be used in a binder.")
        else n

let ltac_interp_name_env k0 lvar env =
  (* envhd is the initial part of the env when pretype was called first *)
  (* (in practice is is probably 0, but we have to grant the
     specification of pretype which accepts to start with a non empty
     rel_context) *)
  (* tail is the part of the env enriched by pretyping *)
  let n = Context.Rel.length (rel_context env) - k0 in
  let ctxt,_ = List.chop n (rel_context env) in
  let open Context.Rel.Declaration in
  let ctxt' = List.smartmap (map_name (ltac_interp_name lvar)) ctxt in
  if List.equal (fun d1 d2 -> Name.equal (get_name d1) (get_name d2)) ctxt ctxt' then env
  else push_rel_context ctxt' (pop_rel_context n env)

let invert_ltac_bound_name lvar env id0 id =
  let id' = Id.Map.find id lvar.ltac_idents in
  try mkRel (pi1 (lookup_rel_id id' (rel_context env)))
  with Not_found ->
    user_err  (str "Ltac variable " ++ pr_id id0 ++
		       str " depends on pattern variable name " ++ pr_id id ++
		       str " which is not bound in current context.")

let protected_get_type_of env sigma c =
  try EConstr.of_constr (Retyping.get_type_of ~lax:true env.ExtraEnv.env sigma c)
  with Retyping.RetypeError _ ->
    user_err 
      (str "Cannot reinterpret " ++ quote (print_constr (EConstr.Unsafe.to_constr c)) ++
       str " in the current environment.")

let pretype_id pretype k0 loc env evdref lvar id =
  let sigma = !evdref in
  (* Look for the binder of [id] *)
  try
    let (n,_,typ) = lookup_rel_id id (rel_context env) in
    let typ = EConstr.of_constr typ in
      { uj_val  = mkRel n; uj_type = lift n typ }
  with Not_found ->
    let env = ltac_interp_name_env k0 lvar env in
    (* Check if [id] is an ltac variable *)
    try
      let (ids,c) = Id.Map.find id lvar.ltac_constrs in
      let subst = List.map (invert_ltac_bound_name lvar env id) ids in
      let c = substl subst (EConstr.of_constr c) in
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
	user_err ~loc 
         (str "Variable " ++ pr_id id ++ str " should be bound to a term but is \
          bound to a " ++ Geninterp.Val.pr typ ++ str ".")
      end;
      (* Check if [id] is a section or goal variable *)
      try
	  { uj_val  = mkVar id; uj_type = EConstr.of_constr (NamedDecl.get_type (lookup_named id env)) }
      with Not_found ->
	  (* [id] not found, standard error message *)
	  error_var_not_found ~loc id

(*************************************************************************)
(* Main pretyping function                                               *)

let interp_universe_level_name loc evd l =
  match l with
  | GProp -> evd, Univ.Level.prop
  | GSet -> evd, Univ.Level.set
  | GType s -> interp_universe_level loc evd s

let pretype_global loc rigid env evd gr us = 
  let evd, instance = 
    match us with
    | None -> evd, None
    | Some l -> 
       let _, ctx = Universes.unsafe_constr_of_global gr in
       let arr = Univ.Instance.to_array (Univ.UContext.instance ctx) in
       let len = Array.length arr in
       if len != List.length l then
	 user_err ~loc ~hdr:"pretype"
		       (str "Universe instance should have length " ++ int len)
       else
	 let evd, l' = List.fold_left (fun (evd, univs) l -> 
	    let evd, l = interp_universe_level_name loc evd l in
	      (evd, l :: univs)) (evd, []) l
	 in
	 if List.exists (fun l -> Univ.Level.is_prop l) l' then
	   user_err ~loc ~hdr:"pretype"
		 (str "Universe instances cannot contain Prop, polymorphic" ++
		   str " universe instances must be greater or equal to Set.");
	 evd, Some (Univ.Instance.of_array (Array.of_list (List.rev l')))
  in
  let (sigma, c) = Evd.fresh_global ~loc ~rigid ?names:instance env.ExtraEnv.env evd gr in
  (sigma, EConstr.of_constr c)

let pretype_ref loc evdref env ref us =
  match ref with
  | VarRef id ->
      (* Section variable *)
      (try make_judge (mkVar id) (EConstr.of_constr (NamedDecl.get_type (lookup_named id env)))
       with Not_found ->
         (* This may happen if env is a goal env and section variables have
            been cleared - section variables should be different from goal
            variables *)
         Pretype_errors.error_var_not_found ~loc id)
  | ref ->
    let evd, c = pretype_global loc univ_flexible env !evdref ref us in
    let () = evdref := evd in
    let ty = unsafe_type_of env.ExtraEnv.env evd c in
    let ty = EConstr.of_constr ty in
      make_judge c ty

let judge_of_Type loc evd s =
  let evd, s = interp_universe ~loc evd s in
  let judge = 
    { uj_val = mkSort (Type s); uj_type = mkSort (Type (Univ.super s)) }
  in
    evd, judge

let pretype_sort loc evdref = function
  | GProp -> judge_of_prop
  | GSet -> judge_of_set
  | GType s -> evd_comb1 (judge_of_Type loc) evdref s

let new_type_evar env evdref loc =
  let sigma = Sigma.Unsafe.of_evar_map !evdref in
  let Sigma ((e, _), sigma, _) =
    Evarutil.new_type_evar env.ExtraEnv.env sigma
      univ_flexible_alg ~src:(loc,Evar_kinds.InternalHole)
  in
  evdref := Sigma.to_evar_map sigma;
  e

let (f_genarg_interp, genarg_interp_hook) = Hook.make ()

(* [pretype tycon env evdref lvar lmeta cstr] attempts to type [cstr] *)
(* in environment [env], with existential variables [evdref] and *)
(* the type constraint tycon *)

let rec pretype k0 resolve_tc (tycon : type_constraint) (env : ExtraEnv.t) evdref (lvar : ltac_var_map) t =
  let inh_conv_coerce_to_tycon = inh_conv_coerce_to_tycon resolve_tc in
  let pretype_type = pretype_type k0 resolve_tc in
  let pretype = pretype k0 resolve_tc in
  let open Context.Rel.Declaration in
  match t with
  | GRef (loc,ref,u) ->
      inh_conv_coerce_to_tycon loc env evdref
	(pretype_ref loc evdref env ref u)
	tycon

  | GVar (loc, id) ->
    inh_conv_coerce_to_tycon loc env evdref
      (pretype_id (fun e r l t -> pretype tycon e r l t) k0 loc env evdref lvar id)
      tycon

  | GEvar (loc, id, inst) ->
      (* Ne faudrait-il pas s'assurer que hyps est bien un
	 sous-contexte du contexte courant, et qu'il n'y a pas de Rel "caché" *)
      let evk =
        try Evd.evar_key id !evdref
        with Not_found ->
          user_err ~loc  (str "Unknown existential variable.") in
      let hyps = evar_filtered_context (Evd.find !evdref evk) in
      let args = pretype_instance k0 resolve_tc env evdref lvar loc hyps evk inst in
      let c = mkEvar (evk, args) in
      let j = (Retyping.get_judgment_of env.ExtraEnv.env !evdref c) in
	inh_conv_coerce_to_tycon loc env evdref j tycon

  | GPatVar (loc,(someta,n)) ->
    let env = ltac_interp_name_env k0 lvar env in
    let ty =
      match tycon with
      | Some ty -> ty
      | None -> new_type_evar env evdref loc in
    let k = Evar_kinds.MatchingVar (someta,n) in
      { uj_val = e_new_evar env evdref ~src:(loc,k) ty; uj_type = ty }

  | GHole (loc, k, naming, None) ->
      let env = ltac_interp_name_env k0 lvar env in
      let ty =
        match tycon with
        | Some ty -> ty
        | None ->
          new_type_evar env evdref loc in
        { uj_val = e_new_evar env evdref ~src:(loc,k) ~naming ty; uj_type = ty }

  | GHole (loc, k, _naming, Some arg) ->
      let env = ltac_interp_name_env k0 lvar env in
      let ty =
        match tycon with
        | Some ty -> ty
        | None ->
          new_type_evar env evdref loc in
      let ist = lvar.ltac_genargs in
      let (c, sigma) = Hook.get f_genarg_interp ty env.ExtraEnv.env !evdref ist arg in
      let () = evdref := sigma in
      { uj_val = c; uj_type = ty }

  | GRec (loc,fixkind,names,bl,lar,vdef) ->
    let rec type_bl env ctxt = function
    [] -> ctxt
      | (na,bk,None,ty)::bl ->
        let ty' = pretype_type empty_valcon env evdref lvar ty in
	let dcl = local_assum (na, ty'.utj_val) in
        let dcl' = local_assum (ltac_interp_name lvar na,ty'.utj_val) in
	  type_bl (push_rel dcl env) (Context.Rel.add dcl' ctxt) bl
      | (na,bk,Some bd,ty)::bl ->
        let ty' = pretype_type empty_valcon env evdref lvar ty in
        let bd' = pretype (mk_tycon ty'.utj_val) env evdref lvar bd in
        let dcl = local_def (na, bd'.uj_val, ty'.utj_val) in
        let dcl' = local_def (ltac_interp_name lvar na, bd'.uj_val, ty'.utj_val) in
	  type_bl (push_rel dcl env) (Context.Rel.add dcl' ctxt) bl in
    let ctxtv = Array.map (type_bl env Context.Rel.empty) bl in
    let larj =
      Array.map2
        (fun e ar ->
          pretype_type empty_valcon (push_rel_context e env) evdref lvar ar)
        ctxtv lar in
    let lara = Array.map (fun a -> a.utj_val) larj in
    let ftys = Array.map2 (fun e a -> it_mkProd_or_LetIn a e) ctxtv lara in
    let nbfix = Array.length lar in
    let names = Array.map (fun id -> Name id) names in
    let _ = 
      match tycon with
      | Some t -> 
 	let fixi = match fixkind with
	  | GFix (vn,i) -> i
	  | GCoFix i -> i
	in e_conv env.ExtraEnv.env evdref ftys.(fixi) t
      | None -> true
    in
      (* Note: bodies are not used by push_rec_types, so [||] is safe *)
    let newenv = push_rec_types (names,ftys,[||]) env in
    let vdefj =
      Array.map2_i
	(fun i ctxt def ->
             (* we lift nbfix times the type in tycon, because of
	      * the nbfix variables pushed to newenv *)
          let (ctxt,ty) =
	    decompose_prod_n_assum !evdref (Context.Rel.length ctxt)
              (lift nbfix ftys.(i)) in
          let nenv = push_rel_context ctxt newenv in
          let j = pretype (mk_tycon ty) nenv evdref lvar def in
	    { uj_val = it_mkLambda_or_LetIn j.uj_val ctxt;
	      uj_type = it_mkProd_or_LetIn j.uj_type ctxt })
        ctxtv vdef in
      Typing.check_type_fixpoint loc env.ExtraEnv.env evdref names ftys vdefj;
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
              loc env.ExtraEnv.env possible_indexes (nf_fix !evdref fixdecls)
          in
	    make_judge (mkFix ((indexes,i),fixdecls)) ftys.(i)
	| GCoFix i ->
          let fixdecls = (names,ftys,fdefs) in
	  let cofix = (i, fixdecls) in
            (try check_cofix env.ExtraEnv.env (i, nf_fix !evdref fixdecls)
             with reraise ->
               let (e, info) = CErrors.push reraise in
               let info = Loc.add_loc info loc in
               iraise (e, info));
	    make_judge (mkCoFix cofix) ftys.(i)
      in
	inh_conv_coerce_to_tycon loc env evdref fixj tycon

  | GSort (loc,s) ->
    let j = pretype_sort loc evdref s in
      inh_conv_coerce_to_tycon loc env evdref j tycon

  | GApp (loc,f,args) ->
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
      | Const (p, u) when Environ.is_projection p env.ExtraEnv.env ->
	let p = Projection.make p false in
	let pb = Environ.lookup_projection p env.ExtraEnv.env in
	let npars = pb.Declarations.proj_npars in
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
        let resty = EConstr.of_constr resty in
      	  match EConstr.kind !evdref resty with
	  | Prod (na,c1,c2) ->
	    let tycon = Some c1 in
	    let hj = pretype tycon env evdref lvar c in
	    let candargs, ujval =
	      match candargs with
	      | [] -> [], j_val hj
	      | arg :: args -> 
		if e_conv env.ExtraEnv.env evdref (j_val hj) arg then
		  args, nf_evar !evdref (j_val hj)
		else [], j_val hj
	    in
	    let value, typ = app_f n (j_val resj) ujval, subst1 ujval c2 in
	    let j = { uj_val = value; uj_type = typ } in
	      apply_rec env (n+1) j candargs rest
		
	  | _ ->
	    let hj = pretype empty_tycon env evdref lvar c in
	      error_cant_apply_not_functional
                ~loc:(Loc.merge floc argloc) env.ExtraEnv.env !evdref
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
	    let c = EConstr.of_constr c in
	    let t = Retyping.get_type_of env.ExtraEnv.env !evdref c in
	    let t = EConstr.of_constr t in
	      make_judge c (* use this for keeping evars: resj.uj_val *) t
	  else resj
      | _ -> resj 
    in
      inh_conv_coerce_to_tycon loc env evdref resj tycon

  | GLambda(loc,name,bk,c1,c2)      ->
    let tycon' = evd_comb1
      (fun evd tycon ->
	match tycon with
	| None -> evd, tycon
	| Some ty ->
	  let evd, ty' = Coercion.inh_coerce_to_prod loc env.ExtraEnv.env evd ty in
	    evd, Some ty')
      evdref tycon
    in
    let (name',dom,rng) = evd_comb1 (split_tycon loc env.ExtraEnv.env) evdref tycon' in
    let dom_valcon = valcon_of_tycon dom in
    let j = pretype_type dom_valcon env evdref lvar c1 in
    (* The name specified by ltac is used also to create bindings. So
       the substitution must also be applied on variables before they are
       looked up in the rel context. *)
    let var = local_assum (name, j.utj_val) in
    let j' = pretype rng (push_rel var env) evdref lvar c2 in
    let name = ltac_interp_name lvar name in
    let resj = judge_of_abstraction env.ExtraEnv.env (orelse_name name name') j j' in
      inh_conv_coerce_to_tycon loc env evdref resj tycon

  | GProd(loc,name,bk,c1,c2)        ->
    let j = pretype_type empty_valcon env evdref lvar c1 in
    (* The name specified by ltac is used also to create bindings. So
       the substitution must also be applied on variables before they are
       looked up in the rel context. *)
    let j' = match name with
      | Anonymous ->
        let j = pretype_type empty_valcon env evdref lvar c2 in
          { j with utj_val = lift 1 j.utj_val }
      | Name _ ->
        let var = local_assum (name, j.utj_val) in
        let env' = push_rel var env in
          pretype_type empty_valcon env' evdref lvar c2
    in
    let name = ltac_interp_name lvar name in
    let resj =
      try
        judge_of_product env.ExtraEnv.env name j j'
      with TypeError _ as e ->
        let (e, info) = CErrors.push e in
        let info = Loc.add_loc info loc in
        iraise (e, info) in
      inh_conv_coerce_to_tycon loc env evdref resj tycon

  | GLetIn(loc,name,c1,c2)      ->
    let j =
      match c1 with
      | GCast (loc, c, CastConv t) ->
	let tj = pretype_type empty_valcon env evdref lvar t in
	  pretype (mk_tycon tj.utj_val) env evdref lvar c
      | _ -> pretype empty_tycon env evdref lvar c1
    in
    let t = evd_comb1 (Evarsolve.refresh_universes
      ~onlyalg:true ~status:Evd.univ_flexible (Some false) env.ExtraEnv.env)
      evdref j.uj_type in
    let t = EConstr.of_constr t in
    (* The name specified by ltac is used also to create bindings. So
       the substitution must also be applied on variables before they are
       looked up in the rel context. *)
    let var = local_def (name, j.uj_val, t) in
    let tycon = lift_tycon 1 tycon in
    let j' = pretype tycon (push_rel var env) evdref lvar c2 in
    let name = ltac_interp_name lvar name in
      { uj_val = mkLetIn (name, j.uj_val, t, j'.uj_val) ;
	uj_type = subst1 j.uj_val j'.uj_type }

  | GLetTuple (loc,nal,(na,po),c,d) ->
    let cj = pretype empty_tycon env evdref lvar c in
    let (IndType (indf,realargs)) =
      try find_rectype env.ExtraEnv.env !evdref cj.uj_type
      with Not_found ->
	let cloc = loc_of_glob_constr c in
	  error_case_not_inductive ~loc:cloc env.ExtraEnv.env !evdref cj
    in
    let realargs = List.map EConstr.of_constr realargs in
    let cstrs = get_constructors env.ExtraEnv.env indf in
    if not (Int.equal (Array.length cstrs) 1) then
      user_err ~loc  (str "Destructing let is only for inductive types" ++
	str " with one constructor.");
    let cs = cstrs.(0) in
    if not (Int.equal (List.length nal) cs.cs_nargs) then
      user_err ~loc:loc (str "Destructing let on this type expects " ++ 
	int cs.cs_nargs ++ str " variables.");
    let fsign, record = 
      match get_projections env.ExtraEnv.env indf with
      | None ->
	 List.map2 set_name (List.rev nal) cs.cs_args, false
      | Some ps ->
	let rec aux n k names l =
	  match names, l with
	  | na :: names, (LocalAssum (_,t) :: l) ->
            let t = EConstr.of_constr t in
	    let proj = Projection.make ps.(cs.cs_nargs - k) true in
	    local_def (na, lift (cs.cs_nargs - n) (mkProj (proj, cj.uj_val)), t)
	    :: aux (n+1) (k + 1) names l
	  | na :: names, (decl :: l) ->
	    set_name na decl :: aux (n+1) k names l
	  | [], [] -> []
	  | _ -> assert false
	in aux 1 1 (List.rev nal) cs.cs_args, true in
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
    let env_f = push_rel_context fsign env in
      (* Make dependencies from arity signature impossible *)
    let arsgn =
      let arsgn,_ = get_arity env.ExtraEnv.env indf in
	if not !allow_anonymous_refs then
	  List.map (set_name Anonymous) arsgn
	else arsgn
    in
      let psign = LocalAssum (na, build_dependent_inductive env.ExtraEnv.env indf) :: arsgn in
      let nar = List.length arsgn in
	  (match po with
	  | Some p ->
	    let env_p = push_rel_context psign env in
	    let pj = pretype_type empty_valcon env_p evdref lvar p in
	    let ccl = nf_evar !evdref pj.utj_val in
	    let psign = make_arity_signature env.ExtraEnv.env true indf in (* with names *)
	    let p = it_mkLambda_or_LetIn ccl psign in
	    let inst =
	      (Array.map_to_list EConstr.of_constr cs.cs_concl_realargs)
	      @[EConstr.of_constr (build_dependent_constructor cs)] in
	    let lp = lift cs.cs_nargs p in
	    let fty = hnf_lam_applist env.ExtraEnv.env !evdref lp inst in
	    let fty = EConstr.of_constr fty in
	    let fj = pretype (mk_tycon fty) env_f evdref lvar d in
	    let v =
	      let ind,_ = dest_ind_family indf in
		Typing.check_allowed_sort env.ExtraEnv.env !evdref ind cj.uj_val p;
		obj ind p cj.uj_val fj.uj_val
	    in
	      { uj_val = v; uj_type = (substl (realargs@[cj.uj_val]) ccl) }

	  | None ->
	    let tycon = lift_tycon cs.cs_nargs tycon in
	    let fj = pretype tycon env_f evdref lvar d in
	    let ccl = nf_evar !evdref fj.uj_type in
	    let ccl =
	      if noccur_between !evdref 1 cs.cs_nargs ccl then
		lift (- cs.cs_nargs) ccl
	      else
		error_cant_find_case_type ~loc env.ExtraEnv.env !evdref
		  cj.uj_val in
		 (* let ccl = refresh_universes ccl in *)
	    let p = it_mkLambda_or_LetIn (lift (nar+1) ccl) psign in
	    let v =
	      let ind,_ = dest_ind_family indf in
		Typing.check_allowed_sort env.ExtraEnv.env !evdref ind cj.uj_val p;
		obj ind p cj.uj_val fj.uj_val
	    in { uj_val = v; uj_type = ccl })

  | GIf (loc,c,(na,po),b1,b2) ->
    let cj = pretype empty_tycon env evdref lvar c in
    let (IndType (indf,realargs)) =
      try find_rectype env.ExtraEnv.env !evdref cj.uj_type
      with Not_found ->
	let cloc = loc_of_glob_constr c in
	  error_case_not_inductive ~loc:cloc env.ExtraEnv.env !evdref cj in
    let cstrs = get_constructors env.ExtraEnv.env indf in
      if not (Int.equal (Array.length cstrs) 2) then
        user_err ~loc 
		      (str "If is only for inductive types with two constructors.");

      let arsgn =
	let arsgn,_ = get_arity env.ExtraEnv.env indf in
	  if not !allow_anonymous_refs then
	      (* Make dependencies from arity signature impossible *)
	    List.map (set_name Anonymous) arsgn
	  else arsgn
      in
      let nar = List.length arsgn in
      let psign = LocalAssum (na, build_dependent_inductive env.ExtraEnv.env indf) :: arsgn in
      let pred,p = match po with
	| Some p ->
	  let env_p = push_rel_context psign env in
	  let pj = pretype_type empty_valcon env_p evdref lvar p in
	  let ccl = nf_evar !evdref pj.utj_val in
	  let pred = it_mkLambda_or_LetIn ccl psign in
	  let typ = lift (- nar) (EConstr.of_constr (beta_applist !evdref (pred,[cj.uj_val]))) in
	    pred, typ
	| None ->
	  let p = match tycon with
	    | Some ty -> ty
	    | None ->
              let env = ltac_interp_name_env k0 lvar env in
              new_type_evar env evdref loc
	  in
	    it_mkLambda_or_LetIn (lift (nar+1) p) psign, p in
      let pred = nf_evar !evdref pred in
      let p = nf_evar !evdref p in
      let f cs b =
	let n = Context.Rel.length cs.cs_args in
	let pi = lift n pred in (* liftn n 2 pred ? *)
	let pi = beta_applist !evdref (pi, [EConstr.of_constr (build_dependent_constructor cs)]) in
	let pi = EConstr.of_constr pi in
	let csgn =
	  if not !allow_anonymous_refs then
	    List.map (set_name Anonymous) cs.cs_args
	  else
	    List.map (map_name (function Name _ as n -> n
				       | Anonymous -> Name Namegen.default_non_dependent_ident))
		     cs.cs_args
	in
	let env_c = push_rel_context csgn env in
	let bj = pretype (mk_tycon pi) env_c evdref lvar b in
	  it_mkLambda_or_LetIn bj.uj_val cs.cs_args in
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
      inh_conv_coerce_to_tycon loc env evdref cj tycon

  | GCases (loc,sty,po,tml,eqns) ->
    Cases.compile_cases loc sty
      ((fun vtyc env evdref -> pretype vtyc (make_env env) evdref lvar),evdref)
      tycon env.ExtraEnv.env (* loc *) (po,tml,eqns)

  | GCast (loc,c,k) ->
    let cj =
      match k with
      | CastCoerce ->
	let cj = pretype empty_tycon env evdref lvar c in
	  evd_comb1 (Coercion.inh_coerce_to_base loc env.ExtraEnv.env) evdref cj
      | CastConv t | CastVM t | CastNative t ->
	let k = (match k with CastVM _ -> VMcast | CastNative _ -> NATIVEcast | _ -> DEFAULTcast) in
	let tj = pretype_type empty_valcon env evdref lvar t in
        let tval = evd_comb1 (Evarsolve.refresh_universes
                             ~onlyalg:true ~status:Evd.univ_flexible (Some false) env.ExtraEnv.env)
                          evdref tj.utj_val in
        let tval = EConstr.of_constr tval in
	let tval = nf_evar !evdref tval in
	let cj, tval = match k with
	  | VMcast ->
 	    let cj = pretype empty_tycon env evdref lvar c in
	    let cty = nf_evar !evdref cj.uj_type and tval = nf_evar !evdref tval in
	      if not (occur_existential !evdref cty || occur_existential !evdref tval) then
		let (evd,b) = Reductionops.vm_infer_conv env.ExtraEnv.env !evdref cty tval in
		if b then (evdref := evd; cj, tval)
		else
		  error_actual_type ~loc env.ExtraEnv.env !evdref cj tval 
                      (ConversionFailed (env.ExtraEnv.env,cty,tval))
	      else user_err ~loc  (str "Cannot check cast with vm: " ++
		str "unresolved arguments remain.")
	  | NATIVEcast ->
 	    let cj = pretype empty_tycon env evdref lvar c in
	    let cty = nf_evar !evdref cj.uj_type and tval = nf_evar !evdref tval in
            begin
	      let (evd,b) = Nativenorm.native_infer_conv env.ExtraEnv.env !evdref cty tval in
	      if b then (evdref := evd; cj, tval)
	      else
                error_actual_type ~loc env.ExtraEnv.env !evdref cj tval
                  (ConversionFailed (env.ExtraEnv.env,cty,tval))
            end
	  | _ -> 
 	    pretype (mk_tycon tval) env evdref lvar c, tval
	in
	let v = mkCast (cj.uj_val, k, tval) in
	  { uj_val = v; uj_type = tval }
    in inh_conv_coerce_to_tycon loc env evdref cj tycon

and pretype_instance k0 resolve_tc env evdref lvar loc hyps evk update =
  let f decl (subst,update) =
    let id = NamedDecl.get_id decl in
    let t = replace_vars subst (EConstr.of_constr (NamedDecl.get_type decl)) in
    let c, update =
      try
        let c = List.assoc id update in
        let c = pretype k0 resolve_tc (mk_tycon t) env evdref lvar c in
        c.uj_val, List.remove_assoc id update
      with Not_found ->
      try
        let (n,_,t') = lookup_rel_id id (rel_context env) in
        let t' = EConstr.of_constr t' in
        if is_conv env.ExtraEnv.env !evdref t t' then mkRel n, update else raise Not_found
      with Not_found ->
      try
        let t' = env |> lookup_named id |> NamedDecl.get_type in
        let t' = EConstr.of_constr t' in
        if is_conv env.ExtraEnv.env !evdref t t' then mkVar id, update else raise Not_found
      with Not_found ->
        user_err ~loc  (str "Cannot interpret " ++
          pr_existential_key !evdref evk ++
          str " in current context: no binding for " ++ pr_id id ++ str ".") in
    ((id,c)::subst, update) in
  let subst,inst = List.fold_right f hyps ([],update) in
  check_instance loc subst inst;
  Array.map_of_list snd subst

(* [pretype_type valcon env evdref lvar c] coerces [c] into a type *)
and pretype_type k0 resolve_tc valcon (env : ExtraEnv.t) evdref lvar = function
  | GHole (loc, knd, naming, None) ->
      let rec is_Type c = match EConstr.kind !evdref c with
      | Sort (Type _) -> true
      | Cast (c, _, _) -> is_Type c
      | _ -> false
      in
      (match valcon with
       | Some v ->
           let s =
	     let sigma =  !evdref in
	     let t = Retyping.get_type_of env.ExtraEnv.env sigma v in
	     let t = EConstr.of_constr t in
	       match EConstr.kind sigma (EConstr.of_constr (whd_all env.ExtraEnv.env sigma t)) with
               | Sort s -> s
               | Evar ev when is_Type (existential_type sigma ev) ->
		   evd_comb1 (define_evar_as_sort env.ExtraEnv.env) evdref ev
               | _ -> anomaly (Pp.str "Found a type constraint which is not a type")
           in
	     { utj_val = v;
	       utj_type = s }
       | None ->
           let env = ltac_interp_name_env k0 lvar env in
	   let s = evd_comb0 (new_sort_variable univ_flexible_alg) evdref in
	     { utj_val = e_new_evar env evdref ~src:(loc, knd) ~naming (mkSort s);
	       utj_type = s})
  | c ->
      let j = pretype k0 resolve_tc empty_tycon env evdref lvar c in
      let loc = loc_of_glob_constr c in
      let tj = evd_comb1 (Coercion.inh_coerce_to_sort loc env.ExtraEnv.env) evdref j in
	match valcon with
	| None -> tj
	| Some v ->
	    if e_cumul env.ExtraEnv.env evdref v tj.utj_val then tj
	    else
	      error_unexpected_type
                ~loc:(loc_of_glob_constr c) env.ExtraEnv.env !evdref tj.utj_val v

let ise_pretype_gen flags env sigma lvar kind c =
  let env = make_env env in
  let evdref = ref sigma in
  let k0 = Context.Rel.length (rel_context env) in
  let c' = match kind with
    | WithoutTypeConstraint ->
        (pretype k0 flags.use_typeclasses empty_tycon env evdref lvar c).uj_val
    | OfType exptyp ->
	(pretype k0 flags.use_typeclasses (mk_tycon exptyp) env evdref lvar c).uj_val
    | IsType ->
	(pretype_type k0 flags.use_typeclasses empty_valcon env evdref lvar c).utj_val 
  in
  process_inference_flags flags env.ExtraEnv.env sigma (!evdref,c')

let default_inference_flags fail = {
  use_typeclasses = true;
  use_unif_heuristics = true;
  use_hook = None;
  fail_evar = fail;
  expand_evars = true }

let no_classes_no_fail_inference_flags = {
  use_typeclasses = false;
  use_unif_heuristics = true;
  use_hook = None;
  fail_evar = false;
  expand_evars = true }

let all_and_fail_flags = default_inference_flags true
let all_no_fail_flags = default_inference_flags false

let empty_lvar : ltac_var_map = {
  ltac_constrs = Id.Map.empty;
  ltac_uconstrs = Id.Map.empty;
  ltac_idents = Id.Map.empty;
  ltac_genargs = Id.Map.empty;
}

let on_judgment sigma f j =
  let c = mkCast(j.uj_val,DEFAULTcast, j.uj_type) in
  let (c,_,t) = destCast sigma (f c) in
  {uj_val = c; uj_type = t}

let understand_judgment env sigma c =
  let env = make_env env in
  let evdref = ref sigma in
  let k0 = Context.Rel.length (rel_context env) in
  let j = pretype k0 true empty_tycon env evdref empty_lvar c in
  let j = on_judgment sigma (fun c ->
    let evd, c = process_inference_flags all_and_fail_flags env.ExtraEnv.env sigma (!evdref,c) in 
      evdref := evd; c) j
  in j, Evd.evar_universe_context !evdref

let understand_judgment_tcc env evdref c =
  let env = make_env env in
  let k0 = Context.Rel.length (rel_context env) in
  let j = pretype k0 true empty_tycon env evdref empty_lvar c in
  on_judgment !evdref (fun c ->
    let (evd,c) = process_inference_flags all_no_fail_flags env.ExtraEnv.env Evd.empty (!evdref,c) in
    evdref := evd; c) j

let ise_pretype_gen_ctx flags env sigma lvar kind c =
  let evd, c = ise_pretype_gen flags env sigma lvar kind c in
  let evd, f = Evarutil.nf_evars_and_universes evd in
    f (EConstr.Unsafe.to_constr c), Evd.evar_universe_context evd

(** Entry points of the high-level type synthesis algorithm *)

let understand
    ?(flags=all_and_fail_flags)
    ?(expected_type=WithoutTypeConstraint)
    env sigma c =
  ise_pretype_gen_ctx flags env sigma empty_lvar expected_type c

let understand_tcc ?(flags=all_no_fail_flags) env sigma ?(expected_type=WithoutTypeConstraint) c =
  let (sigma, c) = ise_pretype_gen flags env sigma empty_lvar expected_type c in
  (sigma, EConstr.Unsafe.to_constr c)

let understand_tcc_evars ?(flags=all_no_fail_flags) env evdref ?(expected_type=WithoutTypeConstraint) c =
  let sigma, c = ise_pretype_gen flags env !evdref empty_lvar expected_type c in
  evdref := sigma;
  EConstr.Unsafe.to_constr c

let understand_ltac flags env sigma lvar kind c =
  let (sigma, c) = ise_pretype_gen flags env sigma lvar kind c in
  (sigma, EConstr.Unsafe.to_constr c)

let constr_flags = {
  use_typeclasses = true;
  use_unif_heuristics = true;
  use_hook = None;
  fail_evar = true;
  expand_evars = true }

(* Fully evaluate an untyped constr *)
let type_uconstr ?(flags = constr_flags)
  ?(expected_type = WithoutTypeConstraint) ist c =
  { delayed = begin fun env sigma ->
  let { closure; term } = c in
  let vars = {
    ltac_constrs = closure.typed;
    ltac_uconstrs = closure.untyped;
    ltac_idents = closure.idents;
    ltac_genargs = Id.Map.empty;
  } in
  let sigma = Sigma.to_evar_map sigma in
  let (sigma, c) = understand_ltac flags env sigma vars expected_type term in
  Sigma.Unsafe.of_pair (c, sigma)
  end }

let pretype k0 resolve_tc typcon env evdref lvar t =
  pretype k0 resolve_tc typcon (make_env env) evdref lvar t

let pretype_type k0 resolve_tc valcon env evdref lvar t =
  pretype_type k0 resolve_tc valcon (make_env env) evdref lvar t
