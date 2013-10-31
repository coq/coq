(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4deps: "grammar/grammar.cma" i*)

open Pp
open Errors
open Util
open Names
open Nameops
open Namegen
open Term
open Vars
open Termops
open Reduction
open Tacticals
open Tacmach
open Tactics
open Patternops
open Clenv
open Glob_term
open Typeclasses
open Typeclasses_errors
open Classes
open Constrexpr
open Libnames
open Globnames
open Evd
open Misctypes
open Locus
open Locusops
open Decl_kinds
open Tacinterp
open Elimschemes
open Goal
open Environ
open Pp
open Names
open Tacinterp
open Termops
open Genarg
open Extraargs
open Entries
open Libnames

(** Typeclass-based generalized rewriting. *)

(** Constants used by the tactic. *)

let classes_dirpath =
  DirPath.make (List.map Id.of_string ["Classes";"Coq"])

let init_setoid () =
  if is_dirpath_prefix_of classes_dirpath (Lib.cwd ()) then ()
  else Coqlib.check_required_library ["Coq";"Setoids";"Setoid"]

let get_class str =
  let qualid = Qualid (Loc.ghost, qualid_of_string str) in
    lazy (class_info (Nametab.global qualid))
    
let proper_class = get_class "Coq.Classes.Morphisms.Proper"
let proper_proxy_class = get_class "Coq.Classes.Morphisms.ProperProxy"

let proper_proj = lazy (mkConst (Option.get (pi3 (List.hd (Lazy.force proper_class).cl_projs))))

let make_dir l = DirPath.make (List.rev_map Id.of_string l)

let try_find_global_reference dir s =
  let sp = Libnames.make_path (make_dir ("Coq"::dir)) (Id.of_string s) in
    Nametab.global_of_path sp

let try_find_reference dir s =
  constr_of_global (try_find_global_reference dir s)

let gen_constant dir s = Coqlib.gen_constant "rewrite" dir s
let coq_eq = lazy(gen_constant ["Init"; "Logic"] "eq")
let coq_f_equal = lazy (gen_constant ["Init"; "Logic"] "f_equal")
let coq_all = lazy (gen_constant ["Init"; "Logic"] "all")
let coq_forall = lazy (gen_constant ["Classes"; "Morphisms"] "forall_def")
let impl = lazy (gen_constant ["Program"; "Basics"] "impl")
let arrow = lazy (gen_constant ["Program"; "Basics"] "arrow")

let reflexive_type = lazy (try_find_reference ["Classes"; "RelationClasses"] "Reflexive")
let reflexive_proof = lazy (try_find_reference ["Classes"; "RelationClasses"] "reflexivity")

let symmetric_type = lazy (try_find_reference ["Classes"; "RelationClasses"] "Symmetric")
let symmetric_proof = lazy (try_find_reference ["Classes"; "RelationClasses"] "symmetry")

let transitive_type = lazy (try_find_reference ["Classes"; "RelationClasses"] "Transitive")
let transitive_proof = lazy (try_find_reference ["Classes"; "RelationClasses"] "transitivity")

let coq_inverse = lazy (gen_constant ["Program"; "Basics"] "flip")

let inverse car rel = mkApp (Lazy.force coq_inverse, [| car ; car; mkProp; rel |])

let forall_relation = lazy (gen_constant ["Classes"; "Morphisms"] "forall_relation")
let pointwise_relation = lazy (gen_constant ["Classes"; "Morphisms"] "pointwise_relation")
let respectful = lazy (gen_constant ["Classes"; "Morphisms"] "respectful")
let default_relation = lazy (gen_constant ["Classes"; "SetoidTactics"] "DefaultRelation")
let subrelation = lazy (gen_constant ["Classes"; "RelationClasses"] "subrelation")
let do_subrelation = lazy (gen_constant ["Classes"; "Morphisms"] "do_subrelation")
let apply_subrelation = lazy (gen_constant ["Classes"; "Morphisms"] "apply_subrelation")
let coq_relation = lazy (gen_constant ["Relations";"Relation_Definitions"] "relation")
let mk_relation a = mkApp (Lazy.force coq_relation, [| a |])
let rewrite_relation_class = lazy (gen_constant ["Classes"; "RelationClasses"] "RewriteRelation")

let proper_type = lazy (constr_of_global (Lazy.force proper_class).cl_impl)
let proper_proxy_type = lazy (constr_of_global (Lazy.force proper_proxy_class).cl_impl)

(** Utility functions *)

let split_head = function
    hd :: tl -> hd, tl
  | [] -> assert(false)

let evd_convertible env evd x y =
  try ignore(Evarconv.the_conv_x env x y evd); true
  with e when Errors.noncritical e -> false

let convertible env evd x y =
  Reductionops.is_conv env evd x y

(** Bookkeeping which evars are constraints so that we can 
    remove them at the end of the tactic. *)

let goalevars evars = fst evars
let cstrevars evars = snd evars

let new_cstr_evar (evd,cstrs) env t =
  let evd', t = Evarutil.new_evar evd env t in
    (evd', Evar.Set.add (fst (destEvar t)) cstrs), t

let new_goal_evar (evd,cstrs) env t =
  let evd', t = Evarutil.new_evar evd env t in
    (evd', cstrs), t

(** Building or looking up instances. *)

let proper_proof env evars carrier relation x =
  let goal = mkApp (Lazy.force proper_proxy_type, [| carrier ; relation; x |])
  in new_cstr_evar evars env goal

let extends_undefined evars evars' =
  let f ev evi found = found || not (Evd.mem evars ev)
  in fold_undefined f evars' false

let find_class_proof proof_type proof_method env evars carrier relation =
  try
    let goal = mkApp (Lazy.force proof_type, [| carrier ; relation |]) in
    let evars', c = Typeclasses.resolve_one_typeclass env evars goal in
      if extends_undefined evars evars' then raise Not_found
      else mkApp (Lazy.force proof_method, [| carrier; relation; c |])
  with e when Logic.catchable_exception e -> raise Not_found

let get_reflexive_proof env = find_class_proof reflexive_type reflexive_proof env
let get_symmetric_proof env = find_class_proof symmetric_type symmetric_proof env
let get_transitive_proof env = find_class_proof transitive_type transitive_proof env

(** Build an infered signature from constraints on the arguments and expected output
    relation *)

let build_signature evars env m (cstrs : (types * types option) option list)
    (finalcstr : (types * types option) option) =
  let mk_relty evars newenv ty obj =
    match obj with
      | None | Some (_, None) ->
	  let relty = mk_relation ty in
	    if closed0 ty then 
	      let env' = Environ.reset_with_named_context (Environ.named_context_val env) env in
		new_cstr_evar evars env' relty
	    else new_cstr_evar evars newenv relty
      | Some (x, Some rel) -> evars, rel
  in
  let rec aux env evars ty l =
    let t = Reductionops.whd_betadeltaiota env (fst evars) ty in
      match kind_of_term t, l with
      | Prod (na, ty, b), obj :: cstrs ->
	  if noccurn 1 b (* non-dependent product *) then
	    let ty = Reductionops.nf_betaiota (fst evars) ty in
	    let (evars, b', arg, cstrs) = aux env evars (subst1 mkProp b) cstrs in
	    let evars, relty = mk_relty evars env ty obj in
	    let newarg = mkApp (Lazy.force respectful, [| ty ; b' ; relty ; arg |]) in
	      evars, mkProd(na, ty, b), newarg, (ty, Some relty) :: cstrs
	  else
	    let (evars, b, arg, cstrs) = aux (Environ.push_rel (na, None, ty) env) evars b cstrs in
	    let ty = Reductionops.nf_betaiota (fst evars) ty in
	    let pred = mkLambda (na, ty, b) in
	    let liftarg = mkLambda (na, ty, arg) in
	    let arg' = mkApp (Lazy.force forall_relation, [| ty ; pred ; liftarg |]) in
	      if Option.is_empty obj then evars, mkProd(na, ty, b), arg', (ty, None) :: cstrs
	      else error "build_signature: no constraint can apply on a dependent argument"
      | _, obj :: _ -> anomaly ~label:"build_signature" (Pp.str "not enough products")
      | _, [] ->
	  (match finalcstr with
	  | None | Some (_, None) ->
	      let t = Reductionops.nf_betaiota (fst evars) ty in
	      let evars, rel = mk_relty evars env t None in
		evars, t, rel, [t, Some rel]
	  | Some (t, Some rel) -> evars, t, rel, [t, Some rel])
  in aux env evars m cstrs
  
type hypinfo = {
  cl : clausenv;
  ext : Evar.Set.t; (* New evars in this clausenv *)
  prf : constr;
  car : constr;
  rel : constr;
  l2r : bool;
  c1 : constr;
  c2 : constr;
  c  : (Tacinterp.interp_sign * Tacexpr.glob_constr_and_expr with_bindings) option;
  abs : (constr * types) option;
  flags : Unification.unify_flags;
}

(** Looking up declared rewrite relations (instances of [RewriteRelation]) *)
let is_applied_rewrite_relation env sigma rels t =
  match kind_of_term t with
  | App (c, args) when Array.length args >= 2 ->
      let head = if isApp c then fst (destApp c) else c in
	if eq_constr (Lazy.force coq_eq) head then None
	else
	  (try
	      let params, args = Array.chop (Array.length args - 2) args in
	      let env' = Environ.push_rel_context rels env in
	      let evd, evar = Evarutil.new_evar sigma env' (new_Type ()) in
	      let inst = mkApp (Lazy.force rewrite_relation_class, [| evar; mkApp (c, params) |]) in
	      let _ = Typeclasses.resolve_one_typeclass env' evd inst in
		Some (it_mkProd_or_LetIn t rels)
	  with e when Errors.noncritical e -> None)
  | _ -> None

let _ =
  Hook.set Equality.is_applied_rewrite_relation is_applied_rewrite_relation

let rec decompose_app_rel env evd t = 
  match kind_of_term t with
  | App (f, args) -> 
      if Array.length args > 1 then 
	let fargs, args = Array.chop (Array.length args - 2) args in
	  mkApp (f, fargs), args
      else 
	let (f', args) = decompose_app_rel env evd args.(0) in
	let ty = Typing.type_of env evd args.(0) in
	let f'' = mkLambda (Name (Id.of_string "x"), ty,
	  mkLambda (Name (Id.of_string "y"), lift 1 ty,
	    mkApp (lift 2 f, [| mkApp (lift 2 f', [| mkRel 2; mkRel 1 |]) |])))
	in (f'', args)
  | _ -> error "The term provided is not an applied relation."

let decompose_applied_relation env sigma flags orig (c,l) left2right =
  let ctype = Typing.type_of env sigma c in
  let find_rel ty =
    let eqclause = Clenv.make_clenv_binding_env_apply env sigma None (c, ty) l in
    let (equiv, args) = decompose_app_rel env eqclause.evd (Clenv.clenv_type eqclause) in
    let c1 = args.(0) and c2 = args.(1) in 
    let ty1, ty2 =
      Typing.type_of env eqclause.evd c1, Typing.type_of env eqclause.evd c2
    in
      if not (evd_convertible env eqclause.evd ty1 ty2) then None
      else
	let value = Clenv.clenv_value eqclause in
	let ext = Evarutil.evars_of_term value in
	  Some { cl=eqclause; ext=ext; prf=value;
		 car=ty1; rel = equiv;
		 l2r=left2right; c1=c1; c2=c2; c=orig; abs=None;
		 flags = flags }
  in
    match find_rel ctype with
    | Some c -> c
    | None ->
	let ctx,t' = Reductionops.splay_prod_assum env sigma ctype in (* Search for underlying eq *)
	match find_rel (it_mkProd_or_LetIn t' ctx) with
	| Some c -> c
	| None -> error "The term does not end with an applied homogeneous relation."

let decompose_applied_relation_expr env sigma flags (is, (c,l)) left2right =
  let sigma, cbl = Tacinterp.interp_open_constr_with_bindings is env sigma (c,l) in
    decompose_applied_relation env sigma flags (Some (is, (c,l))) cbl left2right

(** Hint database named "rewrite", now created directly in Auto *)

let rewrite_db = Auto.rewrite_db

let rewrite_transparent_state () =
  Auto.Hint_db.transparent_state (Auto.searchtable_map rewrite_db)

let rewrite_unif_flags = {
  Unification.modulo_conv_on_closed_terms = None;
  Unification.use_metas_eagerly_in_conv_on_closed_terms = true;
  Unification.modulo_delta = empty_transparent_state;
  Unification.modulo_delta_types = full_transparent_state;
  Unification.modulo_delta_in_merge = None;
  Unification.check_applied_meta_types = true;
  Unification.resolve_evars = false;
  Unification.use_pattern_unification = true;
  Unification.use_meta_bound_pattern_unification = true;
  Unification.frozen_evars = Evar.Set.empty;
  Unification.restrict_conv_on_strict_subterms = false;
  Unification.modulo_betaiota = false;
  Unification.modulo_eta = true;
  Unification.allow_K_in_toplevel_higher_order_unification = true
}

let rewrite2_unif_flags =
  {  Unification.modulo_conv_on_closed_terms = Some cst_full_transparent_state;
     Unification.use_metas_eagerly_in_conv_on_closed_terms = true;
     Unification.modulo_delta = empty_transparent_state;
     Unification.modulo_delta_types = cst_full_transparent_state;
     Unification.modulo_delta_in_merge = None;
     Unification.check_applied_meta_types = true;
     Unification.resolve_evars = false;
     Unification.use_pattern_unification = true;
     Unification.use_meta_bound_pattern_unification = true;
     Unification.frozen_evars = Evar.Set.empty;
     Unification.restrict_conv_on_strict_subterms = false;
     Unification.modulo_betaiota = true;
     Unification.modulo_eta = true;
     Unification.allow_K_in_toplevel_higher_order_unification = true
  }

let general_rewrite_unif_flags () = 
  let ts = rewrite_transparent_state () in
    {  Unification.modulo_conv_on_closed_terms = Some ts;
       Unification.use_metas_eagerly_in_conv_on_closed_terms = true;
       Unification.modulo_delta = ts;
       Unification.modulo_delta_types = ts;
       Unification.modulo_delta_in_merge = None;
       Unification.check_applied_meta_types = true;
       Unification.resolve_evars = false;
       Unification.use_pattern_unification = true;
       Unification.use_meta_bound_pattern_unification = true;
       Unification.frozen_evars = Evar.Set.empty;
       Unification.restrict_conv_on_strict_subterms = false;
       Unification.modulo_betaiota = true;
       Unification.modulo_eta = true;
       Unification.allow_K_in_toplevel_higher_order_unification = true }

let refresh_hypinfo env sigma hypinfo =
  if Option.is_empty hypinfo.abs then
    let {l2r=l2r; c=c;cl=cl;flags=flags} = hypinfo in
      match c with
	| Some c ->
	    (* Refresh the clausenv to not get the same meta twice in the goal. *)
	    decompose_applied_relation_expr env sigma flags c l2r;
	| _ -> hypinfo
  else hypinfo


let solve_remaining_by by env prf =
  match by with
  | None -> env, prf
  | Some tac ->
    let indep = clenv_independent env in
    let tac = eval_tactic tac in
    let evd' = 
      List.fold_right (fun mv evd ->
        let ty = Clenv.clenv_nf_meta env (meta_type evd mv) in
	let c = Pfedit.build_by_tactic env.env ty (tclCOMPLETE tac) in
	  meta_assign mv (c, (Conv,TypeNotProcessed)) evd)
      indep env.evd
    in { env with evd = evd' }, prf

let extend_evd sigma ext sigma' =
  Evar.Set.fold (fun i acc ->
    Evd.add acc i (Evarutil.nf_evar_info sigma' (Evd.find sigma' i)))
    ext sigma

let shrink_evd sigma ext =
  Evar.Set.fold (fun i acc -> Evd.remove acc i) ext sigma

let no_constraints cstrs = 
  fun ev _ -> not (Evar.Set.mem ev cstrs)

let unify_eqn env (sigma, cstrs) hypinfo by t =
  if isEvar t then hypinfo, None
  else try
    let {cl=cl; ext=ext; prf=prf; car=car; rel=rel; l2r=l2r; c1=c1; c2=c2; c=c; abs=abs} = 
      hypinfo in
    let left = if l2r then c1 else c2 in
    let evd' = Evd.evars_reset_evd ~with_conv_pbs:true sigma cl.evd in
    let evd'' = extend_evd evd' ext cl.evd in
    let cl = { cl with evd = evd'' } in
    let hypinfo, evd', prf, c1, c2, car, rel =
      match abs with
      | Some (absprf, absprfty) ->
	  let env' = clenv_unify ~flags:rewrite_unif_flags CONV left t cl in
	    hypinfo, env'.evd, prf, c1, c2, car, rel
      | None ->
	  let env' = clenv_unify ~flags:hypinfo.flags CONV left t cl in
	  let env' = Clenvtac.clenv_pose_dependent_evars true env' in
	  let evd' = Typeclasses.resolve_typeclasses ~filter:(no_constraints cstrs)
	    ~fail:true env'.env env'.evd in
	  let env' = { env' with evd = evd' } in
	  let env', prf = solve_remaining_by by env' (Clenv.clenv_value env') in	   
	  let nf c = Evarutil.nf_evar env'.evd (Clenv.clenv_nf_meta env' c) in
	  let c1 = nf c1 and c2 = nf c2
	  and car = nf car and rel = nf rel
	  and prf = nf prf in
	  let ty1 = Typing.type_of env'.env env'.evd c1
	  and ty2 = Typing.type_of env'.env env'.evd c2
	  in
	    if convertible env env'.evd ty1 ty2 then 
	      (if occur_meta_or_existential prf then
		let hypinfo = refresh_hypinfo env env'.evd hypinfo in
		 (hypinfo, env'.evd, prf, c1, c2, car, rel)
	       else (** Evars have been solved, we can go back to the initial evd,
			but keep the potential refinement of existing evars. *)
		let evd' = shrink_evd env'.evd ext in
		  (hypinfo, evd', prf, c1, c2, car, rel))
	    else raise Reduction.NotConvertible
    in
    let res =
      if l2r then (prf, (car, rel, c1, c2))
      else
	try (mkApp (get_symmetric_proof env evd' car rel,
		   [| c1 ; c2 ; prf |]),
	    (car, rel, c2, c1))
	with Not_found ->
	  (prf, (car, inverse car rel, c2, c1))
    in hypinfo, Some (evd', res)
  with e when Class_tactics.catchable e -> hypinfo, None

let unfold_impl t =
  match kind_of_term t with
    | App (arrow, [| a; b |])(*  when eq_constr arrow (Lazy.force impl) *) ->
	mkProd (Anonymous, a, lift 1 b)
    | _ -> assert false

let unfold_all t =
  match kind_of_term t with
    | App (id, [| a; b |]) (* when eq_constr id (Lazy.force coq_all) *) ->
	(match kind_of_term b with
	  | Lambda (n, ty, b) -> mkProd (n, ty, b)
	  | _ -> assert false)
    | _ -> assert false

let unfold_forall t =
  match kind_of_term t with
    | App (id, [| a; b |]) (* when eq_constr id (Lazy.force coq_all) *) ->
	(match kind_of_term b with
	  | Lambda (n, ty, b) -> mkProd (n, ty, b)
	  | _ -> assert false)
    | _ -> assert false

let arrow_morphism ta tb a b =
  let ap = is_Prop ta and bp = is_Prop tb in
    if ap && bp then mkApp (Lazy.force impl, [| a; b |]), unfold_impl
    else if ap then (* Domain in Prop, CoDomain in Type *)
      mkProd (Anonymous, a, b), (fun x -> x)
    else if bp then (* Dummy forall *)
      mkApp (Lazy.force coq_all, [| a; mkLambda (Anonymous, a, b) |]), unfold_forall
    else (* None in Prop, use arrow *)
      mkApp (Lazy.force arrow, [| a; b |]), unfold_impl

let rec decomp_pointwise n c =
  if Int.equal n 0 then c
  else
    match kind_of_term c with
    | App (f, [| a; b; relb |]) when eq_constr f (Lazy.force pointwise_relation) ->
	decomp_pointwise (pred n) relb
    | App (f, [| a; b; arelb |]) when eq_constr f (Lazy.force forall_relation) ->
	decomp_pointwise (pred n) (Reductionops.beta_applist (arelb, [mkRel 1]))
    | _ -> invalid_arg "decomp_pointwise"

let rec apply_pointwise rel = function
  | arg :: args ->
      (match kind_of_term rel with
      | App (f, [| a; b; relb |]) when eq_constr f (Lazy.force pointwise_relation) ->
	  apply_pointwise relb args
      | App (f, [| a; b; arelb |]) when eq_constr f (Lazy.force forall_relation) ->
	  apply_pointwise (Reductionops.beta_applist (arelb, [arg])) args
      | _ -> invalid_arg "apply_pointwise")
  | [] -> rel

let pointwise_or_dep_relation n t car rel =
  if noccurn 1 car && noccurn 1 rel then
    mkApp (Lazy.force pointwise_relation, [| t; lift (-1) car; lift (-1) rel |])
  else
    mkApp (Lazy.force forall_relation, 
	  [| t; mkLambda (n, t, car); mkLambda (n, t, rel) |])

let lift_cstr env evars (args : constr list) c ty cstr =
  let start evars env car =
    match cstr with
    | None | Some (_, None) -> 
      new_cstr_evar evars env (mk_relation car)
    | Some (ty, Some rel) -> evars, rel
  in
  let rec aux evars env prod n = 
    if Int.equal n 0 then start evars env prod
    else
      match kind_of_term (Reduction.whd_betadeltaiota env prod) with
      | Prod (na, ty, b) ->
	  if noccurn 1 b then
	    let b' = lift (-1) b in
	    let evars, rb = aux evars env b' (pred n) in
	      evars, mkApp (Lazy.force pointwise_relation, [| ty; b'; rb |])
	  else
	    let evars, rb = aux evars (Environ.push_rel (na, None, ty) env) b (pred n) in
	      evars, mkApp (Lazy.force forall_relation, 
		    [| ty; mkLambda (na, ty, b); mkLambda (na, ty, rb) |])
      | _ -> raise Not_found
  in 
  let rec find env c ty = function
    | [] -> None
    | arg :: args ->
	try let evars, found = aux evars env ty (succ (List.length args)) in
	      Some (evars, found, c, ty, arg :: args)
	with Not_found ->
	  find env (mkApp (c, [| arg |])) (prod_applist ty [arg]) args
  in find env c ty args

let unlift_cstr env sigma = function
  | None -> None
  | Some codom -> Some (decomp_pointwise 1 codom)

type rewrite_flags = { under_lambdas : bool; on_morphisms : bool }

let default_flags = { under_lambdas = true; on_morphisms = true; }

type evars = evar_map * Evar.Set.t (* goal evars, constraint evars *)

type rewrite_proof = 
  | RewPrf of constr * constr
  | RewCast of cast_kind

let get_opt_rew_rel = function RewPrf (rel, prf) -> Some rel | _ -> None

type rewrite_result_info = {
  rew_car : constr;
  rew_from : constr;
  rew_to : constr;
  rew_prf : rewrite_proof;
  rew_evars : evars;
}

type rewrite_result = rewrite_result_info option

type 'a pure_strategy = 'a -> Environ.env -> Id.t list -> constr -> types ->
  constr option -> evars -> 'a * rewrite_result option

type strategy = unit pure_strategy

let get_rew_rel r = match r.rew_prf with
  | RewPrf (rel, prf) -> rel
  | RewCast c -> mkApp (Coqlib.build_coq_eq (), [| r.rew_car; r.rew_from; r.rew_to |])

let get_rew_prf r = match r.rew_prf with
  | RewPrf (rel, prf) -> rel, prf 
  | RewCast c ->
    let rel = mkApp (Coqlib.build_coq_eq (), [| r.rew_car |]) in
      rel, mkCast (mkApp (Coqlib.build_coq_eq_refl (), [| r.rew_car; r.rew_from |]),
		   c, mkApp (rel, [| r.rew_from; r.rew_to |]))

let resolve_subrelation env avoid car rel prf rel' res =
  if eq_constr rel rel' then res
  else
    let app = mkApp (Lazy.force subrelation, [|car; rel; rel'|]) in
    let evars, subrel = new_cstr_evar res.rew_evars env app in
    let appsub = mkApp (subrel, [| res.rew_from ; res.rew_to ; prf |]) in
      { res with
	rew_prf = RewPrf (rel', appsub);
	rew_evars = evars }

let resolve_morphism env avoid oldt m ?(fnewt=fun x -> x) args args' cstr evars =
  let evars, morph_instance, proj, sigargs, m', args, args' =
    let first = match (Array.findi (fun _ b -> not (Option.is_empty b)) args') with
    | Some i -> i
    | None -> invalid_arg "resolve_morphism" in
    let morphargs, morphobjs = Array.chop first args in
    let morphargs', morphobjs' = Array.chop first args' in
    let appm = mkApp(m, morphargs) in
    let appmtype = Typing.type_of env (goalevars evars) appm in
    let cstrs = List.map 
      (Option.map (fun r -> r.rew_car, get_opt_rew_rel r.rew_prf)) 
      (Array.to_list morphobjs') 
    in
      (* Desired signature *)
    let evars, appmtype', signature, sigargs = 
      build_signature evars env appmtype cstrs cstr
    in
      (* Actual signature found *)
    let cl_args = [| appmtype' ; signature ; appm |] in
    let app = mkApp (Lazy.force proper_type, cl_args) in
    let env' = Environ.push_named
      (Id.of_string "do_subrelation", 
       Some (Lazy.force do_subrelation), 
       Lazy.force apply_subrelation)
      env
    in
    let evars, morph = new_cstr_evar evars env' app in
      evars, morph, morph, sigargs, appm, morphobjs, morphobjs'
  in
  let projargs, subst, evars, respars, typeargs =
    Array.fold_left2
      (fun (acc, subst, evars, sigargs, typeargs') x y ->
	let (carrier, relation), sigargs = split_head sigargs in
	  match relation with
	  | Some relation ->
	      let carrier = substl subst carrier
	      and relation = substl subst relation in
	      (match y with
	      | None ->
		  let evars, proof = proper_proof env evars carrier relation x in
		    [ proof ; x ; x ] @ acc, subst, evars, sigargs, x :: typeargs'
	      | Some r ->
		  [ snd (get_rew_prf r); r.rew_to; x ] @ acc, subst, evars, 
	      sigargs, r.rew_to :: typeargs')
	  | None ->
	      if not (Option.is_empty y) then 
		error "Cannot rewrite the argument of a dependent function";
	      x :: acc, x :: subst, evars, sigargs, x :: typeargs')
      ([], [], evars, sigargs, []) args args'
  in
  let proof = applistc proj (List.rev projargs) in
  let newt = applistc m' (List.rev typeargs) in
    match respars with
	[ a, Some r ] -> evars, proof, a, r, oldt, fnewt newt
      | _ -> assert(false)

let apply_constraint env avoid car rel prf cstr res =
  match cstr with
  | None -> res
  | Some r -> resolve_subrelation env avoid car rel prf r res

let eq_env x y = x == y

let apply_rule by loccs : (hypinfo * int) pure_strategy =
  let (nowhere_except_in,occs) = convert_occs loccs in
  let is_occ occ =
    if nowhere_except_in
    then Int.List.mem occ occs
    else not (Int.List.mem occ occs) in
    fun (hypinfo, occ) env avoid t ty cstr evars ->
      let hypinfo =
        if not (eq_env hypinfo.cl.env env) then
          refresh_hypinfo env (goalevars evars) hypinfo
        else hypinfo
      in
      let hypinfo, unif = unify_eqn env evars hypinfo by t in
      let occ = if not (Option.is_empty unif) then succ occ else occ in
      let res =
	match unif with
	| Some (evd', (prf, (car, rel, c1, c2))) when is_occ occ ->
	    begin
	      if eq_constr t c2 then Some None
	      else
		let res = { rew_car = ty; rew_from = c1;
			    rew_to = c2; rew_prf = RewPrf (rel, prf); 
			    rew_evars = evd', cstrevars evars }
		in Some (Some (apply_constraint env avoid car rel prf cstr res))
	    end
	| _ -> None
      in
      ((hypinfo, occ), res)

let apply_lemma flags c left2right by loccs : strategy =
  fun () env avoid t ty cstr evars ->
    let hypinfo = 
      decompose_applied_relation env (goalevars evars) flags None c left2right
    in
    let _, res = apply_rule by loccs (hypinfo, 0) env avoid t ty cstr evars in
    (), res

let make_leibniz_proof c ty r =
  let prf = 
    match r.rew_prf with
    | RewPrf (rel, prf) -> 
	let rel = mkApp (Lazy.force coq_eq, [| ty |]) in
	let prf =
	  mkApp (Lazy.force coq_f_equal,
		[| r.rew_car; ty;
		   mkLambda (Anonymous, r.rew_car, c);
		   r.rew_from; r.rew_to; prf |])
	in RewPrf (rel, prf)
    | RewCast k -> r.rew_prf
  in
    { r with rew_car = ty; 
      rew_from = subst1 r.rew_from c; rew_to = subst1 r.rew_to c; rew_prf = prf }

let reset_env env =
  let env' = Global.env_of_context (Environ.named_context_val env) in
    Environ.push_rel_context (Environ.rel_context env) env'
      
let fold_match ?(force=false) env sigma c =
  let (ci, p, c, brs) = destCase c in
  let cty = Retyping.get_type_of env sigma c in
  let dep, pred, exists, (sk, eff) = 
    let env', ctx, body =
      let ctx, pred = decompose_lam_assum p in
      let env' = Environ.push_rel_context ctx env in
	env', ctx, pred
    in
    let sortp = Retyping.get_sort_family_of env' sigma body in
    let sortc = Retyping.get_sort_family_of env sigma cty in
    let dep = not (noccurn 1 body) in
    let pred = if dep then p else
	it_mkProd_or_LetIn (subst1 mkProp body) (List.tl ctx)
    in
    let sk = 
      if sortp == InProp then
	if sortc == InProp then
	  if dep then case_dep_scheme_kind_from_prop
	  else case_scheme_kind_from_prop
	else (
	  if dep
	  then case_dep_scheme_kind_from_type_in_prop
	  else case_scheme_kind_from_type)
      else ((* sortc <> InProp by typing *)
	if dep
	then case_dep_scheme_kind_from_type
	else case_scheme_kind_from_type)
    in 
    let exists = Ind_tables.check_scheme sk ci.ci_ind in
      if exists || force then
	dep, pred, exists, Ind_tables.find_scheme sk ci.ci_ind
      else raise Not_found
  in
  let app =
    let ind, args = Inductive.find_rectype env cty in
    let pars, args = List.chop ci.ci_npar args in
    let meths = List.map (fun br -> br) (Array.to_list brs) in
      applist (mkConst sk, pars @ [pred] @ meths @ args @ [c])
  in 
    sk, (if exists then env else reset_env env), app, eff

let fold_match_tac c gl =
  let _, _, c', eff = fold_match ~force:true (pf_env gl) (project gl) c in
   tclTHEN (Tactics.emit_side_effects eff)
    (change (Some (snd (pattern_of_constr (project gl) c))) c' onConcl) gl


let unfold_match env sigma sk app =
  match kind_of_term app with
  | App (f', args) when eq_constr f' (mkConst sk) ->
      let v = Environ.constant_value (Global.env ()) sk in
	Reductionops.whd_beta sigma (mkApp (v, args))
  | _ -> app

let is_rew_cast = function RewCast _ -> true | _ -> false

let coerce env avoid cstr res = 
  let rel, prf = get_rew_prf res in
    apply_constraint env avoid res.rew_car rel prf cstr res

let subterm all flags (s : 'a pure_strategy) : 'a pure_strategy =
  let rec aux state env avoid t ty cstr evars =
    let cstr' = Option.map (fun c -> (ty, Some c)) cstr in
      match kind_of_term t with
      | App (m, args) ->
	  let rewrite_args state success =
	    let state, args', evars', progress =
	      Array.fold_left
		(fun (state, acc, evars, progress) arg ->
		  if not (Option.is_empty progress) && not all then (state, None :: acc, evars, progress)
		  else
		    let state, res = s state env avoid arg (Typing.type_of env (goalevars evars) arg) None evars in
		      match res with
		      | Some None -> (state, None :: acc, evars, if Option.is_empty progress then Some false else progress)
		      | Some (Some r) -> (state, Some r :: acc, r.rew_evars, Some true)
		      | None -> (state, None :: acc, evars, progress))
		(state, [], evars, success) args
	    in
	      state, match progress with
	      | None -> None
	      | Some false -> Some None
	      | Some true ->
		  let args' = Array.of_list (List.rev args') in
		    if Array.exists
		      (function 
			 | None -> false 
			 | Some r -> not (is_rew_cast r.rew_prf)) args'
		    then
		      let evars', prf, car, rel, c1, c2 = resolve_morphism env avoid t m args args' cstr' evars' in
		      let res = { rew_car = ty; rew_from = c1;
				  rew_to = c2; rew_prf = RewPrf (rel, prf);
				  rew_evars = evars' } 
		      in Some (Some res)
		    else 
		      let args' = Array.map2
			(fun aorig anew ->
			   match anew with None -> aorig
			   | Some r -> r.rew_to) args args' 
		      in
		      let res = { rew_car = ty; rew_from = t;
				  rew_to = mkApp (m, args'); rew_prf = RewCast DEFAULTcast;
				  rew_evars = evars' }
		      in Some (Some res)

	  in
	    if flags.on_morphisms then
	      let mty = Typing.type_of env (goalevars evars) m in
	      let evars, cstr', m, mty, argsl, args = 
		let argsl = Array.to_list args in
		  match lift_cstr env evars argsl m mty None with
		  | Some (evars, cstr', m, mty, args) -> 
		    evars, Some cstr', m, mty, args, Array.of_list args
		  | None -> evars, None, m, mty, argsl, args
	      in
	      let state, m' = s state env avoid m mty cstr' evars in
		match m' with
		| None -> rewrite_args state None (* Standard path, try rewrite on arguments *)
		| Some None -> rewrite_args state (Some false)
		| Some (Some r) ->
		    (* We rewrote the function and get a proof of pointwise rel for the arguments.
		       We just apply it. *)
		    let prf = match r.rew_prf with
		      | RewPrf (rel, prf) ->
			  RewPrf (apply_pointwise rel argsl, mkApp (prf, args))
		      | x -> x
		    in
		    let res =
		      { rew_car = prod_appvect r.rew_car args;
			rew_from = mkApp(r.rew_from, args); rew_to = mkApp(r.rew_to, args);
			rew_prf = prf;
			rew_evars = r.rew_evars }
		    in 
		      state, match prf with
		      | RewPrf (rel, prf) ->
			Some (Some (apply_constraint env avoid res.rew_car rel prf cstr res))
		      | _ -> Some (Some res)
	    else rewrite_args state None
	      
      | Prod (n, x, b) when noccurn 1 b ->
	  let b = subst1 mkProp b in
	  let tx = Typing.type_of env (goalevars evars) x and tb = Typing.type_of env (goalevars evars) b in
	  let mor, unfold = arrow_morphism tx tb x b in
	  let state, res = aux state env avoid mor ty cstr evars in
	    state, (match res with
	    | Some (Some r) -> Some (Some { r with rew_to = unfold r.rew_to })
	    | _ -> res)

      (* 		if x' = None && flags.under_lambdas then *)
      (* 		  let lam = mkLambda (n, x, b) in *)
      (* 		  let lam', occ = aux env lam occ None in *)
      (* 		  let res =  *)
      (* 		    match lam' with *)
      (* 		    | None -> None *)
      (* 		    | Some (prf, (car, rel, c1, c2)) -> *)
      (* 			Some (resolve_morphism env sigma t *)
      (* 				 ~fnewt:unfold_all *)
      (* 				 (Lazy.force coq_all) [| x ; lam |] [| None; lam' |] *)
      (* 				 cstr evars) *)
      (* 		  in res, occ *)
      (* 		else *)

      | Prod (n, dom, codom) ->
	  let lam = mkLambda (n, dom, codom) in
	  let app, unfold = 
	    if eq_constr ty mkProp then
	      mkApp (Lazy.force coq_all, [| dom; lam |]), unfold_all
	    else mkApp (Lazy.force coq_forall, [| dom; lam |]), unfold_forall
	  in
	  let state, res = aux state env avoid app ty cstr evars in
	    state, (match res with
	     | Some (Some r) -> Some (Some { r with rew_to = unfold r.rew_to })
	     | _ -> res)

      | Lambda (n, t, b) when flags.under_lambdas ->
	  let n' = name_app (fun id -> Tactics.fresh_id_in_env avoid id env) n in
	  let env' = Environ.push_rel (n', None, t) env in
	  let state, b' = s state env' avoid b (Typing.type_of env' (goalevars evars) b) (unlift_cstr env (goalevars evars) cstr) evars in
	    state, (match b' with
	    | Some (Some r) ->
		let prf = match r.rew_prf with
		  | RewPrf (rel, prf) ->
		      let rel = pointwise_or_dep_relation n' t r.rew_car rel in
		      let prf = mkLambda (n', t, prf) in
			RewPrf (rel, prf)
		  | x -> x
		in
		  Some (Some { r with
		    rew_prf = prf;
		    rew_car = mkProd (n, t, r.rew_car);
		    rew_from = mkLambda(n, t, r.rew_from);
		    rew_to = mkLambda (n, t, r.rew_to) })
	    | _ -> b')

      | Case (ci, p, c, brs) ->
	  let cty = Typing.type_of env (goalevars evars) c in
	  let cstr' = Some (mkApp (Lazy.force coq_eq, [| cty |])) in
	  let state, c' = s state env avoid c cty cstr' evars in
	  let state, res = 
	    match c' with
	    | Some (Some r) ->
		let res = make_leibniz_proof (mkCase (ci, lift 1 p, mkRel 1, Array.map (lift 1) brs)) ty r in
		  state, Some (Some (coerce env avoid cstr res))
	    | x ->
	      if Array.for_all (Int.equal 0) ci.ci_cstr_ndecls then
		let cstr = Some (mkApp (Lazy.force coq_eq, [| ty |])) in
		let state, found, brs' = Array.fold_left 
		  (fun (state, found, acc) br ->
		   if not (Option.is_empty found) then (state, found, fun x -> lift 1 br :: acc x)
		   else
                     let state, res = s state env avoid br ty cstr evars in
		     match res with
		     | Some (Some r) -> (state, Some r, fun x -> mkRel 1 :: acc x)
		     | _ -> (state, None, fun x -> lift 1 br :: acc x))
		  (state, None, fun x -> []) brs
		in
		  state, match found with
		  | Some r ->
		    let ctxc = mkCase (ci, lift 1 p, lift 1 c, Array.of_list (List.rev (brs' x))) in
		      Some (Some (make_leibniz_proof ctxc ty r))
		  | None -> x
	      else
		match try Some (fold_match env (goalevars evars) t) with Not_found -> None with
		| None -> state, x
		| Some (cst, _, t',_) -> (* eff XXX *)
                  let state, res = aux state env avoid t' ty cstr evars in
		  state, match res with
		  | Some (Some prf) -> 
		    Some (Some { prf with
				 rew_from = t; rew_to = unfold_match env (goalevars evars) cst prf.rew_to })
		  | x' -> x
	  in 
	    state, (match res with
	     | Some (Some r) ->  
	       let rel, prf = get_rew_prf r in
		 Some (Some (apply_constraint env avoid r.rew_car rel prf cstr r))
	     | x -> x)
      | _ -> state, None
  in aux

let all_subterms = subterm true default_flags
let one_subterm = subterm false default_flags

(** Requires transitivity of the rewrite step, if not a reduction.
    Not tail-recursive. *)

let transitivity state env avoid (res : rewrite_result_info) (next : 'a pure_strategy) : 'a * rewrite_result option =
  let state, res' = next state env avoid res.rew_to res.rew_car (get_opt_rew_rel res.rew_prf) res.rew_evars in
  state, match res' with
  | None -> None
  | Some None -> Some (Some res)
  | Some (Some res') ->
      match res.rew_prf with
      | RewCast c -> Some (Some { res' with rew_from = res.rew_from })
      | RewPrf (rew_rel, rew_prf) ->
	  match res'.rew_prf with
	  | RewCast _ -> Some (Some ({ res with rew_to = res'.rew_to }))
	  | RewPrf (res'_rel, res'_prf) ->
	      let prfty = mkApp (Lazy.force transitive_type, [| res.rew_car; rew_rel |]) in
	      let evars, prf = new_cstr_evar res'.rew_evars env prfty in
	      let prf = mkApp (prf, [|res.rew_from; res'.rew_from; res'.rew_to;
				      rew_prf; res'_prf |])
	      in Some (Some { res' with rew_from = res.rew_from; 
		rew_evars = evars; rew_prf = RewPrf (res'_rel, prf) })
		
(** Rewriting strategies.

    Inspired by ELAN's rewriting strategies:
    http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.21.4049
*)

module Strategies =
  struct

    let fail : 'a pure_strategy =
      fun s env avoid t ty cstr evars -> (s, None)

    let id : 'a pure_strategy =
      fun s env avoid t ty cstr evars -> (s, Some None)

    let refl : 'a pure_strategy =
      fun s env avoid t ty cstr evars ->
	let evars, rel = match cstr with
	  | None -> new_cstr_evar evars env (mk_relation ty)
	  | Some r -> evars, r
	in
	let evars, proof =
	  let mty = mkApp (Lazy.force proper_proxy_type, [| ty ; rel; t |]) in
	    new_cstr_evar evars env mty
	in
	  s, Some (Some { rew_car = ty; rew_from = t; rew_to = t;
		       rew_prf = RewPrf (rel, proof); rew_evars = evars })

    let progress (s : 'a pure_strategy) : 'a pure_strategy =
      fun state env avoid t ty cstr evars ->
        let state, res = s state env avoid t ty cstr evars in
	state, match res with
	| None -> None
	| Some None -> None
	| r -> r

    let seq (fst : 'a pure_strategy) (snd : 'a pure_strategy) : 'a pure_strategy =
      fun state env avoid t ty cstr evars ->
        let state, res = fst state env avoid t ty cstr evars in
	match res with
	| None -> state, None
	| Some None -> snd state env avoid t ty cstr evars
	| Some (Some res) -> transitivity state env avoid res snd

    let choice fst snd : 'a pure_strategy =
      fun state env avoid t ty cstr evars ->
        let state, res = fst state env avoid t ty cstr evars in
	match res with
	| None -> snd state env avoid t ty cstr evars
	| res -> state, res

    let try_ str : 'a pure_strategy = choice str id

    let fix (f : 'a pure_strategy -> 'a pure_strategy) : 'a pure_strategy =
      let rec aux state env avoid t ty cstr evars =
        f aux state env avoid t ty cstr evars
      in aux

    let any (s : 'a pure_strategy) : 'a pure_strategy =
      fix (fun any -> try_ (seq s any))

    let repeat (s : 'a pure_strategy) : 'a pure_strategy =
      seq s (any s)

    let bu (s : 'a pure_strategy) : 'a pure_strategy =
      fix (fun s' -> seq (choice (progress (all_subterms s')) s) (try_ s'))

    let td (s : 'a pure_strategy) : 'a pure_strategy =
      fix (fun s' -> seq (choice s (progress (all_subterms s'))) (try_ s'))

    let innermost (s : 'a pure_strategy) : 'a pure_strategy =
      fix (fun ins -> choice (one_subterm ins) s)

    let outermost (s : 'a pure_strategy) : 'a pure_strategy =
      fix (fun out -> choice s (one_subterm out))

    let lemmas flags cs : 'a pure_strategy =
      List.fold_left (fun tac (l,l2r,by) ->
	choice tac (apply_lemma flags l l2r by AllOccurrences))
	fail cs

    let old_hints (db : string) : 'a pure_strategy =
      let rules = Autorewrite.find_rewrites db in
	lemmas rewrite_unif_flags
	  (List.map (fun hint -> ((hint.Autorewrite.rew_lemma, NoBindings), hint.Autorewrite.rew_l2r, hint.Autorewrite.rew_tac)) rules)

    let hints (db : string) : 'a pure_strategy =
      fun state env avoid t ty cstr evars ->
      let rules = Autorewrite.find_matches db t in
      let lemma hint = ((hint.Autorewrite.rew_lemma, NoBindings), hint.Autorewrite.rew_l2r,
			hint.Autorewrite.rew_tac) in
      let lems = List.map lemma rules in
	lemmas rewrite_unif_flags lems state env avoid t ty cstr evars

    let reduce (r : Redexpr.red_expr) : 'a pure_strategy =
      fun state env avoid t ty cstr evars ->
        let rfn, ckind = Redexpr.reduction_of_red_expr env r in
	  let t' = rfn env (goalevars evars) t in
	    if eq_constr t' t then
	      state, Some None
	    else
	      state, Some (Some { rew_car = ty; rew_from = t; rew_to = t';
			   rew_prf = RewCast ckind; rew_evars = evars })
	
    let fold c : 'a pure_strategy =
      fun state env avoid t ty cstr evars ->
(* 	let sigma, (c,_) = Tacinterp.interp_open_constr_with_bindings is env (goalevars evars) c in *)
	let sigma, c = Constrintern.interp_open_constr (goalevars evars) env c in
	let unfolded =
	  try Tacred.try_red_product env sigma c
	  with e when Errors.noncritical e ->
            error "fold: the term is not unfoldable !"
	in
	  try
	    let sigma = Unification.w_unify env sigma CONV ~flags:Unification.elim_flags unfolded t in
	    let c' = Evarutil.nf_evar sigma c in
	      state, Some (Some { rew_car = ty; rew_from = t; rew_to = c';
			   rew_prf = RewCast DEFAULTcast; 
			   rew_evars = sigma, cstrevars evars })
	  with e when Errors.noncritical e -> state, None

    let fold_glob c : 'a pure_strategy =
      fun state env avoid t ty cstr evars ->
(* 	let sigma, (c,_) = Tacinterp.interp_open_constr_with_bindings is env (goalevars evars) c in *)
	let sigma, c = Pretyping.understand_tcc (goalevars evars) env c in
	let unfolded =
	  try Tacred.try_red_product env sigma c
	  with e when Errors.noncritical e ->
            error "fold: the term is not unfoldable !"
	in
	  try
	    let sigma = Unification.w_unify env sigma CONV ~flags:Unification.elim_flags unfolded t in
	    let c' = Evarutil.nf_evar sigma c in
	      state, Some (Some { rew_car = ty; rew_from = t; rew_to = c';
			   rew_prf = RewCast DEFAULTcast; 
			   rew_evars = sigma, cstrevars evars })
	  with e when Errors.noncritical e -> state, None
  

end

(** The strategy for a single rewrite, dealing with occurences. *)

let rewrite_strat flags occs : (hypinfo * int) pure_strategy =
  let app = apply_rule None occs in
  Strategies.fix (fun aux -> Strategies.choice app (subterm true flags aux))

let get_hypinfo_ids {c = opt} =
  match opt with
  | None -> []
  | Some (is, gc) ->
    let avoid = Option.default [] (TacStore.get is.extra f_avoid_ids) in
    Id.Map.fold (fun id _ accu -> id :: accu) is.lfun avoid

let rewrite_with flags c left2right loccs : strategy =
  fun () env avoid t ty cstr evars ->
    let gevars = goalevars evars in
    let hypinfo = decompose_applied_relation_expr env gevars flags c left2right in
    let avoid = get_hypinfo_ids hypinfo @ avoid in
    let _, res = rewrite_strat default_flags loccs (hypinfo, 0) env avoid t ty cstr (gevars, cstrevars evars) in
    ((), res)

let apply_strategy (s : strategy) env avoid concl cstr evars =
  let _, res =
    s () env avoid concl (Typing.type_of env (goalevars evars) concl)
      (Option.map snd cstr) evars
  in
    match res with
    | None -> None
    | Some None -> Some None
    | Some (Some res) ->
	Some (Some (res.rew_prf, res.rew_evars, res.rew_car, res.rew_from, res.rew_to))

let solve_constraints env evars =
  Typeclasses.resolve_typeclasses env ~split:false ~fail:true evars

let nf_zeta =
  Reductionops.clos_norm_flags (Closure.RedFlags.mkflags [Closure.RedFlags.fZETA])

let map_rewprf f = function
  | RewPrf (rel, prf) -> RewPrf (f rel, f prf)
  | RewCast c -> RewCast c

exception RewriteFailure of std_ppcmds

type result = (evar_map * constr option * types) option option

let cl_rewrite_clause_aux ?(abs=None) strat env avoid sigma concl is_hyp : result =
  let cstr =
    let sort = mkProp in
    let impl = Lazy.force impl in
      match is_hyp with
      | None -> (sort, inverse sort impl)
      | Some _ -> (sort, impl)
  in
  let evars = (sigma, Evar.Set.empty) in
  let eq = apply_strategy strat env avoid concl (Some cstr) evars in
    match eq with
    | Some (Some (p, (evars, cstrs), car, oldt, newt)) ->
	let evars' = solve_constraints env evars in
	let p = map_rewprf (fun p -> nf_zeta env evars' (Evarutil.nf_evar evars' p)) p in
	let newt = Evarutil.nf_evar evars' newt in
	let abs = Option.map (fun (x, y) ->
				Evarutil.nf_evar evars' x, Evarutil.nf_evar evars' y) abs in
	let evars = (* Keep only original evars (potentially instantiated) and goal evars,
		       the rest has been defined and substituted already. *)
	  Evd.fold (fun ev evi acc -> 
	    if Evar.Set.mem ev cstrs then Evd.remove acc ev
	    else acc) evars' evars'
	in
	let res =
	  match is_hyp with
	  | Some id ->
	      (match p with
	       | RewPrf (rel, p) ->
		   let term =
		     match abs with
		     | None -> p
		     | Some (t, ty) ->
			 mkApp (mkLambda (Name (Id.of_string "lemma"), ty, p), [| t |])
		   in
		     Some (evars, Some (mkApp (term, [| mkVar id |])), newt)
	       | RewCast c ->
		   Some (evars, None, newt))
		
	  | None ->
	      (match p with
	       | RewPrf (rel, p) ->
		   (match abs with
		    | None -> Some (evars, Some p, newt)
		    | Some (t, ty) ->
			let proof = mkApp (mkLambda (Name (Id.of_string "lemma"), ty, p), [| t |]) in
			  Some (evars, Some proof, newt))
	       | RewCast c -> Some (evars, None, newt))
	in Some res
    | Some None -> Some None
    | None -> None

(** ppedrot: this is a workaround. The current implementation of rewrite leaks
    evar maps. We know that we should not produce effects in here, so we reput
    them after computing... *)
let tclEFFECT (tac : tactic) : tactic = fun gl ->
  let eff = Evd.eval_side_effects gl.sigma in
  let gls = tac gl in
  let sigma = Evd.emit_side_effects eff (Evd.drop_side_effects gls.sigma) in
  { gls with sigma; }

let cl_rewrite_clause_tac ?abs strat clause gl =
  let evartac evd = Refiner.tclEVARS evd in
  let treat res =
    match res with
    | None -> tclFAIL 0 (str "Nothing to rewrite")
    | Some None ->
	tclFAIL 0 (str"No progress made")
    | Some (Some (undef, p, newt)) ->
	let tac = 
	  match clause, p with
	  | Some id, Some p ->
	      cut_replacing id newt (Tacmach.refine p)
	  | Some id, None -> 
	      change_in_hyp None newt (id, InHypTypeOnly)
	  | None, Some p ->
	      let name = next_name_away_with_default "H" Anonymous (pf_ids_of_hyps gl) in
		tclTHENLAST
		  (Tacmach.internal_cut_no_check false name newt)
		  (tclTHEN (Tactics.revert [name]) (Tacmach.refine p))
	  | None, None -> change_in_concl None newt
	in tclTHEN (evartac undef) tac
  in
  let tac =
    try
      let concl, is_hyp =
	match clause with
	| Some id -> pf_get_hyp_typ gl id, Some id
	| None -> pf_concl gl, None
      in
      let sigma = project gl in
      let concl = Evarutil.nf_evar sigma concl in 
      let res = cl_rewrite_clause_aux ?abs strat (pf_env gl) [] sigma concl is_hyp in
	treat res
    with
    | TypeClassError (env, (UnsatisfiableConstraints _ as e)) ->
	Refiner.tclFAIL 0
	  (str"Unable to satisfy the rewriting constraints."
	   ++ fnl () ++ Himsg.explain_typeclass_error env e)
  in tclEFFECT tac gl


let bind_gl_info f =
  bind concl (fun c -> bind env (fun v -> bind defs (fun ev -> f c v ev))) 

let fail l s = Refiner.tclFAIL l s

let new_refine c : Goal.subgoals Goal.sensitive =
  let refable = Goal.Refinable.make
    (fun handle -> Goal.Refinable.constr_of_open_constr handle true c) 
  in Goal.bind refable Goal.refine

let assert_replacing id newt tac = 
  let sens = bind_gl_info 
    (fun concl env sigma ->
       let nc' = 
	 Environ.fold_named_context
	   (fun _ (n, b, t as decl) nc' ->
	      if Id.equal n id then (n, b, newt) :: nc'
	      else decl :: nc')
	   env ~init:[]
       in
       let reft = Refinable.make 
	 (fun h -> 
	    Goal.bind (Refinable.mkEvar h
			 (Environ.reset_with_named_context (val_of_named_context nc') env) concl)
	      (fun ev -> 
		 Goal.bind (Refinable.mkEvar h env newt)
		   (fun ev' ->
		      let inst = 
			fold_named_context
			  (fun _ (n, b, t) inst ->
			     if Id.equal n id then ev' :: inst
			     else if Option.is_empty b then mkVar n :: inst else inst)
			  env ~init:[]
		      in
		      let (e, args) = destEvar ev in
			Goal.return 
                         (mkEvar (e, Array.of_list inst)))))
       in Goal.bind reft Goal.refine)
  in Proofview.tclTHEN (Proofview.tclSENSITIVE sens) 
       (Proofview.tclFOCUS 2 2 tac)

let newfail n s = 
  Proofview.tclZERO (Refiner.FailError (n, lazy s))

let cl_rewrite_clause_newtac ?abs strat clause =
  let treat (res, is_hyp) = 
    match res with
    | None -> newfail 0 (str "Nothing to rewrite")
    | Some None ->
	newfail 0 (str"No progress made")
    | Some (Some res) ->
	match is_hyp, res with
	| Some id, (undef, Some p, newt) ->
	    assert_replacing id newt (Proofview.tclSENSITIVE (new_refine (undef, p)))
	| Some id, (undef, None, newt) -> 
	    Proofview.tclSENSITIVE (Goal.convert_hyp false (id, None, newt))
	| None, (undef, Some p, newt) ->
	    let refable = Goal.Refinable.make
	      (fun handle -> 
		 Goal.bind env
		   (fun env -> Goal.bind (Refinable.mkEvar handle env newt)
		      (fun ev ->
			 Goal.Refinable.constr_of_open_constr handle true 
			   (undef, mkApp (p, [| ev |])))))
	    in
	      Proofview.tclSENSITIVE (Goal.bind refable Goal.refine)
	| None, (undef, None, newt) ->
	    Proofview.tclSENSITIVE (Goal.convert_concl false newt)
  in
  let info =
    bind_gl_info
      (fun concl env sigma ->
	 let ty, is_hyp =
	   match clause with
	   | Some id -> Environ.named_type id env, Some id
	   | None -> concl, None
	 in
	   try 
	     let res = 
	       cl_rewrite_clause_aux ?abs strat env [] sigma ty is_hyp 
	     in return (res, is_hyp)
	   with
	   | TypeClassError (env, (UnsatisfiableConstraints _ as e)) ->
	     raise (RewriteFailure (str"Unable to satisfy the rewriting constraints."
			++ fnl () ++ Himsg.explain_typeclass_error env e)))
  in
  Proofview.tclGOALBINDU info (fun i -> treat i)
  
let newtactic_init_setoid () = 
  try init_setoid (); Proofview.tclUNIT ()
  with e when Errors.noncritical e -> Proofview.tclZERO e

let tactic_init_setoid () = 
  init_setoid (); tclIDTAC
  
let cl_rewrite_clause_new_strat ?abs strat clause =
  Proofview.tclTHEN (newtactic_init_setoid ())
  (try cl_rewrite_clause_newtac ?abs strat clause
   with RewriteFailure s ->
   newfail 0 (str"setoid rewrite failed: " ++ s))

let cl_rewrite_clause_newtac' l left2right occs clause =
  Proof_global.with_current_proof (fun _ -> Proof.run_tactic (Global.env ())
    (Proofview.tclFOCUS 1 1 
       (cl_rewrite_clause_new_strat (rewrite_with rewrite_unif_flags l left2right occs) clause)))

let cl_rewrite_clause_strat strat clause =
  tclTHEN (tactic_init_setoid ())
  (fun gl -> 
     (*     let gl = { gl with sigma = Typeclasses.mark_unresolvables gl.sigma } in *)
     try cl_rewrite_clause_tac strat clause gl
     with RewriteFailure e ->
       tclFAIL 0 (str"setoid rewrite failed: " ++ e) gl
     | Refiner.FailError (n, pp) -> 
       tclFAIL n (str"setoid rewrite failed: " ++ Lazy.force pp) gl)

let cl_rewrite_clause l left2right occs clause gl =
  cl_rewrite_clause_strat (rewrite_with (general_rewrite_unif_flags ()) l left2right occs) clause gl


let occurrences_of = function
  | n::_ as nl when n < 0 -> (false,List.map abs nl)
  | nl ->
      if List.exists (fun n -> n < 0) nl then
	error "Illegal negative occurrence number.";
      (true,nl)

open Extraargs

let apply_glob_constr c l2r occs = fun () env avoid t ty cstr evars ->
  let evd, c = (Pretyping.understand_tcc (goalevars evars) env c) in
    apply_lemma (general_rewrite_unif_flags ()) (c, NoBindings)
      l2r None occs () env avoid t ty cstr (evd, cstrevars evars)

let interp_glob_constr_list env sigma cl =
  let understand sigma (c, _) =
    let sigma, c = Pretyping.understand_tcc sigma env c in
    (sigma, ((c, NoBindings), true, None))
  in
  List.fold_map understand sigma cl

type ('constr,'redexpr) strategy_ast = 
  | StratId | StratFail | StratRefl
  | StratUnary of string * ('constr,'redexpr) strategy_ast
  | StratBinary of string * ('constr,'redexpr) strategy_ast * ('constr,'redexpr) strategy_ast
  | StratConstr of 'constr * bool
  | StratTerms of 'constr list
  | StratHints of bool * string
  | StratEval of 'redexpr 
  | StratFold of 'constr

let rec map_strategy (f : 'a -> 'a2) (g : 'b -> 'b2) : ('a,'b) strategy_ast -> ('a2,'b2) strategy_ast = function
  | StratId | StratFail | StratRefl as s -> s
  | StratUnary (s, str) -> StratUnary (s, map_strategy f g str)
  | StratBinary (s, str, str') -> StratBinary (s, map_strategy f g str, map_strategy f g str')
  | StratConstr (c, b) -> StratConstr (f c, b)
  | StratTerms l -> StratTerms (List.map f l)
  | StratHints (b, id) -> StratHints (b, id)
  | StratEval r -> StratEval (g r)
  | StratFold c -> StratFold (f c)

let rec strategy_of_ast = function
  | StratId -> Strategies.id
  | StratFail -> Strategies.fail
  | StratRefl -> Strategies.refl
  | StratUnary (f, s) -> 
    let s' = strategy_of_ast s in
    let f' = match f with
      | "subterms" -> all_subterms
      | "subterm" -> one_subterm
      | "innermost" -> Strategies.innermost
      | "outermost" -> Strategies.outermost
      | "bottomup" -> Strategies.bu
      | "topdown" -> Strategies.td
      | "progress" -> Strategies.progress
      | "try" -> Strategies.try_
      | "any" -> Strategies.any
      | "repeat" -> Strategies.repeat
      | _ -> anomaly ~label:"strategy_of_ast" (str"Unkwnon strategy: " ++ str f)
    in f' s'
  | StratBinary (f, s, t) ->
    let s' = strategy_of_ast s in
    let t' = strategy_of_ast t in
    let f' = match f with
      | "compose" -> Strategies.seq
      | "choice" -> Strategies.choice
      | _ -> anomaly ~label:"strategy_of_ast" (str"Unkwnon strategy: " ++ str f)
    in f' s' t'
  | StratConstr (c, b) -> apply_glob_constr (fst c) b AllOccurrences
  | StratHints (old, id) -> if old then Strategies.old_hints id else Strategies.hints id
  | StratTerms l -> 
    (fun () env avoid t ty cstr (evars, cstrs) ->
     let evars, cl = interp_glob_constr_list env evars l in
       Strategies.lemmas rewrite_unif_flags cl () env avoid t ty cstr (evars, cstrs))
  | StratEval r -> 
    (fun () env avoid t ty cstr evars ->
     let (sigma,r_interp) = Tacinterp.interp_redexp env (goalevars evars) r in
       Strategies.reduce r_interp () env avoid t ty cstr (sigma,cstrevars evars))
  | StratFold c -> Strategies.fold_glob (fst c)


let mkappc s l = CAppExpl (Loc.ghost,(None,(Libnames.Ident (Loc.ghost,Id.of_string s))),l)

let declare_an_instance n s args =
  ((Loc.ghost,Name n), Explicit,
  CAppExpl (Loc.ghost, (None, Qualid (Loc.ghost, qualid_of_string s)),
	   args))

let declare_instance a aeq n s = declare_an_instance n s [a;aeq]

let anew_instance global binders instance fields =
  new_instance binders instance (Some (CRecord (Loc.ghost,None,fields)))
    ~global ~generalize:false None

let declare_instance_refl global binders a aeq n lemma =
  let instance = declare_instance a aeq (add_suffix n "_Reflexive") "Coq.Classes.RelationClasses.Reflexive"
  in anew_instance global binders instance
       [(Ident (Loc.ghost,Id.of_string "reflexivity"),lemma)]

let declare_instance_sym global binders a aeq n lemma =
  let instance = declare_instance a aeq (add_suffix n "_Symmetric") "Coq.Classes.RelationClasses.Symmetric"
  in anew_instance global binders instance
       [(Ident (Loc.ghost,Id.of_string "symmetry"),lemma)]

let declare_instance_trans global binders a aeq n lemma =
  let instance = declare_instance a aeq (add_suffix n "_Transitive") "Coq.Classes.RelationClasses.Transitive"
  in anew_instance global binders instance
       [(Ident (Loc.ghost,Id.of_string "transitivity"),lemma)]

let declare_relation ?(binders=[]) a aeq n refl symm trans =
  init_setoid ();
  let global = not (Locality.make_section_locality (Locality.LocalityFixme.consume ())) in
  let instance = declare_instance a aeq (add_suffix n "_relation") "Coq.Classes.RelationClasses.RewriteRelation"
  in ignore(anew_instance global binders instance []);
  match (refl,symm,trans) with
      (None, None, None) -> ()
    | (Some lemma1, None, None) ->
	ignore (declare_instance_refl global binders a aeq n lemma1)
    | (None, Some lemma2, None) ->
	ignore (declare_instance_sym global binders a aeq n lemma2)
    | (None, None, Some lemma3) ->
	ignore (declare_instance_trans global binders a aeq n lemma3)
    | (Some lemma1, Some lemma2, None) ->
	ignore (declare_instance_refl global binders a aeq n lemma1);
	ignore (declare_instance_sym global binders a aeq n lemma2)
    | (Some lemma1, None, Some lemma3) ->
	let _lemma_refl = declare_instance_refl global binders a aeq n lemma1 in
	let _lemma_trans = declare_instance_trans global binders a aeq n lemma3 in
	let instance = declare_instance a aeq n "Coq.Classes.RelationClasses.PreOrder"
	in ignore(
	    anew_instance global binders instance
	      [(Ident (Loc.ghost,Id.of_string "PreOrder_Reflexive"), lemma1);
	       (Ident (Loc.ghost,Id.of_string "PreOrder_Transitive"),lemma3)])
    | (None, Some lemma2, Some lemma3) ->
	let _lemma_sym = declare_instance_sym global binders a aeq n lemma2 in
	let _lemma_trans = declare_instance_trans global binders a aeq n lemma3 in
	let instance = declare_instance a aeq n "Coq.Classes.RelationClasses.PER"
	in ignore(
	    anew_instance global binders instance
	      [(Ident (Loc.ghost,Id.of_string "PER_Symmetric"), lemma2);
	       (Ident (Loc.ghost,Id.of_string "PER_Transitive"),lemma3)])
     | (Some lemma1, Some lemma2, Some lemma3) ->
	let _lemma_refl = declare_instance_refl global binders a aeq n lemma1 in
	let _lemma_sym = declare_instance_sym global binders a aeq n lemma2 in
	let _lemma_trans = declare_instance_trans global binders a aeq n lemma3 in
	let instance = declare_instance a aeq n "Coq.Classes.RelationClasses.Equivalence"
	in ignore(
	  anew_instance global binders instance
	    [(Ident (Loc.ghost,Id.of_string "Equivalence_Reflexive"), lemma1);
	     (Ident (Loc.ghost,Id.of_string "Equivalence_Symmetric"), lemma2);
	     (Ident (Loc.ghost,Id.of_string "Equivalence_Transitive"), lemma3)])

let cHole = CHole (Loc.ghost, None)

let proper_projection r ty =
  let ctx, inst = decompose_prod_assum ty in
  let mor, args = destApp inst in
  let instarg = mkApp (r, rel_vect 0 (List.length ctx)) in
  let app = mkApp (Lazy.force proper_proj,
		  Array.append args [| instarg |]) in
    it_mkLambda_or_LetIn app ctx

let declare_projection n instance_id r =
  let ty = Global.type_of_global r in
  let c = constr_of_global r in
  let term = proper_projection c ty in
  let env = Global.env() in
  let typ = Typing.type_of env Evd.empty term in
  let ctx, typ = decompose_prod_assum typ in
  let typ =
    let n =
      let rec aux t =
	match kind_of_term t with
	    App (f, [| a ; a' ; rel; rel' |]) when eq_constr f (Lazy.force respectful) ->
	      succ (aux rel')
	  | _ -> 0
      in
      let init =
	match kind_of_term typ with
	    App (f, args) when eq_constr f (Lazy.force respectful) ->
	      mkApp (f, fst (Array.chop (Array.length args - 2) args))
	  | _ -> typ
      in aux init
    in
    let ctx,ccl = Reductionops.splay_prod_n env Evd.empty (3 * n) typ
    in it_mkProd_or_LetIn ccl ctx
  in
  let typ = it_mkProd_or_LetIn typ ctx in
  let cst =
    { const_entry_body = Future.from_val (term,Declareops.no_seff);
      const_entry_secctx = None;
      const_entry_type = Some typ;
      const_entry_opaque = false;
      const_entry_inline_code = false }
  in
    ignore(Declare.declare_constant n (Entries.DefinitionEntry cst, Decl_kinds.IsDefinition Decl_kinds.Definition))

let build_morphism_signature m =
  let env = Global.env () in
  let m = Constrintern.interp_constr Evd.empty env m in
  let t = Typing.type_of env Evd.empty m in
  let evdref = ref (Evd.empty, Evar.Set.empty) in
  let cstrs =
    let rec aux t =
      match kind_of_term t with
	| Prod (na, a, b) ->
	    None :: aux b
	| _ -> []
    in aux t
  in
  let evars, t', sig_, cstrs = build_signature !evdref env t cstrs None in
  let _ = evdref := evars in
  let _ = List.iter
    (fun (ty, rel) ->
      Option.iter (fun rel ->
	let default = mkApp (Lazy.force default_relation, [| ty; rel |]) in
	let evars,c = new_cstr_evar !evdref env default in
	  evdref := evars)
	rel)
    cstrs
  in
  let morph =
    mkApp (Lazy.force proper_type, [| t; sig_; m |])
  in
  let evd = solve_constraints env (goalevars !evdref) in
  let m = Evarutil.nf_evar evd morph in
    Evarutil.check_evars env Evd.empty evd m; m

let default_morphism sign m =
  let env = Global.env () in
  let t = Typing.type_of env Evd.empty m in
  let evars, _, sign, cstrs =
    build_signature (Evd.empty, Evar.Set.empty) env t (fst sign) (snd sign)
  in
  let morph =
    mkApp (Lazy.force proper_type, [| t; sign; m |])
  in
  let evars, mor = resolve_one_typeclass env (fst evars) morph in
    mor, proper_projection mor morph

let add_setoid global binders a aeq t n =
  init_setoid ();
  let _lemma_refl = declare_instance_refl global binders a aeq n (mkappc "Seq_refl" [a;aeq;t]) in
  let _lemma_sym = declare_instance_sym global binders a aeq n (mkappc "Seq_sym" [a;aeq;t]) in
  let _lemma_trans = declare_instance_trans global binders a aeq n (mkappc "Seq_trans" [a;aeq;t]) in
  let instance = declare_instance a aeq n "Coq.Classes.RelationClasses.Equivalence"
  in ignore(
    anew_instance global binders instance
      [(Ident (Loc.ghost,Id.of_string "Equivalence_Reflexive"), mkappc "Seq_refl" [a;aeq;t]);
       (Ident (Loc.ghost,Id.of_string "Equivalence_Symmetric"), mkappc "Seq_sym" [a;aeq;t]);
       (Ident (Loc.ghost,Id.of_string "Equivalence_Transitive"), mkappc "Seq_trans" [a;aeq;t])])

let make_tactic name =
  let open Tacexpr in
  let loc = Loc.ghost in
  let tacpath = Libnames.qualid_of_string name in
  let tacname = Qualid (loc, tacpath) in
  TacArg (loc, TacCall (loc, tacname, []))

let add_morphism_infer glob m n =
  init_setoid ();
  let instance_id = add_suffix n "_Proper" in
  let instance = build_morphism_signature m in
    if Lib.is_modtype () then
      let cst = Declare.declare_constant ~internal:Declare.KernelSilent instance_id
				(Entries.ParameterEntry (None,instance,None), Decl_kinds.IsAssumption Decl_kinds.Logical)
      in
	add_instance (Typeclasses.new_instance (Lazy.force proper_class) None glob (ConstRef cst));
	declare_projection n instance_id (ConstRef cst)
    else
      let kind = Decl_kinds.Global, Decl_kinds.DefinitionBody Decl_kinds.Instance in
      let tac = make_tactic "Coq.Classes.SetoidTactics.add_morphism_tactic" in
	Flags.silently
	  (fun () ->
	    Lemmas.start_proof instance_id kind instance
	      (fun _ -> function
		Globnames.ConstRef cst ->
		  add_instance (Typeclasses.new_instance (Lazy.force proper_class) None
				   glob (ConstRef cst));
		  declare_projection n instance_id (ConstRef cst)
		| _ -> assert false);
	    Pfedit.by (Tacinterp.interp tac)) ()

let add_morphism glob binders m s n =
  init_setoid ();
  let instance_id = add_suffix n "_Proper" in
  let instance =
    ((Loc.ghost,Name instance_id), Explicit,
    CAppExpl (Loc.ghost,
	     (None, Qualid (Loc.ghost, Libnames.qualid_of_string "Coq.Classes.Morphisms.Proper")),
	     [cHole; s; m]))
  in
  let tac = Tacinterp.interp (make_tactic "add_morphism_tactic") in
    ignore(new_instance ~global:glob binders instance (Some (CRecord (Loc.ghost,None,[])))
	      ~generalize:false ~tac ~hook:(declare_projection n instance_id) None)

(** Bind to "rewrite" too *)

(** Taken from original setoid_replace, to emulate the old rewrite semantics where
    lemmas are first instantiated and then rewrite proceeds. *)

let check_evar_map_of_evars_defs evd =
 let metas = Evd.meta_list evd in
 let check_freemetas_is_empty rebus =
  Evd.Metaset.iter
   (fun m ->
     if Evd.meta_defined evd m then () else
      raise
	(Logic.RefinerError (Logic.UnresolvedBindings [Evd.meta_name evd m])))
 in
  List.iter
   (fun (_,binding) ->
     match binding with
        Evd.Cltyp (_,{Evd.rebus=rebus; Evd.freemetas=freemetas}) ->
         check_freemetas_is_empty rebus freemetas
      | Evd.Clval (_,({Evd.rebus=rebus1; Evd.freemetas=freemetas1},_),
                 {Evd.rebus=rebus2; Evd.freemetas=freemetas2}) ->
         check_freemetas_is_empty rebus1 freemetas1 ;
         check_freemetas_is_empty rebus2 freemetas2
   ) metas

let unification_rewrite flags l2r c1 c2 cl car rel but gl =
  let env = pf_env gl in
  let (evd',c') =
    try
      (* ~flags:(false,true) to allow to mark occurrences that must not be
         rewritten simply by replacing them with let-defined definitions
         in the context *)
      Unification.w_unify_to_subterm 
       ~flags:{ rewrite_unif_flags with Unification.resolve_evars = true } env
        cl.evd ((if l2r then c1 else c2),but)
    with
	Pretype_errors.PretypeError _ ->
	  (* ~flags:(true,true) to make Ring work (since it really
             exploits conversion) *)
	  Unification.w_unify_to_subterm 
	  ~flags:{ flags with Unification.resolve_evars = true }
	    env cl.evd ((if l2r then c1 else c2),but)
  in
  let cl' = {cl with evd = evd'} in
  let cl' = Clenvtac.clenv_pose_dependent_evars true cl' in
  let nf c = Evarutil.nf_evar cl'.evd (Clenv.clenv_nf_meta cl' c) in
  let c1 = if l2r then nf c' else nf c1
  and c2 = if l2r then nf c2 else nf c'
  and car = nf car and rel = nf rel in
  check_evar_map_of_evars_defs cl'.evd;
  let prf = nf (Clenv.clenv_value cl') and prfty = nf (Clenv.clenv_type cl') in
  let cl' = { cl' with templval = mk_freelisted prf ; templtyp = mk_freelisted prfty } in
    {cl=cl'; ext=Evar.Set.empty; prf=(mkRel 1); car=car; rel=rel; l2r=l2r; 
     c1=c1; c2=c2; c=None; abs=Some (prf, prfty); flags = flags}

let get_hyp gl evars (c,l) clause l2r =
  let flags = rewrite2_unif_flags in
  let hi = decompose_applied_relation (pf_env gl) evars flags None (c,l) l2r in
  let but = match clause with
    | Some id -> pf_get_hyp_typ gl id 
    | None -> Evarutil.nf_evar evars (pf_concl gl)
  in
  let rew = unification_rewrite flags hi.l2r hi.c1 hi.c2 hi.cl hi.car hi.rel but gl in
  { rew with flags = rewrite_unif_flags }

let general_rewrite_flags = { under_lambdas = false; on_morphisms = true }

let apply_lemma gl (c,l) cl l2r occs =
  let app = apply_rule None occs in
  Strategies.fix
    (fun aux -> Strategies.choice app (subterm true general_rewrite_flags aux))

let general_s_rewrite cl l2r occs (c,l) ~new_goals gl =
  let sigma = project gl in
  let hypinfo = get_hyp gl sigma (c,l) cl l2r in
  let strat () env avoid t ty cstr evars =
    let _, res = apply_lemma gl (c,l) cl l2r occs (hypinfo, 0) env avoid t ty cstr evars in
    (), res
  in
    try
      (tclWEAK_PROGRESS 
	(tclTHEN
           (Refiner.tclEVARS hypinfo.cl.evd)
	   (cl_rewrite_clause_tac ~abs:hypinfo.abs strat cl))) gl
    with RewriteFailure e ->
      let {l2r=l2r; c1=x; c2=y} = hypinfo in
	raise (Pretype_errors.PretypeError
		  (pf_env gl,project gl,
		  Pretype_errors.NoOccurrenceFound ((if l2r then x else y), cl)))

let general_s_rewrite_clause x =
  init_setoid ();
  match x with
    | None -> general_s_rewrite None
    | Some id -> general_s_rewrite (Some id)

let _ = Hook.set Equality.general_rewrite_clause general_s_rewrite_clause

(** [setoid_]{reflexivity,symmetry,transitivity} tactics *)

let not_declared env ty rel =
  tclFAIL 0 (str" The relation " ++ Printer.pr_constr_env env rel ++ str" is not a declared " ++
		str ty ++ str" relation. Maybe you need to require the Setoid library")

let setoid_proof gl ty fn fallback =
  let env = pf_env gl in
    try
      let rel, args = decompose_app_rel env (project gl) (pf_concl gl) in
      let evm = project gl in
      let car = pi3 (List.hd (fst (Reduction.dest_prod env (Typing.type_of env evm rel)))) in
	fn env evm car rel gl
    with e when Errors.noncritical e ->
      try fallback gl
      with Hipattern.NoEquationFound ->
          let e = Errors.push e in
	  match e with
	  | Not_found ->
	      let rel, args = decompose_app_rel env (project gl) (pf_concl gl) in
		not_declared env ty rel gl
	  | _ -> raise e

let setoid_reflexivity gl =
  setoid_proof gl "reflexive"
    (fun env evm car rel -> apply (get_reflexive_proof env evm car rel))
    (reflexivity_red true)

let setoid_symmetry gl =
  setoid_proof gl "symmetric"
    (fun env evm car rel -> apply (get_symmetric_proof env evm car rel))
    (symmetry_red true)

let setoid_transitivity c gl =
  setoid_proof gl "transitive"
    (fun env evm car rel ->
      let proof = get_transitive_proof env evm car rel in
      match c with
      | None -> eapply proof
      | Some c -> apply_with_bindings (proof,ImplicitBindings [ c ]))
    (transitivity_red true c)

let setoid_symmetry_in id gl =
  let ctype = pf_type_of gl (mkVar id) in
  let binders,concl = decompose_prod_assum ctype in
  let (equiv, args) = decompose_app concl in
  let rec split_last_two = function
    | [c1;c2] -> [],(c1, c2)
    | x::y::z -> let l,res = split_last_two (y::z) in x::l, res
    | _ -> error "The term provided is not an equivalence."
  in
  let others,(c1,c2) = split_last_two args in
  let he,c1,c2 =  mkApp (equiv, Array.of_list others),c1,c2 in
  let new_hyp' =  mkApp (he, [| c2 ; c1 |]) in
  let new_hyp = it_mkProd_or_LetIn new_hyp'  binders in
    tclTHENS (Tactics.cut new_hyp)
      [ intro_replacing id;
	tclTHENLIST [ intros; setoid_symmetry; apply (mkVar id); Tactics.assumption ] ]
      gl

let _ = Hook.set Tactics.setoid_reflexivity setoid_reflexivity
let _ = Hook.set Tactics.setoid_symmetry setoid_symmetry
let _ = Hook.set Tactics.setoid_symmetry_in setoid_symmetry_in
let _ = Hook.set Tactics.setoid_transitivity setoid_transitivity

let implify id gl =
  let (_, b, ctype) = pf_get_hyp gl id in
  let binders,concl = decompose_prod_assum ctype in
  let ctype' =
    match binders with
    | (_, None, ty as hd) :: tl when noccurn 1 concl ->
	let env = Environ.push_rel_context tl (pf_env gl) in
	let sigma = project gl in
	let tyhd = Typing.type_of env sigma ty
	and tyconcl = Typing.type_of (Environ.push_rel hd env) sigma concl in
	let app, unfold = arrow_morphism tyhd (subst1 mkProp tyconcl) ty (subst1 mkProp concl) in
	  it_mkProd_or_LetIn app tl
    | _ -> ctype
  in convert_hyp_no_check (id, b, ctype') gl

let rec fold_matches eff env sigma c =
  map_constr_with_full_binders Environ.push_rel 
    (fun env c ->
      match kind_of_term c with
      | Case _ ->
          let cst, env, c',eff' = fold_match ~force:true env sigma c in
          eff := Declareops.union_side_effects eff' !eff;
          fold_matches eff env sigma c'
      | _ -> fold_matches eff env sigma c)
    env c

let fold_matches_tac c gl =
  let eff = ref Declareops.no_seff in
  let c' = fold_matches eff (pf_env gl) (project gl) c in
  tclTHEN (Tactics.emit_side_effects !eff)
    (change (Some (snd (pattern_of_constr (project gl) c))) c' onConcl) gl

let myapply id l gl =
  let gr = id in
  let _, impls = List.hd (Impargs.implicits_of_global gr) in
  let ty = Global.type_of_global gr in
  let env = pf_env gl in
  let evars = ref (project gl) in
  let app =
    let rec aux ty impls args args' =
      match impls, kind_of_term ty with
      | Some (_, _, (_, _)) :: impls, Prod (n, t, t') ->
          let arg = Evarutil.e_new_evar evars env t in
            aux (subst1 arg t') impls args (arg :: args')
      | None :: impls, Prod (n, t, t') ->
          (match args with
            | [] ->
                if dependent (mkRel 1) t' then
                  let arg = Evarutil.e_new_evar evars env t in
                    aux (subst1 arg t') impls args (arg :: args')
                else
                  let arg = Evarutil.mk_new_meta () in
                    evars := meta_declare (destMeta arg) t !evars;
                    aux (subst1 arg t') impls args (arg :: args')
            | arg :: args -> 
                aux (subst1 arg t') impls args (arg :: args'))
      | _, _ -> mkApp (constr_of_global gr, Array.of_list (List.rev args'))
    in aux ty impls l []
  in
  tclTHEN (Refiner.tclEVARS !evars) (apply app) gl
