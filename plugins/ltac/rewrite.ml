(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open CErrors
open Util
open Names
open Nameops
open Namegen
open Constr
open EConstr
open Vars
open Reduction
open Tacticals.New
open Tactics
open Pretype_errors
open Typeclasses
open Classes
open Constrexpr
open Globnames
open Evd
open Tactypes
open Locus
open Locusops
open Decl_kinds
open Elimschemes
open Environ
open Termops
open EConstr
open Libnames
open Proofview.Notations
open Context.Named.Declaration

module NamedDecl = Context.Named.Declaration
(* module RelDecl = Context.Rel.Declaration *)

(** Typeclass-based generalized rewriting. *)

(** Constants used by the tactic. *)

let classes_dirpath =
  Names.DirPath.make (List.map Id.of_string ["Classes";"Coq"])

let init_relation_classes () =
  if is_dirpath_prefix_of classes_dirpath (Lib.cwd ()) then ()
  else Coqlib.check_required_library ["Coq";"Classes";"RelationClasses"]

let init_setoid () =
  if is_dirpath_prefix_of classes_dirpath (Lib.cwd ()) then ()
  else Coqlib.check_required_library ["Coq";"Setoids";"Setoid"]

let lazy_find_reference dir s =
  let gr = lazy (Coqlib.coq_reference "generalized rewriting" dir s) in
  fun () -> Lazy.force gr

let find_reference dir s = Coqlib.coq_reference "generalized rewriting" dir s

type evars = evar_map * Evar.Set.t (* goal evars, constraint evars *)

let find_global dir s =
  let gr = lazy (find_reference dir s) in
    fun (evd,cstrs) ->
      let (evd, c) = Evarutil.new_global evd (Lazy.force gr) in
	(evd, cstrs), c

(** Utility for dealing with polymorphic applications *)

(** Global constants. *)

let coq_eq_ref = lazy_find_reference ["Init"; "Logic"] "eq"
let coq_eq = find_global ["Init"; "Logic"] "eq"
let coq_f_equal = find_global ["Init"; "Logic"] "f_equal"
let coq_all = find_global ["Init"; "Logic"] "all"
let impl = find_global ["Program"; "Basics"] "impl"

(** Bookkeeping which evars are constraints so that we can 
    remove them at the end of the tactic. *)

let goalevars evars = fst evars
let cstrevars evars = snd evars

let new_cstr_evar (evd,cstrs) env t =
  let s = Typeclasses.set_resolvable Evd.Store.empty false in
  let (evd', t) = Evarutil.new_evar ~store:s env evd t in
  let ev, _ = destEvar evd' t in
    (evd', Evar.Set.add ev cstrs), t

(** Building or looking up instances. *)
let e_new_cstr_evar env evars t =
  let evd', t = new_cstr_evar !evars env t in evars := evd'; t

(** Building or looking up instances. *)

let extends_undefined evars evars' =
  let f ev evi found = found || not (Evd.mem evars ev)
  in fold_undefined f evars' false

let app_poly_check env evars f args =
  let (evars, cstrs), fc = f evars in
  let evars, t = Typing.solve_evars env evars (mkApp (fc, args)) in
  (evars, cstrs), t

let app_poly_nocheck env evars f args =
  let evars, fc = f evars in 
    evars, mkApp (fc, args)

let app_poly_sort b =
  if b then app_poly_nocheck
  else app_poly_check
    
let find_class_proof proof_type proof_method env evars carrier relation =
  try
    let evars, goal = app_poly_check env evars proof_type [| carrier ; relation |] in
    let evars', c = Typeclasses.resolve_one_typeclass env (goalevars evars) goal in
      if extends_undefined (goalevars evars) evars' then raise Not_found
      else app_poly_check env (evars',cstrevars evars) proof_method [| carrier; relation; c |]
  with e when Logic.catchable_exception e -> raise Not_found
 
(** Utility functions *)

module GlobalBindings (M : sig
  val relation_classes : string list
  val morphisms : string list
  val relation : string list * string
  val app_poly : env -> evars -> (evars -> evars * constr) -> constr array -> evars * constr
  val arrow : evars -> evars * constr
end) = struct
  open M
  open Context.Rel.Declaration
  let relation : evars -> evars * constr = find_global (fst relation) (snd relation)

  let reflexive_type = find_global relation_classes "Reflexive"
  let reflexive_proof = find_global relation_classes "reflexivity"
    
  let symmetric_type = find_global relation_classes "Symmetric"
  let symmetric_proof = find_global relation_classes "symmetry"

  let transitive_type = find_global relation_classes "Transitive"
  let transitive_proof = find_global relation_classes "transitivity"

  let forall_relation = find_global morphisms "forall_relation"
  let pointwise_relation = find_global morphisms "pointwise_relation"

  let forall_relation_ref = lazy_find_reference morphisms "forall_relation"
  let pointwise_relation_ref = lazy_find_reference morphisms "pointwise_relation"

  let respectful = find_global morphisms "respectful"
  let respectful_ref = lazy_find_reference morphisms "respectful"

  let default_relation = find_global ["Classes"; "SetoidTactics"] "DefaultRelation"

  let coq_forall = find_global morphisms "forall_def"

  let subrelation = find_global relation_classes "subrelation"
  let do_subrelation = find_global morphisms "do_subrelation"
  let apply_subrelation = find_global morphisms "apply_subrelation"

  let rewrite_relation_class = find_global relation_classes "RewriteRelation"

  let proper_class = lazy (class_info (find_reference morphisms "Proper"))
  let proper_proxy_class = lazy (class_info (find_reference morphisms "ProperProxy"))
    
  let proper_proj = lazy (mkConst (Option.get (pi3 (List.hd (Lazy.force proper_class).cl_projs))))
    
  let proper_type = 
    let l = lazy (Lazy.force proper_class).cl_impl in
      fun (evd,cstrs) -> 
        let (evd, c) = Evarutil.new_global evd (Lazy.force l) in
	  (evd, cstrs), c
	
  let proper_proxy_type = 
    let l = lazy (Lazy.force proper_proxy_class).cl_impl in
      fun (evd,cstrs) -> 
        let (evd, c) = Evarutil.new_global evd (Lazy.force l) in
	  (evd, cstrs), c

  let proper_proof env evars carrier relation x =
    let evars, goal = app_poly env evars proper_proxy_type [| carrier ; relation; x |] in
      new_cstr_evar evars env goal

  let get_reflexive_proof env = find_class_proof reflexive_type reflexive_proof env
  let get_symmetric_proof env = find_class_proof symmetric_type symmetric_proof env
  let get_transitive_proof env = find_class_proof transitive_type transitive_proof env

  let mk_relation env evd a = 
    app_poly env evd relation [| a |]

  (** Build an infered signature from constraints on the arguments and expected output
      relation *)
    
  let build_signature evars env m (cstrs : (types * types option) option list)
      (finalcstr : (types * types option) option) =
    let mk_relty evars newenv ty obj =
      match obj with
      | None | Some (_, None) ->
	let evars, relty = mk_relation env evars ty in
	  if closed0 (goalevars evars) ty then 
	    let env' = Environ.reset_with_named_context (Environ.named_context_val env) env in
	      new_cstr_evar evars env' relty
	  else new_cstr_evar evars newenv relty
      | Some (x, Some rel) -> evars, rel
    in
    let rec aux env evars ty l =
      let t = Reductionops.whd_all env (goalevars evars) ty in
	match EConstr.kind (goalevars evars) t, l with
	| Prod (na, ty, b), obj :: cstrs ->
          let b = Reductionops.nf_betaiota env (goalevars evars) b in
	  if noccurn (goalevars evars) 1 b (* non-dependent product *) then
            let ty = Reductionops.nf_betaiota env (goalevars evars) ty in
	    let (evars, b', arg, cstrs) = aux env evars (subst1 mkProp b) cstrs in
	    let evars, relty = mk_relty evars env ty obj in
	    let evars, newarg = app_poly env evars respectful [| ty ; b' ; relty ; arg |] in
	      evars, mkProd(na, ty, b), newarg, (ty, Some relty) :: cstrs
	  else
	    let (evars, b, arg, cstrs) =
	      aux (push_rel (LocalAssum (na, ty)) env) evars b cstrs
	    in
            let ty = Reductionops.nf_betaiota env (goalevars evars) ty in
	    let pred = mkLambda (na, ty, b) in
	    let liftarg = mkLambda (na, ty, arg) in
	    let evars, arg' = app_poly env evars forall_relation [| ty ; pred ; liftarg |] in
	      if Option.is_empty obj then evars, mkProd(na, ty, b), arg', (ty, None) :: cstrs
	      else user_err Pp.(str "build_signature: no constraint can apply on a dependent argument")
	| _, obj :: _ -> anomaly ~label:"build_signature" (Pp.str "not enough products.")
	| _, [] ->
	  (match finalcstr with
	  | None | Some (_, None) ->
            let t = Reductionops.nf_betaiota env (fst evars) ty in
	    let evars, rel = mk_relty evars env t None in
	      evars, t, rel, [t, Some rel]
	  | Some (t, Some rel) -> evars, t, rel, [t, Some rel])
    in aux env evars m cstrs

  (** Folding/unfolding of the tactic constants. *)

  let unfold_impl sigma t =
    match EConstr.kind sigma t with
    | App (arrow, [| a; b |])(*  when eq_constr arrow (Lazy.force impl) *) ->
      mkProd (Anonymous, a, lift 1 b)
    | _ -> assert false

  let unfold_all sigma t =
    match EConstr.kind sigma t with
    | App (id, [| a; b |]) (* when eq_constr id (Lazy.force coq_all) *) ->
      (match EConstr.kind sigma b with
      | Lambda (n, ty, b) -> mkProd (n, ty, b)
      | _ -> assert false)
    | _ -> assert false

  let unfold_forall sigma t =
    match EConstr.kind sigma t with
    | App (id, [| a; b |]) (* when eq_constr id (Lazy.force coq_all) *) ->
      (match EConstr.kind sigma b with
      | Lambda (n, ty, b) -> mkProd (n, ty, b)
      | _ -> assert false)
    | _ -> assert false

  let arrow_morphism env evd ta tb a b =
    let ap = is_Prop (goalevars evd) ta and bp = is_Prop (goalevars evd) tb in
      if ap && bp then app_poly env evd impl [| a; b |], unfold_impl
      else if ap then (* Domain in Prop, CoDomain in Type *)
	(app_poly env evd arrow [| a; b |]), unfold_impl
	(* (evd, mkProd (Anonymous, a, b)), (fun x -> x) *)
      else if bp then (* Dummy forall *)
	(app_poly env evd coq_all [| a; mkLambda (Anonymous, a, lift 1 b) |]), unfold_forall
      else (* None in Prop, use arrow *)
	(app_poly env evd arrow [| a; b |]), unfold_impl

  let rec decomp_pointwise sigma n c =
    if Int.equal n 0 then c
    else
      match EConstr.kind sigma c with
      | App (f, [| a; b; relb |]) when Termops.is_global sigma (pointwise_relation_ref ()) f ->
	decomp_pointwise sigma (pred n) relb
      | App (f, [| a; b; arelb |]) when Termops.is_global sigma (forall_relation_ref ()) f ->
	decomp_pointwise sigma (pred n) (Reductionops.beta_applist sigma (arelb, [mkRel 1]))
      | _ -> invalid_arg "decomp_pointwise"

  let rec apply_pointwise sigma rel = function
    | arg :: args ->
      (match EConstr.kind sigma rel with
      | App (f, [| a; b; relb |]) when Termops.is_global sigma (pointwise_relation_ref ()) f ->
	apply_pointwise sigma relb args
      | App (f, [| a; b; arelb |]) when Termops.is_global sigma (forall_relation_ref ()) f ->
	apply_pointwise sigma (Reductionops.beta_applist sigma (arelb, [arg])) args
      | _ -> invalid_arg "apply_pointwise")
    | [] -> rel

  let pointwise_or_dep_relation env evd n t car rel =
    if noccurn (goalevars evd) 1 car && noccurn (goalevars evd) 1 rel then
      app_poly env evd pointwise_relation [| t; lift (-1) car; lift (-1) rel |]
    else
      app_poly env evd forall_relation
	[| t; mkLambda (n, t, car); mkLambda (n, t, rel) |]

  let lift_cstr env evars (args : constr list) c ty cstr =
    let start evars env car =
      match cstr with
      | None | Some (_, None) -> 
	let evars, rel = mk_relation env evars car in
	  new_cstr_evar evars env rel
      | Some (ty, Some rel) -> evars, rel
    in
    let rec aux evars env prod n = 
      if Int.equal n 0 then start evars env prod
      else
        let sigma = goalevars evars in
	match EConstr.kind sigma (Reductionops.whd_all env sigma prod) with
	| Prod (na, ty, b) ->
	  if noccurn sigma 1 b then
	    let b' = lift (-1) b in
	    let evars, rb = aux evars env b' (pred n) in
	      app_poly env evars pointwise_relation [| ty; b'; rb |]
	  else
	    let evars, rb = aux evars (push_rel (LocalAssum (na, ty)) env) b (pred n) in
	      app_poly env evars forall_relation
		[| ty; mkLambda (na, ty, b); mkLambda (na, ty, rb) |]
	| _ -> raise Not_found
    in 
    let rec find env c ty = function
      | [] -> None
      | arg :: args ->
	try let evars, found = aux evars env ty (succ (List.length args)) in
	      Some (evars, found, c, ty, arg :: args)
	with Not_found ->
          let sigma = goalevars evars in
	  let ty = Reductionops.whd_all env sigma ty in
	  find env (mkApp (c, [| arg |])) (prod_applist sigma ty [arg]) args
    in find env c ty args

  let unlift_cstr env sigma = function
    | None -> None
    | Some codom -> Some (decomp_pointwise (goalevars sigma) 1 codom)

  (** Looking up declared rewrite relations (instances of [RewriteRelation]) *)
  let is_applied_rewrite_relation env sigma rels t =
    match EConstr.kind sigma t with
    | App (c, args) when Array.length args >= 2 ->
      let head = if isApp sigma c then fst (destApp sigma c) else c in
	if Termops.is_global sigma (coq_eq_ref ()) head then None
	else
	  (try
	   let params, args = Array.chop (Array.length args - 2) args in
	   let env' = push_rel_context rels env in
	   let (evars, (evar, _)) = Evarutil.new_type_evar env' sigma Evd.univ_flexible in
	   let evars, inst = 
	     app_poly env (evars,Evar.Set.empty)
	       rewrite_relation_class [| evar; mkApp (c, params) |] in
	   let _ = Typeclasses.resolve_one_typeclass env' (goalevars evars) inst in
	     Some (it_mkProd_or_LetIn t rels)
	   with e when CErrors.noncritical e -> None)
  | _ -> None


end

(* let my_type_of env evars c = Typing.e_type_of env evars c *)
(* let mytypeofkey = CProfile.declare_profile "my_type_of";; *)
(* let my_type_of = CProfile.profile3 mytypeofkey my_type_of *)


let type_app_poly env env evd f args =
  let evars, c = app_poly_nocheck env evd f args in
  let evd', t = Typing.type_of env (goalevars evars) c in
    (evd', cstrevars evars), c

module PropGlobal = struct
  module Consts =
  struct 
    let relation_classes = ["Classes"; "RelationClasses"]
    let morphisms = ["Classes"; "Morphisms"]
    let relation = ["Relations";"Relation_Definitions"], "relation"
    let app_poly = app_poly_nocheck
    let arrow = find_global ["Program"; "Basics"] "arrow"
    let coq_inverse = find_global ["Program"; "Basics"] "flip"
  end

  module G = GlobalBindings(Consts)

  include G
  include Consts
  let inverse env evd car rel = 
    type_app_poly env env evd coq_inverse [| car ; car; mkProp; rel |]
      (* app_poly env evd coq_inverse [| car ; car; mkProp; rel |] *)

end

module TypeGlobal = struct
  module Consts = 
    struct 
      let relation_classes = ["Classes"; "CRelationClasses"]
      let morphisms = ["Classes"; "CMorphisms"]
      let relation = relation_classes, "crelation"
      let app_poly = app_poly_check
      let arrow = find_global ["Classes"; "CRelationClasses"] "arrow"
      let coq_inverse = find_global ["Classes"; "CRelationClasses"] "flip"
    end

  module G = GlobalBindings(Consts)
  include G
  include Consts


  let inverse env (evd,cstrs) car rel = 
    let (evd, sort) = Evarutil.new_Type ~rigid:Evd.univ_flexible evd in
      app_poly_check env (evd,cstrs) coq_inverse [| car ; car; sort; rel |]

end

let sort_of_rel env evm rel =
  ESorts.kind evm (Reductionops.sort_of_arity env evm (Retyping.get_type_of env evm rel))

let is_applied_rewrite_relation = PropGlobal.is_applied_rewrite_relation

(* let _ = *)
(*   Hook.set Equality.is_applied_rewrite_relation is_applied_rewrite_relation *)

let split_head = function
    hd :: tl -> hd, tl
  | [] -> assert(false)

let eq_pb (ty, env, x, y as pb) (ty', env', x', y' as pb') =
  let equal x y = Constr.equal (EConstr.Unsafe.to_constr x) (EConstr.Unsafe.to_constr y) in
  pb == pb' || (ty == ty' && equal x x' && equal y y')

let problem_inclusion x y =
  List.for_all (fun pb -> List.exists (fun pb' -> eq_pb pb pb') y) x

let evd_convertible env evd x y =
  try
    (* Unfortunately, the_conv_x might say they are unifiable even if some
       unsolvable constraints remain, so we check that this unification
       does not introduce any new problem. *)
    let _, pbs = Evd.extract_all_conv_pbs evd in
    let evd' = Evarconv.the_conv_x env x y evd in
    let _, pbs' = Evd.extract_all_conv_pbs evd' in
    if evd' == evd || problem_inclusion pbs' pbs then Some evd'
    else None
  with e when CErrors.noncritical e -> None

let convertible env evd x y =
  Reductionops.is_conv_leq env evd x y

type hypinfo = {
  prf : constr;
  car : constr;
  rel : constr;
  sort : bool; (* true = Prop; false = Type *)
  c1 : constr;
  c2 : constr;
  holes : Clenv.hole list;
}

let get_symmetric_proof b = 
  if b then PropGlobal.get_symmetric_proof else TypeGlobal.get_symmetric_proof

let error_no_relation () = user_err Pp.(str "Cannot find a relation to rewrite.")

let rec decompose_app_rel env evd t = 
  (** Head normalize for compatibility with the old meta mechanism *)
  let t = Reductionops.whd_betaiota evd t in
  match EConstr.kind evd t with
  | App (f, [||]) -> assert false
  | App (f, [|arg|]) ->
    let (f', argl, argr) = decompose_app_rel env evd arg in
    let ty = Typing.unsafe_type_of env evd argl in
    let f'' = mkLambda (Name default_dependent_ident, ty,
      mkLambda (Name (Id.of_string "y"), lift 1 ty,
        mkApp (lift 2 f, [| mkApp (lift 2 f', [| mkRel 2; mkRel 1 |]) |])))
    in (f'', argl, argr)
  | App (f, args) ->
    let len = Array.length args in
    let fargs = Array.sub args 0 (Array.length args - 2) in
    let rel = mkApp (f, fargs) in
    rel, args.(len - 2), args.(len - 1)
  | _ -> error_no_relation ()

let decompose_app_rel env evd t =
  let (rel, t1, t2) = decompose_app_rel env evd t in
  let ty = Retyping.get_type_of env evd rel in
  let () = if not (Reductionops.is_arity env evd ty) then error_no_relation () in
  (rel, t1, t2)

let decompose_applied_relation env sigma (c,l) =
  let open Context.Rel.Declaration in
  let ctype = Retyping.get_type_of env sigma c in
  let find_rel ty =
    let sigma, cl = Clenv.make_evar_clause env sigma ty in
    let sigma = Clenv.solve_evar_clause env sigma true cl l in
    let { Clenv.cl_holes = holes; Clenv.cl_concl = t } = cl in
    let (equiv, c1, c2) = decompose_app_rel env sigma t in
    let ty1 = Retyping.get_type_of env sigma c1 in
    let ty2 = Retyping.get_type_of env sigma c2 in
    match evd_convertible env sigma ty1 ty2 with
    | None -> None
    | Some sigma ->
      let sort = sort_of_rel env sigma equiv in
      let args = Array.map_of_list (fun h -> h.Clenv.hole_evar) holes in
      let value = mkApp (c, args) in
        Some (sigma, { prf=value;
                car=ty1; rel = equiv; sort = Sorts.is_prop sort;
                c1=c1; c2=c2; holes })
  in
    match find_rel ctype with
    | Some c -> c
    | None ->
	let ctx,t' = Reductionops.splay_prod env sigma ctype in (* Search for underlying eq *)
	match find_rel (it_mkProd_or_LetIn t' (List.map (fun (n,t) -> LocalAssum (n, t)) ctx)) with
	| Some c -> c
	| None -> user_err Pp.(str "Cannot find an homogeneous relation to rewrite.")

let rewrite_db = "rewrite"

let conv_transparent_state = (Id.Pred.empty, Cpred.full)

let _ = 
  Hints.add_hints_init
    (fun () ->
       Hints.create_hint_db false rewrite_db conv_transparent_state true)

let rewrite_transparent_state () =
  Hints.Hint_db.transparent_state (Hints.searchtable_map rewrite_db)

let rewrite_core_unif_flags = {
  Unification.modulo_conv_on_closed_terms = None;
  Unification.use_metas_eagerly_in_conv_on_closed_terms = true;
  Unification.use_evars_eagerly_in_conv_on_closed_terms = true;
  Unification.modulo_delta = empty_transparent_state;
  Unification.modulo_delta_types = full_transparent_state;
  Unification.check_applied_meta_types = true;
  Unification.use_pattern_unification = true;
  Unification.use_meta_bound_pattern_unification = true;
  Unification.frozen_evars = Evar.Set.empty;
  Unification.restrict_conv_on_strict_subterms = false;
  Unification.modulo_betaiota = false;
  Unification.modulo_eta = true;
}

(* Flags used for the setoid variant of "rewrite" and for the strategies
   "hints"/"old_hints"/"terms" of "rewrite_strat", and for solving pre-existing
   evars in "rewrite" (see unify_abs) *)
let rewrite_unif_flags =
  let flags = rewrite_core_unif_flags in {
  Unification.core_unify_flags = flags;
  Unification.merge_unify_flags = flags;
  Unification.subterm_unify_flags = flags;
  Unification.allow_K_in_toplevel_higher_order_unification = true;
  Unification.resolve_evars = true
  }

let rewrite_core_conv_unif_flags = {
  rewrite_core_unif_flags with
    Unification.modulo_conv_on_closed_terms = Some conv_transparent_state;
    Unification.modulo_delta_types = conv_transparent_state;
    Unification.modulo_betaiota = true
}

(* Fallback flags for the setoid variant of "rewrite" *)
let rewrite_conv_unif_flags =
  let flags = rewrite_core_conv_unif_flags in {
  Unification.core_unify_flags = flags;
  Unification.merge_unify_flags = flags;
  Unification.subterm_unify_flags = flags;
  Unification.allow_K_in_toplevel_higher_order_unification = true;
  Unification.resolve_evars = true
  }

(* Flags for "setoid_rewrite c"/"rewrite_strat -> c" *)
let general_rewrite_unif_flags () =
  let ts = rewrite_transparent_state () in
  let core_flags =
    { rewrite_core_unif_flags with
      Unification.modulo_conv_on_closed_terms = Some ts;
      Unification.use_evars_eagerly_in_conv_on_closed_terms = true;
      Unification.modulo_delta = ts;
      Unification.modulo_delta_types = full_transparent_state;
      Unification.modulo_betaiota = true }
  in {
    Unification.core_unify_flags = core_flags;
    Unification.merge_unify_flags = core_flags;
    Unification.subterm_unify_flags = { core_flags with Unification.modulo_delta = empty_transparent_state };
    Unification.allow_K_in_toplevel_higher_order_unification = true;
    Unification.resolve_evars = true
  }

let refresh_hypinfo env sigma (is, cb) =
  let sigma, cbl = Tacinterp.interp_open_constr_with_bindings is env sigma cb in
  let sigma, hypinfo = decompose_applied_relation env sigma cbl in
  let { c1; c2; car; rel; prf; sort; holes } = hypinfo in
  sigma, (car, rel, prf, c1, c2, holes, sort)

(** FIXME: write this in the new monad interface *)
let solve_remaining_by env sigma holes by =
  match by with
  | None -> sigma
  | Some tac ->
    let map h =
      if h.Clenv.hole_deps then None
      else match EConstr.kind sigma h.Clenv.hole_evar with
      | Evar (evk, _) ->
        Some evk
      | _ -> None
    in
    (** Only solve independent holes *)
    let indep = List.map_filter map holes in
    let ist = { Geninterp.lfun = Id.Map.empty; extra = Geninterp.TacStore.empty } in
    let solve_tac = match tac with
    | Genarg.GenArg (Genarg.Glbwit tag, tac) ->
      Ftactic.run (Geninterp.interp tag ist tac) (fun _ -> Proofview.tclUNIT ())
    in
    let solve_tac = tclCOMPLETE solve_tac in
    let solve sigma evk =
      let evi =
        try Some (Evd.find_undefined sigma evk)
        with Not_found -> None
      in
      match evi with
      | None -> sigma
        (** Evar should not be defined, but just in case *)
      | Some evi ->
        let env = Environ.reset_with_named_context evi.evar_hyps env in
        let ty = evi.evar_concl in
        let c, sigma = Pfedit.refine_by_tactic env sigma ty solve_tac in
        Evd.define evk (EConstr.of_constr c) sigma
    in
    List.fold_left solve sigma indep

let no_constraints cstrs = 
  fun ev _ -> not (Evar.Set.mem ev cstrs)

let all_constraints cstrs = 
  fun ev _ -> Evar.Set.mem ev cstrs

let poly_inverse sort =
  if sort then PropGlobal.inverse else TypeGlobal.inverse

type rewrite_proof = 
  | RewPrf of constr * constr
  (** A Relation (R : rew_car -> rew_car -> Prop) and a proof of R rew_from rew_to *)
  | RewCast of cast_kind
  (** A proof of convertibility (with casts) *)

type rewrite_result_info = {
  rew_car : constr ;
  (** A type *)
  rew_from : constr ;
  (** A term of type rew_car *)
  rew_to : constr ;
  (** A term of type rew_car *)
  rew_prf : rewrite_proof ;
  (** A proof of rew_from == rew_to *)
  rew_evars : evars;
}

type rewrite_result =
| Fail
| Identity
| Success of rewrite_result_info

type 'a strategy_input = { state : 'a ; (* a parameter: for instance, a state *)
			   env : Environ.env ;
			   unfresh : Id.Set.t; (* Unfresh names *)
			   term1 : constr ;
			   ty1 : types ; (* first term and its type (convertible to rew_from) *)
			   cstr : (bool (* prop *) * constr option) ;
			   evars : evars }
	       
type 'a pure_strategy = { strategy :
  'a strategy_input ->
  'a * rewrite_result (* the updated state and the "result" *) }

type strategy = unit pure_strategy

let symmetry env sort rew =
  let { rew_evars = evars; rew_car = car; } = rew in
  let (rew_evars, rew_prf) = match rew.rew_prf with
  | RewCast _ -> (rew.rew_evars, rew.rew_prf)
  | RewPrf (rel, prf) ->
    try
      let evars, symprf = get_symmetric_proof sort env evars car rel in
      let prf = mkApp (symprf, [| rew.rew_from ; rew.rew_to ; prf |]) in
      (evars, RewPrf (rel, prf))
    with Not_found ->
      let evars, rel = poly_inverse sort env evars car rel in
      (evars, RewPrf (rel, prf))
  in
  { rew with rew_from = rew.rew_to; rew_to = rew.rew_from; rew_prf; rew_evars; }

(* Matching/unifying the rewriting rule against [t] *)
let unify_eqn (car, rel, prf, c1, c2, holes, sort) l2r flags env (sigma, cstrs) by t =
  try
    let left = if l2r then c1 else c2 in
    let sigma = Unification.w_unify ~flags env sigma CONV left t in
    let sigma = Typeclasses.resolve_typeclasses ~filter:(no_constraints cstrs)
      ~fail:true env sigma in
    let evd = solve_remaining_by env sigma holes by in
    let nf c = Reductionops.nf_evar evd (Reductionops.nf_meta evd c) in
    let c1 = nf c1 and c2 = nf c2
    and rew_car = nf car and rel = nf rel
    and prf = nf prf in
    let ty1 = Retyping.get_type_of env evd c1 in
    let ty2 = Retyping.get_type_of env evd c2 in
    let () = if not (convertible env evd ty2 ty1) then raise Reduction.NotConvertible in
    let rew_evars = evd, cstrs in
    let rew_prf = RewPrf (rel, prf) in
    let rew = { rew_evars; rew_prf; rew_car; rew_from = c1; rew_to = c2; } in
    let rew = if l2r then rew else symmetry env sort rew in
    Some rew
  with 
  | e when Class_tactics.catchable e -> None
  | Reduction.NotConvertible -> None

let unify_abs (car, rel, prf, c1, c2) l2r sort env (sigma, cstrs) t =
  try
    let left = if l2r then c1 else c2 in
    (* The pattern is already instantiated, so the next w_unify is
       basically an eq_constr, except when preexisting evars occur in
       either the lemma or the goal, in which case the eq_constr also
       solved this evars *)
    let sigma = Unification.w_unify ~flags:rewrite_unif_flags env sigma CONV left t in
    let rew_evars = sigma, cstrs in
    let rew_prf = RewPrf (rel, prf) in
    let rew = { rew_car = car; rew_from = c1; rew_to = c2; rew_prf; rew_evars; } in
    let rew = if l2r then rew else symmetry env sort rew in
    Some rew
  with 
  | e when Class_tactics.catchable e -> None
  | Reduction.NotConvertible -> None

type rewrite_flags = { under_lambdas : bool; on_morphisms : bool }

let default_flags = { under_lambdas = true; on_morphisms = true; }

let get_opt_rew_rel = function RewPrf (rel, prf) -> Some rel | _ -> None

let new_global (evars, cstrs) gr =
  let (sigma,c) = Evarutil.new_global evars gr in
  (sigma, cstrs), c

let make_eq sigma =
  new_global sigma (Coqlib.build_coq_eq ())
let make_eq_refl sigma =
  new_global sigma (Coqlib.build_coq_eq_refl ())

let get_rew_prf evars r = match r.rew_prf with
  | RewPrf (rel, prf) -> evars, (rel, prf)
  | RewCast c ->
    let evars, eq = make_eq evars in
    let evars, eq_refl = make_eq_refl evars in
    let rel = mkApp (eq, [| r.rew_car |]) in
    evars, (rel, mkCast (mkApp (eq_refl, [| r.rew_car; r.rew_from |]),
		         c, mkApp (rel, [| r.rew_from; r.rew_to |])))

let poly_subrelation sort = 
  if sort then PropGlobal.subrelation else TypeGlobal.subrelation

let resolve_subrelation env avoid car rel sort prf rel' res =
  if Termops.eq_constr (fst res.rew_evars) rel rel' then res
  else
    let evars, app = app_poly_check env res.rew_evars (poly_subrelation sort) [|car; rel; rel'|] in
    let evars, subrel = new_cstr_evar evars env app in
    let appsub = mkApp (subrel, [| res.rew_from ; res.rew_to ; prf |]) in
      { res with
	rew_prf = RewPrf (rel', appsub);
	rew_evars = evars }

let resolve_morphism env avoid oldt m ?(fnewt=fun x -> x) args args' (b,cstr) evars =
  let evars, morph_instance, proj, sigargs, m', args, args' =
    let first = match (Array.findi (fun _ b -> not (Option.is_empty b)) args') with
    | Some i -> i
    | None -> invalid_arg "resolve_morphism" in
    let morphargs, morphobjs = Array.chop first args in
    let morphargs', morphobjs' = Array.chop first args' in
    let appm = mkApp(m, morphargs) in
    let appmtype = Typing.unsafe_type_of env (goalevars evars) appm in
    let cstrs = List.map 
      (Option.map (fun r -> r.rew_car, get_opt_rew_rel r.rew_prf)) 
      (Array.to_list morphobjs') 
    in
      (* Desired signature *)
    let evars, appmtype', signature, sigargs = 
      if b then PropGlobal.build_signature evars env appmtype cstrs cstr
      else TypeGlobal.build_signature evars env appmtype cstrs cstr
    in
      (* Actual signature found *)
    let cl_args = [| appmtype' ; signature ; appm |] in
    let evars, app = app_poly_sort b env evars (if b then PropGlobal.proper_type else TypeGlobal.proper_type)
      cl_args in
    let env' = 
      let dosub, appsub = 
	if b then PropGlobal.do_subrelation, PropGlobal.apply_subrelation 
	else TypeGlobal.do_subrelation, TypeGlobal.apply_subrelation
      in
	EConstr.push_named
	  (LocalDef (Id.of_string "do_subrelation",
	             snd (app_poly_sort b env evars dosub [||]),
	             snd (app_poly_nocheck env evars appsub [||])))
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
		  let evars, proof = 
		    (if b then PropGlobal.proper_proof else TypeGlobal.proper_proof) 
		      env evars carrier relation x in
		    [ proof ; x ; x ] @ acc, subst, evars, sigargs, x :: typeargs'
	      | Some r ->
                 let evars, proof = get_rew_prf evars r in
		 [ snd proof; r.rew_to; x ] @ acc, subst, evars, 
	      sigargs, r.rew_to :: typeargs')
	  | None ->
	      if not (Option.is_empty y) then 
		user_err Pp.(str "Cannot rewrite inside dependent arguments of a function");
	      x :: acc, x :: subst, evars, sigargs, x :: typeargs')
      ([], [], evars, sigargs, []) args args'
  in
  let proof = applist (proj, List.rev projargs) in
  let newt = applist (m', List.rev typeargs) in
    match respars with
	[ a, Some r ] -> evars, proof, substl subst a, substl subst r, oldt, fnewt newt
      | _ -> assert(false)

let apply_constraint env avoid car rel prf cstr res =
  match snd cstr with
  | None -> res
  | Some r -> resolve_subrelation env avoid car rel (fst cstr) prf r res

let coerce env avoid cstr res = 
  let evars, (rel, prf) = get_rew_prf res.rew_evars res in
  let res = { res with rew_evars = evars } in
    apply_constraint env avoid res.rew_car rel prf cstr res

let apply_rule unify loccs : int pure_strategy =
  let (nowhere_except_in,occs) = convert_occs loccs in
  let is_occ occ =
    if nowhere_except_in 
    then List.mem occ occs 
    else not (List.mem occ occs) 
  in
  { strategy = fun { state = occ ; env ; unfresh ;
		     term1 = t ; ty1 = ty ; cstr ; evars } ->
      let unif = if isEvar (goalevars evars) t then None else unify env evars t in
	match unif with
	| None -> (occ, Fail)
        | Some rew ->
	  let occ = succ occ in
	    if not (is_occ occ) then (occ, Fail)
	    else if Termops.eq_constr (fst rew.rew_evars) t rew.rew_to then (occ, Identity)
	    else
	      let res = { rew with rew_car = ty } in
	      let res = Success (coerce env unfresh cstr res) in
              (occ, res)
    }

let apply_lemma l2r flags oc by loccs : strategy = { strategy =
  fun ({ state = () ; env ; term1 = t ; evars = (sigma, cstrs) } as input) ->
    let sigma, c = oc sigma in
    let sigma, hypinfo = decompose_applied_relation env sigma c in
    let { c1; c2; car; rel; prf; sort; holes } = hypinfo in
    let rew = (car, rel, prf, c1, c2, holes, sort) in
    let evars = (sigma, cstrs) in
    let unify env evars t =
      let rew = unify_eqn rew l2r flags env evars by t in
      match rew with
      | None -> None
      | Some rew -> Some rew
    in
    let _, res = (apply_rule unify loccs).strategy { input with
						     state = 0 ;
						     evars } in
    (), res
						   }

let e_app_poly env evars f args =
  let evars', c = app_poly_nocheck env !evars f args in
    evars := evars';
    c

let make_leibniz_proof env c ty r =
  let evars = ref r.rew_evars in
  let prf = 
    match r.rew_prf with
    | RewPrf (rel, prf) -> 
	let rel = e_app_poly env evars coq_eq [| ty |] in
	let prf =
	  e_app_poly env evars coq_f_equal
		[| r.rew_car; ty;
		   mkLambda (Anonymous, r.rew_car, c);
		   r.rew_from; r.rew_to; prf |]
	in RewPrf (rel, prf)
    | RewCast k -> r.rew_prf
  in
    { rew_car = ty; rew_evars = !evars;
      rew_from = subst1 r.rew_from c; rew_to = subst1 r.rew_to c; rew_prf = prf }

let reset_env env =
  let env' = Global.env_of_context (Environ.named_context_val env) in
    Environ.push_rel_context (Environ.rel_context env) env'
      
let fold_match ?(force=false) env sigma c =
  let (ci, p, c, brs) = destCase sigma c in
  let cty = Retyping.get_type_of env sigma c in
  let dep, pred, exists, (sk,eff) = 
    let env', ctx, body =
      let ctx, pred = decompose_lam_assum sigma p in
      let env' = push_rel_context ctx env in
	env', ctx, pred
    in
    let sortp = Retyping.get_sort_family_of env' sigma body in
    let sortc = Retyping.get_sort_family_of env sigma cty in
    let dep = not (noccurn sigma 1 body) in
    let pred = if dep then p else
	it_mkProd_or_LetIn (subst1 mkProp body) (List.tl ctx)
    in
    let sk = 
      if sortp == Sorts.InProp then
	if sortc == Sorts.InProp then
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
    let ind, args = Inductiveops.find_mrectype env sigma cty in
    let pars, args = List.chop ci.ci_npar args in
    let meths = List.map (fun br -> br) (Array.to_list brs) in
      applist (mkConst sk, pars @ [pred] @ meths @ args @ [c])
  in 
    sk, (if exists then env else reset_env env), app, eff

let unfold_match env sigma sk app =
  match EConstr.kind sigma app with
  | App (f', args) when Constant.equal (fst (destConst sigma f')) sk ->
      let v = Environ.constant_value_in (Global.env ()) (sk,Univ.Instance.empty)(*FIXME*) in
      let v = EConstr.of_constr v in
	Reductionops.whd_beta sigma (mkApp (v, args))
  | _ -> app

let is_rew_cast = function RewCast _ -> true | _ -> false

let subterm all flags (s : 'a pure_strategy) : 'a pure_strategy =
  let rec aux { state ; env ; unfresh ;
		term1 = t ; ty1 = ty ; cstr = (prop, cstr) ; evars } =
    let cstr' = Option.map (fun c -> (ty, Some c)) cstr in
      match EConstr.kind (goalevars evars) t with
      | App (m, args) ->
	  let rewrite_args state success =
	    let state, (args', evars', progress) =
	      Array.fold_left
		(fun (state, (acc, evars, progress)) arg ->
		  if not (Option.is_empty progress) && not all then 
		    state, (None :: acc, evars, progress)
		  else
		    let argty = Retyping.get_type_of env (goalevars evars) arg in
		    let state, res = s.strategy { state ; env ;
						  unfresh ;
						  term1 = arg ;	ty1 = argty ;
						  cstr = (prop,None) ;
						  evars } in
		    let res' = 
		      match res with
		      | Identity ->
			let progress = if Option.is_empty progress then Some false else progress in
			  (None :: acc, evars, progress)
		      | Success r -> 
			(Some r :: acc, r.rew_evars, Some true)
		      | Fail -> (None :: acc, evars, progress)
		    in state, res')
		(state, ([], evars, success)) args
	    in
	    let res = 
	      match progress with
	      | None -> Fail
	      | Some false -> Identity
	      | Some true ->
		let args' = Array.of_list (List.rev args') in
		  if Array.exists
		    (function 
		      | None -> false 
		      | Some r -> not (is_rew_cast r.rew_prf)) args'
		  then
		    let evars', prf, car, rel, c1, c2 = 
		      resolve_morphism env unfresh t m args args' (prop, cstr') evars' 
		    in
		    let res = { rew_car = ty; rew_from = c1;
				rew_to = c2; rew_prf = RewPrf (rel, prf);
				rew_evars = evars' } 
		    in Success res
		  else 
		    let args' = Array.map2
		      (fun aorig anew ->
			match anew with None -> aorig
			| Some r -> r.rew_to) args args' 
		    in
		    let res = { rew_car = ty; rew_from = t;
				rew_to = mkApp (m, args'); rew_prf = RewCast DEFAULTcast;
				rew_evars = evars' }
		    in Success res
	    in state, res
	  in
	    if flags.on_morphisms then
	      let mty = Retyping.get_type_of env (goalevars evars) m in
	      let evars, cstr', m, mty, argsl, args = 
		let argsl = Array.to_list args in
		let lift = if prop then PropGlobal.lift_cstr else TypeGlobal.lift_cstr in
		  match lift env evars argsl m mty None with
		  | Some (evars, cstr', m, mty, args) -> 
		    evars, Some cstr', m, mty, args, Array.of_list args
		  | None -> evars, None, m, mty, argsl, args
	      in
	      let state, m' = s.strategy { state ; env ; unfresh ;
					   term1 = m ; ty1 = mty ;
					   cstr = (prop, cstr') ; evars } in
		match m' with
		| Fail -> rewrite_args state None (* Standard path, try rewrite on arguments *)
		| Identity -> rewrite_args state (Some false)
		| Success r ->
		    (* We rewrote the function and get a proof of pointwise rel for the arguments.
		       We just apply it. *)
		    let prf = match r.rew_prf with
		      | RewPrf (rel, prf) ->
			let app = if prop then PropGlobal.apply_pointwise 
			  else TypeGlobal.apply_pointwise 
			in
			  RewPrf (app (goalevars evars) rel argsl, mkApp (prf, args))
		      | x -> x
		    in
		    let res =
		      { rew_car = Reductionops.hnf_prod_appvect env (goalevars evars) r.rew_car args;
			rew_from = mkApp(r.rew_from, args); rew_to = mkApp(r.rew_to, args);
			rew_prf = prf; rew_evars = r.rew_evars }
		    in 
		    let res = 
		      match prf with
		      | RewPrf (rel, prf) ->
			Success (apply_constraint env unfresh res.rew_car
				      rel prf (prop,cstr) res)
		      | _ -> Success res
		    in state, res
	    else rewrite_args state None
	      
      | Prod (n, x, b) when noccurn (goalevars evars) 1 b ->
	  let b = subst1 mkProp b in
	  let tx = Retyping.get_type_of env (goalevars evars) x
	  and tb = Retyping.get_type_of env (goalevars evars) b in
	  let arr = if prop then PropGlobal.arrow_morphism 
	    else TypeGlobal.arrow_morphism 
	  in
	  let (evars', mor), unfold = arr env evars tx tb x b in
	  let state, res = aux { state ; env ; unfresh ;
				 term1 = mor ; ty1 = ty ;
				 cstr = (prop,cstr) ; evars = evars' } in
	  let res = 
	    match res with
	    | Success r -> Success { r with rew_to = unfold (goalevars r.rew_evars) r.rew_to }
	    | Fail | Identity -> res
	  in state, res

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
	  let (evars', app), unfold = 
	    if eq_constr (fst evars) ty mkProp then
	      (app_poly_sort prop env evars coq_all [| dom; lam |]), TypeGlobal.unfold_all
	    else 
	      let forall = if prop then PropGlobal.coq_forall else TypeGlobal.coq_forall in
		(app_poly_sort prop env evars forall [| dom; lam |]), TypeGlobal.unfold_forall
	  in
	  let state, res = aux { state ; env ; unfresh ;
				 term1 = app ; ty1 = ty ;
				 cstr = (prop,cstr) ; evars = evars' } in
	  let res = 
	    match res with
	    | Success r -> Success { r with rew_to = unfold (goalevars r.rew_evars) r.rew_to }
	    | Fail | Identity -> res
	  in state, res

(* TODO: real rewriting under binders: introduce x x' (H : R x x') and rewrite with 
   H at any occurrence of x. Ask for (R ==> R') for the lambda. Formalize this.
   B. Barras' idea is to have a context of relations, of length 1, with Σ for gluing
   dependent relations and using projections to get them out.
 *)
      (* | Lambda (n, t, b) when flags.under_lambdas -> *)
      (* 	  let n' = name_app (fun id -> Tactics.fresh_id_in_env avoid id env) n in *)
      (* 	  let n'' = name_app (fun id -> Tactics.fresh_id_in_env avoid id env) n' in *)
      (* 	  let n''' = name_app (fun id -> Tactics.fresh_id_in_env avoid id env) n'' in *)
      (* 	  let rel = new_cstr_evar cstr env (mkApp (Lazy.force coq_relation, [|t|])) in *)
      (* 	  let env' = Environ.push_rel_context [(n'',None,lift 2 rel);(n'',None,lift 1 t);(n', None, t)] env in *)
      (* 	  let b' = s env' avoid b (Typing.type_of env' (goalevars evars) (lift 2 b)) (unlift_cstr env (goalevars evars) cstr) evars in *)
      (* 	    (match b' with *)
      (* 	    | Some (Some r) -> *)
      (* 		let prf = match r.rew_prf with *)
      (* 		  | RewPrf (rel, prf) -> *)
      (* 		      let rel = pointwise_or_dep_relation n' t r.rew_car rel in *)
      (* 		      let prf = mkLambda (n', t, prf) in *)
      (* 			RewPrf (rel, prf) *)
      (* 		  | x -> x *)
      (* 		in *)
      (* 		  Some (Some { r with *)
      (* 		    rew_prf = prf; *)
      (* 		    rew_car = mkProd (n, t, r.rew_car); *)
      (* 		    rew_from = mkLambda(n, t, r.rew_from); *)
      (* 		    rew_to = mkLambda (n, t, r.rew_to) }) *)
      (* 	    | _ -> b') *)

      | Lambda (n, t, b) when flags.under_lambdas ->
        let n' = Nameops.Name.map (fun id -> Tactics.fresh_id_in_env unfresh id env) n in
        let open Context.Rel.Declaration in
	let env' = EConstr.push_rel (LocalAssum (n', t)) env in
	let bty = Retyping.get_type_of env' (goalevars evars) b in
	let unlift = if prop then PropGlobal.unlift_cstr else TypeGlobal.unlift_cstr in
	let state, b' = s.strategy { state ; env = env' ; unfresh ;
				     term1 = b ; ty1 = bty ;
				     cstr = (prop, unlift env evars cstr) ;
				     evars } in
	let res = 
	  match b' with
	  | Success r ->
	    let r = match r.rew_prf with
	      | RewPrf (rel, prf) ->
		let point = if prop then PropGlobal.pointwise_or_dep_relation else
		    TypeGlobal.pointwise_or_dep_relation
		in
		let evars, rel = point env r.rew_evars n' t r.rew_car rel in
		let prf = mkLambda (n', t, prf) in
		  { r with rew_prf = RewPrf (rel, prf); rew_evars = evars }
	      | x -> r
	    in
	      Success { r with
		rew_car = mkProd (n, t, r.rew_car);
		rew_from = mkLambda(n, t, r.rew_from);
		rew_to = mkLambda (n, t, r.rew_to) }
	  | Fail | Identity -> b'
	in state, res
	    
      | Case (ci, p, c, brs) ->
	let cty = Retyping.get_type_of env (goalevars evars) c in
	let evars', eqty = app_poly_sort prop env evars coq_eq [| cty |] in
	let cstr' = Some eqty in
	let state, c' = s.strategy { state ; env ; unfresh ;
				     term1 = c ; ty1 = cty ;
				     cstr = (prop, cstr') ; evars = evars' } in
	let state, res = 
	  match c' with
	  | Success r ->
	    let case = mkCase (ci, lift 1 p, mkRel 1, Array.map (lift 1) brs) in
	    let res = make_leibniz_proof env case ty r in
	      state, Success (coerce env unfresh (prop,cstr) res)
	  | Fail | Identity ->
	    if Array.for_all (Int.equal 0) ci.ci_cstr_ndecls then
	      let evars', eqty = app_poly_sort prop env evars coq_eq [| ty |] in
	      let cstr = Some eqty in
	      let state, found, brs' = Array.fold_left 
		(fun (state, found, acc) br ->
		  if not (Option.is_empty found) then 
		    (state, found, fun x -> lift 1 br :: acc x)
		  else
		    let state, res = s.strategy { state ; env ; unfresh ;
						  term1 = br ; ty1 = ty ;
						  cstr = (prop,cstr) ; evars } in
		      match res with
		      | Success r -> (state, Some r, fun x -> mkRel 1 :: acc x)
		      | Fail | Identity -> (state, None, fun x -> lift 1 br :: acc x))
		(state, None, fun x -> []) brs
	      in
		match found with
		| Some r ->
		  let ctxc = mkCase (ci, lift 1 p, lift 1 c, Array.of_list (List.rev (brs' c'))) in
		    state, Success (make_leibniz_proof env ctxc ty r)
		| None -> state, c'
	    else
	      match try Some (fold_match env (goalevars evars) t) with Not_found -> None with
	      | None -> state, c'
	      | Some (cst, _, t', eff (*FIXME*)) ->
		 let state, res = aux { state ; env ; unfresh ;
					term1 = t' ; ty1 = ty ;
					cstr = (prop,cstr) ; evars } in
		let res = 
		  match res with
		  | Success prf -> 
		    Success { prf with
		      rew_from = t; 
		      rew_to = unfold_match env (goalevars evars) cst prf.rew_to }
		  | x' -> c'
		in state, res
	in 
	let res = 
	  match res with
	  | Success r -> Success (coerce env unfresh (prop,cstr) r)
	  | Fail | Identity -> res
	in state, res
      | _ -> state, Fail
  in { strategy = aux }

let all_subterms = subterm true default_flags
let one_subterm = subterm false default_flags

(** Requires transitivity of the rewrite step, if not a reduction.
    Not tail-recursive. *)

let transitivity state env unfresh prop (res : rewrite_result_info) (next : 'a pure_strategy) : 
    'a * rewrite_result =
  let state, nextres =
    next.strategy { state ; env ; unfresh ;
		    term1 = res.rew_to ; ty1 = res.rew_car ;
		    cstr = (prop, get_opt_rew_rel res.rew_prf) ;
		    evars = res.rew_evars }
  in 
  let res = 
    match nextres with
    | Fail -> Fail
    | Identity -> Success res
    | Success res' ->
      match res.rew_prf with
      | RewCast c -> Success { res' with rew_from = res.rew_from }
      | RewPrf (rew_rel, rew_prf) ->
	match res'.rew_prf with
	| RewCast _ -> Success { res with rew_to = res'.rew_to }
	| RewPrf (res'_rel, res'_prf) ->
	  let trans = 
	    if prop then PropGlobal.transitive_type 
	    else TypeGlobal.transitive_type
	  in
	  let evars, prfty = 
	    app_poly_sort prop env res'.rew_evars trans [| res.rew_car; rew_rel |] 
	  in
	  let evars, prf = new_cstr_evar evars env prfty in
	  let prf = mkApp (prf, [|res.rew_from; res'.rew_from; res'.rew_to;
				  rew_prf; res'_prf |])
	  in Success { res' with rew_from = res.rew_from; 
	    rew_evars = evars; rew_prf = RewPrf (res'_rel, prf) }
  in state, res

(** Rewriting strategies.

    Inspired by ELAN's rewriting strategies:
    http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.21.4049
*)

module Strategies =
  struct

    let fail : 'a pure_strategy =
      { strategy = fun { state } -> state, Fail }

    let id : 'a pure_strategy =
      { strategy = fun { state } -> state, Identity }

    let refl : 'a pure_strategy =
      { strategy =
	fun { state ; env ;
	      term1 = t ; ty1 = ty ;
	      cstr = (prop,cstr) ; evars } ->
	let evars, rel = match cstr with
	  | None -> 
	    let mkr = if prop then PropGlobal.mk_relation else TypeGlobal.mk_relation in
	    let evars, rty = mkr env evars ty in
	      new_cstr_evar evars env rty
	  | Some r -> evars, r
	in
	let evars, proof =
	  let proxy = 
	    if prop then PropGlobal.proper_proxy_type 
	    else TypeGlobal.proper_proxy_type
	  in
	  let evars, mty = app_poly_sort prop env evars proxy [| ty ; rel; t |] in
	    new_cstr_evar evars env mty
	in
	let res = Success { rew_car = ty; rew_from = t; rew_to = t;
			       rew_prf = RewPrf (rel, proof); rew_evars = evars }
	in state, res
      }

    let progress (s : 'a pure_strategy) : 'a pure_strategy = { strategy =
      fun input ->
	let state, res = s.strategy input in
	  match res with
	  | Fail -> state, Fail
	  | Identity -> state, Fail
	  | Success r -> state, Success r
							     }
	    
    let seq first snd : 'a pure_strategy = { strategy =
      fun ({ env ; unfresh ; cstr } as input) ->
	let state, res = first.strategy input in
	  match res with
	  | Fail -> state, Fail
	  | Identity -> snd.strategy { input with state }
	  | Success res -> transitivity state env unfresh (fst cstr) res snd
					   }
	    
    let choice fst snd : 'a pure_strategy = { strategy =
      fun input ->
	let state, res = fst.strategy input in
	  match res with
	  | Fail -> snd.strategy { input with state }
	  | Identity | Success _ -> state, res
					    }

    let try_ str : 'a pure_strategy = choice str id

    let check_interrupt str input =
      Control.check_for_interrupt ();
      str input

    let fix (f : 'a pure_strategy -> 'a pure_strategy) : 'a pure_strategy =
      let rec aux input = (f { strategy = fun input -> check_interrupt aux input }).strategy input in
      { strategy = aux }
    
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

    let lemmas cs : 'a pure_strategy =
      List.fold_left (fun tac (l,l2r,by) ->
	choice tac (apply_lemma l2r rewrite_unif_flags l by AllOccurrences))
	fail cs

    let inj_open hint = (); fun sigma ->
      let ctx = UState.of_context_set hint.Autorewrite.rew_ctx in
      let sigma = Evd.merge_universe_context sigma ctx in
      (sigma, (EConstr.of_constr hint.Autorewrite.rew_lemma, NoBindings))

    let old_hints (db : string) : 'a pure_strategy =
      let rules = Autorewrite.find_rewrites db in
	lemmas
	  (List.map (fun hint -> (inj_open hint, hint.Autorewrite.rew_l2r,
				  hint.Autorewrite.rew_tac)) rules)

    let hints (db : string) : 'a pure_strategy = { strategy =
      fun ({ term1 = t } as input) ->
      let t = EConstr.Unsafe.to_constr t in
      let rules = Autorewrite.find_matches db t in
      let lemma hint = (inj_open hint, hint.Autorewrite.rew_l2r,
			hint.Autorewrite.rew_tac) in
      let lems = List.map lemma rules in
      (lemmas lems).strategy input
						 }

    let reduce (r : Redexpr.red_expr) : 'a pure_strategy = { strategy =
	fun { state = state ; env = env ; term1 = t ; ty1 = ty ; cstr = cstr ; evars = evars } ->
          let rfn, ckind = Redexpr.reduction_of_red_expr env r in
          let sigma = goalevars evars in
	  let (sigma, t') = rfn env sigma t in
	    if Termops.eq_constr sigma t' t then
	      state, Identity
	    else
	      state, Success { rew_car = ty; rew_from = t; rew_to = t';
			       rew_prf = RewCast ckind; 
			       rew_evars = sigma, cstrevars evars }
							   }
	
    let fold_glob c : 'a pure_strategy = { strategy =
      fun { state ; env ; term1 = t ; ty1 = ty ; cstr ; evars } ->
(* 	let sigma, (c,_) = Tacinterp.interp_open_constr_with_bindings is env (goalevars evars) c in *)
	let sigma, c = Pretyping.understand_tcc env (goalevars evars) c in
	let unfolded =
	  try Tacred.try_red_product env sigma c
	  with e when CErrors.noncritical e ->
            user_err Pp.(str "fold: the term is not unfoldable!")
	in
	  try
	    let sigma = Unification.w_unify env sigma CONV ~flags:(Unification.elim_flags ()) unfolded t in
	    let c' = Reductionops.nf_evar sigma c in
	      state, Success { rew_car = ty; rew_from = t; rew_to = c';
				  rew_prf = RewCast DEFAULTcast;
				  rew_evars = (sigma, snd evars) }
	  with e when CErrors.noncritical e -> state, Fail
					 }
  

end

(** The strategy for a single rewrite, dealing with occurrences. *)

(** A dummy initial clauseenv to avoid generating initial evars before
    even finding a first application of the rewriting lemma, in setoid_rewrite
    mode *)

let rewrite_with l2r flags c occs : strategy = { strategy =
  fun ({ state = () } as input) ->
    let unify env evars t =
      let (sigma, cstrs) = evars in
      let (sigma, rew) = refresh_hypinfo env sigma c in
      unify_eqn rew l2r flags env (sigma, cstrs) None t
    in
    let app = apply_rule unify occs in
    let strat = 
      Strategies.fix (fun aux -> 
	Strategies.choice app (subterm true default_flags aux))
    in
    let _, res = strat.strategy { input with state = 0 } in
    ((), res)
					       }

let apply_strategy (s : strategy) env unfresh concl (prop, cstr) evars =
  let ty = Retyping.get_type_of env (goalevars evars) concl in
  let _, res = s.strategy { state = () ; env ; unfresh ;
			    term1 = concl ; ty1 = ty ;
			    cstr = (prop, Some cstr) ; evars } in
  res

let solve_constraints env (evars,cstrs) =
  let filter = all_constraints cstrs in
    Typeclasses.resolve_typeclasses env ~filter ~split:false ~fail:true 
      (Typeclasses.mark_resolvables ~filter evars)
      
let nf_zeta =
  Reductionops.clos_norm_flags (CClosure.RedFlags.mkflags [CClosure.RedFlags.fZETA])

exception RewriteFailure of Pp.t

type result = (evar_map * constr option * types) option option

let cl_rewrite_clause_aux ?(abs=None) strat env avoid sigma concl is_hyp : result =
  let sigma, sort = Typing.sort_of env sigma concl in
  let evdref = ref sigma in
  let evars = (!evdref, Evar.Set.empty) in
  let evars, cstr =
    let prop, (evars, arrow) = 
      if Sorts.is_prop sort then true, app_poly_sort true env evars impl [||]
      else false, app_poly_sort false env evars TypeGlobal.arrow [||]
    in
      match is_hyp with
      | None -> 
	let evars, t = poly_inverse prop env evars (mkSort sort) arrow in 
	  evars, (prop, t)
      | Some _ -> evars, (prop, arrow)
  in
  let eq = apply_strategy strat env avoid concl cstr evars in
    match eq with
    | Fail -> None
    | Identity -> Some None
    | Success res ->
      let (_, cstrs) = res.rew_evars in
      let evars' = solve_constraints env res.rew_evars in
      let newt = Reductionops.nf_evar evars' res.rew_to in
      let evars = (* Keep only original evars (potentially instantiated) and goal evars,
		     the rest has been defined and substituted already. *)
	Evar.Set.fold 
	  (fun ev acc -> 
	   if not (Evd.is_defined acc ev) then 
	     user_err ~hdr:"rewrite"
			  (str "Unsolved constraint remaining: " ++ spc () ++
			   Termops.pr_evar_info (Evd.find acc ev))
	   else Evd.remove acc ev) 
	  cstrs evars'
      in
      let res = match res.rew_prf with
	| RewCast c -> None
	| RewPrf (rel, p) ->
	  let p = nf_zeta env evars' (Reductionops.nf_evar evars' p) in
	  let term =
	    match abs with
	    | None -> p
	    | Some (t, ty) ->
              let t = Reductionops.nf_evar evars' t in
              let ty = Reductionops.nf_evar evars' ty in
		mkApp (mkLambda (Name (Id.of_string "lemma"), ty, p), [| t |])
	  in
	  let proof = match is_hyp with
            | None -> term
            | Some id -> mkApp (term, [| mkVar id |])
          in Some proof
      in Some (Some (evars, res, newt))

(** Insert a declaration after the last declaration it depends on *)
let rec insert_dependent env sigma decl accu hyps = match hyps with
| [] -> List.rev_append accu [decl]
| ndecl :: rem ->
  if occur_var_in_decl env sigma (NamedDecl.get_id ndecl) decl then
    List.rev_append accu (decl :: hyps)
  else
    insert_dependent env sigma decl (ndecl :: accu) rem

let assert_replacing id newt tac = 
  let prf = Proofview.Goal.enter begin fun gl ->
    let concl = Proofview.Goal.concl gl in
    let env = Proofview.Goal.env gl in
    let sigma = Tacmach.New.project gl in
    let ctx = named_context env in
    let after, before = List.split_when (NamedDecl.get_id %> Id.equal id) ctx in
    let nc = match before with
    | [] -> assert false
    | d :: rem -> insert_dependent env sigma (LocalAssum (NamedDecl.get_id d, newt)) [] after @ rem
    in
    let env' = Environ.reset_with_named_context (val_of_named_context nc) env in
    Refine.refine ~typecheck:true begin fun sigma ->
      let (sigma, ev) = Evarutil.new_evar env' sigma concl in
      let (sigma, ev') = Evarutil.new_evar env sigma newt in
      let map d =
        let n = NamedDecl.get_id d in
        if Id.equal n id then ev' else mkVar n
      in
      let (e, _) = destEvar sigma ev in
      (sigma, mkEvar (e, Array.map_of_list map nc))
    end
  end in
  Proofview.tclTHEN prf (Proofview.tclFOCUS 2 2 tac)

let newfail n s = 
  Proofview.tclZERO (Refiner.FailError (n, lazy s))

let cl_rewrite_clause_newtac ?abs ?origsigma ~progress strat clause =
  let open Proofview.Notations in
  (** For compatibility *)
  let beta = Tactics.reduct_in_concl (Reductionops.nf_betaiota, DEFAULTcast) in
  let beta_hyp id = Tactics.reduct_in_hyp Reductionops.nf_betaiota (id, InHyp) in
  let treat sigma res = 
    match res with
    | None -> newfail 0 (str "Nothing to rewrite")
    | Some None -> if progress then newfail 0 (str"Failed to progress")
		   else Proofview.tclUNIT ()
    | Some (Some res) ->
        let (undef, prf, newt) = res in
        let fold ev _ accu = if Evd.mem sigma ev then accu else ev :: accu in
        let gls = List.rev (Evd.fold_undefined fold undef []) in
        let gls = List.map Proofview.with_empty_state gls in
          match clause, prf with
	| Some id, Some p ->
            let tac = tclTHENLIST [
              Refine.refine ~typecheck:true (fun h -> (h,p));
              Proofview.Unsafe.tclNEWGOALS gls;
            ] in
            Proofview.Unsafe.tclEVARS undef <*>
	    tclTHENFIRST (assert_replacing id newt tac) (beta_hyp id)
	| Some id, None ->
            Proofview.Unsafe.tclEVARS undef <*>
            convert_hyp_no_check (LocalAssum (id, newt)) <*>
            beta_hyp id
	| None, Some p ->
            Proofview.Unsafe.tclEVARS undef <*>
            Proofview.Goal.enter begin fun gl ->
            let env = Proofview.Goal.env gl in
            let make = begin fun sigma ->
              let (sigma, ev) = Evarutil.new_evar env sigma newt in
              (sigma, mkApp (p, [| ev |]))
            end in
            Refine.refine ~typecheck:true make <*> Proofview.Unsafe.tclNEWGOALS gls
            end
	| None, None ->
            Proofview.Unsafe.tclEVARS undef <*>
            convert_concl_no_check newt DEFAULTcast
  in
  Proofview.Goal.enter begin fun gl ->
    let concl = Proofview.Goal.concl gl in
    let env = Proofview.Goal.env gl in
    let sigma = Tacmach.New.project gl in
    let ty = match clause with
    | None -> concl
    | Some id -> EConstr.of_constr (Environ.named_type id env)
    in
    let env = match clause with
    | None -> env
    | Some id ->
      (** Only consider variables not depending on [id] *)
      let ctx = named_context env in
      let filter decl = not (occur_var_in_decl env sigma id decl) in
      let nctx = List.filter filter ctx in
      Environ.reset_with_named_context (val_of_named_context nctx) env
    in
    try
      let res =
        cl_rewrite_clause_aux ?abs strat env Id.Set.empty sigma ty clause
      in
      let sigma = match origsigma with None -> sigma | Some sigma -> sigma in
      treat sigma res <*>
      (** For compatibility *)
      beta <*> Proofview.shelve_unifiable
    with
    | PretypeError (env, evd, (UnsatisfiableConstraints _ as e)) ->
      raise (RewriteFailure (Himsg.explain_pretype_error env evd e))
  end

let tactic_init_setoid () = 
  try init_setoid (); Proofview.tclUNIT ()
  with e when CErrors.noncritical e -> Tacticals.New.tclFAIL 0 (str"Setoid library not loaded")

let cl_rewrite_clause_strat progress strat clause =
  tactic_init_setoid () <*>
  (if progress then Proofview.tclPROGRESS else fun x -> x)
   (Proofview.tclOR
      (cl_rewrite_clause_newtac ~progress strat clause)
      (fun (e, info) -> match e with
       | RewriteFailure e ->
	 tclZEROMSG (str"setoid rewrite failed: " ++ e)
       | Refiner.FailError (n, pp) -> 
	  tclFAIL n (str"setoid rewrite failed: " ++ Lazy.force pp)
       | e -> Proofview.tclZERO ~info e))

(** Setoid rewriting when called with "setoid_rewrite" *)
let cl_rewrite_clause l left2right occs clause =
  let strat = rewrite_with left2right (general_rewrite_unif_flags ()) l occs in
    cl_rewrite_clause_strat true strat clause

(** Setoid rewriting when called with "rewrite_strat" *)
let cl_rewrite_clause_strat strat clause =
  cl_rewrite_clause_strat false strat clause
  
let apply_glob_constr c l2r occs = (); fun ({ state = () ; env = env } as input) ->
  let c sigma =
    let (sigma, c) = Pretyping.understand_tcc env sigma c in
    (sigma, (c, NoBindings))
  in
  let flags = general_rewrite_unif_flags () in
  (apply_lemma l2r flags c None occs).strategy input

let interp_glob_constr_list env =
  let make c = (); fun sigma ->
    let sigma, c = Pretyping.understand_tcc env sigma c in
    (sigma, (c, NoBindings))
  in
  List.map (fun c -> make c, true, None)

(* Syntax for rewriting with strategies *)

type unary_strategy = 
    Subterms | Subterm | Innermost | Outermost
  | Bottomup | Topdown | Progress | Try | Any | Repeat

type binary_strategy = 
  | Compose | Choice

type ('constr,'redexpr) strategy_ast = 
  | StratId | StratFail | StratRefl
  | StratUnary of unary_strategy * ('constr,'redexpr) strategy_ast
  | StratBinary of binary_strategy 
    * ('constr,'redexpr) strategy_ast * ('constr,'redexpr) strategy_ast
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

let pr_ustrategy = function
| Subterms -> str "subterms"
| Subterm -> str "subterm"
| Innermost -> str "innermost"
| Outermost -> str "outermost"
| Bottomup -> str "bottomup"
| Topdown -> str "topdown"
| Progress -> str "progress"
| Try -> str "try"
| Any -> str "any"
| Repeat -> str "repeat"

let paren p = str "(" ++ p ++ str ")"

let rec pr_strategy prc prr = function
| StratId -> str "id"
| StratFail -> str "fail"
| StratRefl -> str "refl"
| StratUnary (s, str) ->
  pr_ustrategy s ++ spc () ++ paren (pr_strategy prc prr str)
| StratBinary (Choice, str1, str2) ->
  str "choice" ++ spc () ++ paren (pr_strategy prc prr str1) ++ spc () ++
    paren (pr_strategy prc prr str2)
| StratBinary (Compose, str1, str2) ->
  pr_strategy prc prr str1 ++ str ";" ++ spc () ++ pr_strategy prc prr str2
| StratConstr (c, true) -> prc c
| StratConstr (c, false) -> str "<-" ++ spc () ++ prc c
| StratTerms cl -> str "terms" ++ spc () ++ pr_sequence prc cl
| StratHints (old, id) ->
  let cmd = if old then "old_hints" else "hints" in
  str cmd ++ spc () ++ str id
| StratEval r -> str "eval" ++ spc () ++ prr r
| StratFold c -> str "fold" ++ spc () ++ prc c

let rec strategy_of_ast = function
  | StratId -> Strategies.id
  | StratFail -> Strategies.fail
  | StratRefl -> Strategies.refl
  | StratUnary (f, s) -> 
    let s' = strategy_of_ast s in
    let f' = match f with
      | Subterms -> all_subterms
      | Subterm -> one_subterm
      | Innermost -> Strategies.innermost
      | Outermost -> Strategies.outermost
      | Bottomup -> Strategies.bu
      | Topdown -> Strategies.td
      | Progress -> Strategies.progress
      | Try -> Strategies.try_
      | Any -> Strategies.any
      | Repeat -> Strategies.repeat
    in f' s'
  | StratBinary (f, s, t) ->
    let s' = strategy_of_ast s in
    let t' = strategy_of_ast t in
    let f' = match f with
      | Compose -> Strategies.seq
      | Choice -> Strategies.choice
    in f' s' t'
  | StratConstr (c, b) -> { strategy = apply_glob_constr (fst c) b AllOccurrences }
  | StratHints (old, id) -> if old then Strategies.old_hints id else Strategies.hints id
  | StratTerms l -> { strategy =
    (fun ({ state = () ; env } as input) ->
     let l' = interp_glob_constr_list env (List.map fst l) in
     (Strategies.lemmas l').strategy input)
		    }
  | StratEval r -> { strategy =
    (fun ({ state = () ; env ; evars } as input) ->
     let (sigma,r_interp) = Tacinterp.interp_redexp env (goalevars evars) r in
     (Strategies.reduce r_interp).strategy { input with
					     evars = (sigma,cstrevars evars) }) }
  | StratFold c -> Strategies.fold_glob (fst c)


(* By default the strategy for "rewrite_db" is top-down *)

let mkappc s l = CAst.make @@ CAppExpl ((None,qualid_of_ident (Id.of_string s),None),l)

let declare_an_instance n s args =
  (((CAst.make @@ Name n),None), Explicit,
   CAst.make @@ CAppExpl ((None, qualid_of_string s,None), args))

let declare_instance a aeq n s = declare_an_instance n s [a;aeq]

let anew_instance global binders instance fields =
  let program_mode = Flags.is_program_mode () in
  let poly = Flags.is_universe_polymorphism () in
  new_instance ~program_mode poly
    binders instance (Some (true, CAst.make @@ CRecord (fields)))
    ~global ~generalize:false ~refine:false Hints.empty_hint_info

let declare_instance_refl global binders a aeq n lemma =
  let instance = declare_instance a aeq (add_suffix n "_Reflexive") "Coq.Classes.RelationClasses.Reflexive"
  in anew_instance global binders instance
       [(qualid_of_ident (Id.of_string "reflexivity"),lemma)]

let declare_instance_sym global binders a aeq n lemma =
  let instance = declare_instance a aeq (add_suffix n "_Symmetric") "Coq.Classes.RelationClasses.Symmetric"
  in anew_instance global binders instance
       [(qualid_of_ident (Id.of_string "symmetry"),lemma)]

let declare_instance_trans global binders a aeq n lemma =
  let instance = declare_instance a aeq (add_suffix n "_Transitive") "Coq.Classes.RelationClasses.Transitive"
  in anew_instance global binders instance
       [(qualid_of_ident (Id.of_string "transitivity"),lemma)]

let declare_relation ?locality ?(binders=[]) a aeq n refl symm trans =
  init_setoid ();
  let global = not (Locality.make_section_locality locality) in
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
              [(qualid_of_ident (Id.of_string "PreOrder_Reflexive"), lemma1);
               (qualid_of_ident (Id.of_string "PreOrder_Transitive"),lemma3)])
    | (None, Some lemma2, Some lemma3) ->
	let _lemma_sym = declare_instance_sym global binders a aeq n lemma2 in
	let _lemma_trans = declare_instance_trans global binders a aeq n lemma3 in
	let instance = declare_instance a aeq n "Coq.Classes.RelationClasses.PER"
	in ignore(
	    anew_instance global binders instance
              [(qualid_of_ident (Id.of_string "PER_Symmetric"), lemma2);
               (qualid_of_ident (Id.of_string "PER_Transitive"),lemma3)])
     | (Some lemma1, Some lemma2, Some lemma3) ->
	let _lemma_refl = declare_instance_refl global binders a aeq n lemma1 in
	let _lemma_sym = declare_instance_sym global binders a aeq n lemma2 in
	let _lemma_trans = declare_instance_trans global binders a aeq n lemma3 in
	let instance = declare_instance a aeq n "Coq.Classes.RelationClasses.Equivalence"
	in ignore(
	  anew_instance global binders instance
            [(qualid_of_ident (Id.of_string "Equivalence_Reflexive"), lemma1);
             (qualid_of_ident (Id.of_string "Equivalence_Symmetric"), lemma2);
             (qualid_of_ident (Id.of_string "Equivalence_Transitive"), lemma3)])

let cHole = CAst.make @@ CHole (None, Namegen.IntroAnonymous, None)

let proper_projection sigma r ty =
  let rel_vect n m = Array.init m (fun i -> mkRel(n+m-i)) in
  let ctx, inst = decompose_prod_assum sigma ty in
  let mor, args = destApp sigma inst in
  let instarg = mkApp (r, rel_vect 0 (List.length ctx)) in
  let app = mkApp (Lazy.force PropGlobal.proper_proj,
		  Array.append args [| instarg |]) in
    it_mkLambda_or_LetIn app ctx

let declare_projection n instance_id r =
  let poly = Global.is_polymorphic r in
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let sigma,c = Evd.fresh_global env sigma r in
  let ty = Retyping.get_type_of env sigma c in
  let term = proper_projection sigma c ty in
  let sigma, typ = Typing.type_of env sigma term in
  let ctx, typ = decompose_prod_assum sigma typ in
  let typ =
    let n =
      let rec aux t =
	match EConstr.kind sigma t with
	| App (f, [| a ; a' ; rel; rel' |]) 
	    when Termops.is_global sigma (PropGlobal.respectful_ref ()) f ->
	  succ (aux rel')
	| _ -> 0
      in
      let init =
	match EConstr.kind sigma typ with
	    App (f, args) when Termops.is_global sigma (PropGlobal.respectful_ref ()) f  ->
	      mkApp (f, fst (Array.chop (Array.length args - 2) args))
	  | _ -> typ
      in aux init
    in
    let ctx,ccl = Reductionops.splay_prod_n env sigma (3 * n) typ
    in it_mkProd_or_LetIn ccl ctx
  in
  let typ = it_mkProd_or_LetIn typ ctx in
  let univs = Evd.const_univ_entry ~poly sigma in
  let typ = EConstr.to_constr sigma typ in
  let term = EConstr.to_constr sigma term in
  let cst = 
    Declare.definition_entry ~types:typ ~univs term
  in
    ignore(Declare.declare_constant n 
	   (Entries.DefinitionEntry cst, Decl_kinds.IsDefinition Decl_kinds.Definition))

let build_morphism_signature env sigma m =
  let m,ctx = Constrintern.interp_constr env sigma m in
  let sigma = Evd.from_ctx ctx in
  let t = Typing.unsafe_type_of env sigma m in
  let cstrs =
    let rec aux t =
      match EConstr.kind sigma t with
	| Prod (na, a, b) ->
	    None :: aux b
	| _ -> []
    in aux t
  in
  let evars, t', sig_, cstrs = 
    PropGlobal.build_signature (sigma, Evar.Set.empty) env t cstrs None in
  let evd = ref evars in
  let _ = List.iter
    (fun (ty, rel) ->
      Option.iter (fun rel ->
	let default = e_app_poly env evd PropGlobal.default_relation [| ty; rel |] in
	  ignore(e_new_cstr_evar env evd default))
	rel)
    cstrs
  in
  let morph = e_app_poly env evd PropGlobal.proper_type [| t; sig_; m |] in
  let evd = solve_constraints env !evd in
  let evd = Evd.minimize_universes evd in
  let m = Evarutil.nf_evars_universes evd (EConstr.Unsafe.to_constr morph) in
  Pretyping.check_evars env (Evd.from_env env) evd (EConstr.of_constr m);
  Evd.evar_universe_context evd, m

let default_morphism sign m =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let t = Typing.unsafe_type_of env sigma m in
  let evars, _, sign, cstrs =
    PropGlobal.build_signature (sigma, Evar.Set.empty) env t (fst sign) (snd sign)
  in
  let evars, morph = app_poly_check env evars PropGlobal.proper_type [| t; sign; m |] in
  let evars, mor = resolve_one_typeclass env (goalevars evars) morph in
    mor, proper_projection sigma mor morph

let warn_add_setoid_deprecated =
  CWarnings.create ~name:"add-setoid" ~category:"deprecated" (fun () ->
      Pp.(str "Add Setoid is deprecated, please use Add Parametric Relation."))

let add_setoid global binders a aeq t n =
  warn_add_setoid_deprecated ?loc:a.CAst.loc ();
  init_setoid ();
  let _lemma_refl = declare_instance_refl global binders a aeq n (mkappc "Seq_refl" [a;aeq;t]) in
  let _lemma_sym = declare_instance_sym global binders a aeq n (mkappc "Seq_sym" [a;aeq;t]) in
  let _lemma_trans = declare_instance_trans global binders a aeq n (mkappc "Seq_trans" [a;aeq;t]) in
  let instance = declare_instance a aeq n "Coq.Classes.RelationClasses.Equivalence"
  in ignore(
    anew_instance global binders instance
      [(qualid_of_ident (Id.of_string "Equivalence_Reflexive"), mkappc "Seq_refl" [a;aeq;t]);
       (qualid_of_ident (Id.of_string "Equivalence_Symmetric"), mkappc "Seq_sym" [a;aeq;t]);
       (qualid_of_ident (Id.of_string "Equivalence_Transitive"), mkappc "Seq_trans" [a;aeq;t])])


let make_tactic name =
  let open Tacexpr in
  let tacqid = Libnames.qualid_of_string name in
  TacArg (Loc.tag @@ (TacCall (Loc.tag (tacqid, []))))

let warn_add_morphism_deprecated =
  CWarnings.create ~name:"add-morphism" ~category:"deprecated" (fun () ->
      Pp.(str "Add Morphism f : id is deprecated, please use Add Morphism f with signature (...) as id"))

let add_morphism_infer glob m n =
  warn_add_morphism_deprecated ?loc:m.CAst.loc ();
  init_setoid ();
  let poly = Flags.is_universe_polymorphism () in
  let instance_id = add_suffix n "_Proper" in
  let env = Global.env () in
  let evd = Evd.from_env env in
  let uctx, instance = build_morphism_signature env evd m in
    if Lib.is_modtype () then
      let uctx = UState.const_univ_entry ~poly uctx in
      let cst = Declare.declare_constant ~internal:Declare.InternalTacticRequest instance_id
				(Entries.ParameterEntry 
                                 (None,(instance,uctx),None),
				 Decl_kinds.IsAssumption Decl_kinds.Logical)
      in
	add_instance (Typeclasses.new_instance 
                        (Lazy.force PropGlobal.proper_class) Hints.empty_hint_info glob (ConstRef cst));
	declare_projection n instance_id (ConstRef cst)
    else
      let kind = Decl_kinds.Global, poly, 
	Decl_kinds.DefinitionBody Decl_kinds.Instance 
      in
      let tac = make_tactic "Coq.Classes.SetoidTactics.add_morphism_tactic" in
      let hook _ = function
	| Globnames.ConstRef cst ->
	  add_instance (Typeclasses.new_instance 
			  (Lazy.force PropGlobal.proper_class) Hints.empty_hint_info
                          glob (ConstRef cst));
	  declare_projection n instance_id (ConstRef cst)
	| _ -> assert false
      in
      let hook = Lemmas.mk_hook hook in
	Flags.silently
	  (fun () ->
	    Lemmas.start_proof instance_id kind (Evd.from_ctx uctx) (EConstr.of_constr instance) hook;
	    ignore (Pfedit.by (Tacinterp.interp tac))) ()

let add_morphism glob binders m s n =
  init_setoid ();
  let poly = Flags.is_universe_polymorphism () in
  let instance_id = add_suffix n "_Proper" in
  let instance =
    (((CAst.make @@ Name instance_id),None), Explicit,
    CAst.make @@ CAppExpl (
             (None, Libnames.qualid_of_string "Coq.Classes.Morphisms.Proper",None),
	     [cHole; s; m]))
  in
  let tac = Tacinterp.interp (make_tactic "add_morphism_tactic") in
  let program_mode = Flags.is_program_mode () in
  ignore(new_instance ~program_mode ~global:glob poly binders instance
           (Some (true, CAst.make @@ CRecord []))
    ~generalize:false ~tac ~hook:(declare_projection n instance_id) Hints.empty_hint_info)

(** Bind to "rewrite" too *)

(** Taken from original setoid_replace, to emulate the old rewrite semantics where
    lemmas are first instantiated and then rewrite proceeds. *)

let check_evar_map_of_evars_defs env evd =
 let metas = Evd.meta_list evd in
 let check_freemetas_is_empty rebus =
  Evd.Metaset.iter
   (fun m ->
     if Evd.meta_defined evd m then ()
     else begin
       raise
         (Logic.RefinerError (env, evd, Logic.UnresolvedBindings [Evd.meta_name evd m]))
     end)
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

(* Find a subterm which matches the pattern to rewrite for "rewrite" *)
let unification_rewrite l2r c1 c2 sigma prf car rel but env =
  let (sigma,c') =
    try
      (* ~flags:(false,true) to allow to mark occurrences that must not be
         rewritten simply by replacing them with let-defined definitions
         in the context *)
      Unification.w_unify_to_subterm 
       ~flags:rewrite_unif_flags
        env sigma ((if l2r then c1 else c2),but)
    with
    | ex when Pretype_errors.precatchable_exception ex ->
	(* ~flags:(true,true) to make Ring work (since it really
           exploits conversion) *)
      Unification.w_unify_to_subterm 
        ~flags:rewrite_conv_unif_flags
        env sigma ((if l2r then c1 else c2),but)
  in
  let nf c = Reductionops.nf_evar sigma c in
  let c1 = if l2r then nf c' else nf c1
  and c2 = if l2r then nf c2 else nf c'
  and car = nf car and rel = nf rel in
  check_evar_map_of_evars_defs env sigma;
  let prf = nf prf in
  let prfty = nf (Retyping.get_type_of env sigma prf) in
  let sort = sort_of_rel env sigma but in
  let abs = prf, prfty in
  let prf = mkRel 1 in
  let res = (car, rel, prf, c1, c2) in
  abs, sigma, res, Sorts.is_prop sort

let get_hyp gl (c,l) clause l2r =
  let evars = Tacmach.New.project gl in
  let env = Tacmach.New.pf_env gl in
  let sigma, hi = decompose_applied_relation env evars (c,l) in
  let but = match clause with
    | Some id -> Tacmach.New.pf_get_hyp_typ id gl
    | None -> Reductionops.nf_evar evars (Tacmach.New.pf_concl gl)
  in
  unification_rewrite l2r hi.c1 hi.c2 sigma hi.prf hi.car hi.rel but env

let general_rewrite_flags = { under_lambdas = false; on_morphisms = true }

(* let rewriteclaustac_key = CProfile.declare_profile "cl_rewrite_clause_tac";; *)
(* let cl_rewrite_clause_tac = CProfile.profile5 rewriteclaustac_key cl_rewrite_clause_tac *)

(** Setoid rewriting when called with "rewrite" *)
let general_s_rewrite cl l2r occs (c,l) ~new_goals =
  Proofview.Goal.enter begin fun gl ->
  let abs, evd, res, sort = get_hyp gl (c,l) cl l2r in
  let unify env evars t = unify_abs res l2r sort env evars t in
  let app = apply_rule unify occs in
  let recstrat aux = Strategies.choice app (subterm true general_rewrite_flags aux) in
  let substrat = Strategies.fix recstrat in
  let strat = { strategy = fun ({ state = () } as input) ->
    let _, res = substrat.strategy { input with state = 0 } in
    (), res
	      }
  in
  let origsigma = Tacmach.New.project gl in
  tactic_init_setoid () <*>
    Proofview.tclOR
      (tclPROGRESS
	(tclTHEN
           (Proofview.Unsafe.tclEVARS evd)
	    (cl_rewrite_clause_newtac ~progress:true ~abs:(Some abs) ~origsigma strat cl)))
    (fun (e, info) -> match e with
    | RewriteFailure e ->
      tclFAIL 0 (str"setoid rewrite failed: " ++ e)
    | e -> Proofview.tclZERO ~info e)
  end

let _ = Hook.set Equality.general_setoid_rewrite_clause general_s_rewrite

(** [setoid_]{reflexivity,symmetry,transitivity} tactics *)

let not_declared env sigma ty rel =
  tclFAIL 0
    (str" The relation " ++ Printer.pr_econstr_env env sigma rel ++ str" is not a declared " ++
     str ty ++ str" relation. Maybe you need to require the Coq.Classes.RelationClasses library")

let setoid_proof ty fn fallback =
  Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Tacmach.New.project gl in
    let concl = Proofview.Goal.concl gl in
    Proofview.tclORELSE
      begin
        try
          let rel, _, _ = decompose_app_rel env sigma concl in
          let (sigma, t) = Typing.type_of env sigma rel in
          let car = snd (List.hd (fst (Reductionops.splay_prod env sigma t))) in
	    (try init_relation_classes () with _ -> raise Not_found);
            fn env sigma car rel
        with e -> Proofview.tclZERO e
      end
      begin function
        | e ->
            Proofview.tclORELSE
              fallback
              begin function (e', info) -> match e' with
                | Hipattern.NoEquationFound ->
	            begin match e with
	            | (Not_found, _) ->
	                let rel, _, _ = decompose_app_rel env sigma concl in
		        not_declared env sigma ty rel
	            | (e, info) -> Proofview.tclZERO ~info e
                    end
                | e' -> Proofview.tclZERO ~info e'
              end
      end
  end

let tac_open ((evm,_), c) tac = 
    (tclTHEN (Proofview.Unsafe.tclEVARS evm) (tac c))

let poly_proof getp gett env evm car rel =
  if Sorts.is_prop (sort_of_rel env evm rel) then
    getp env (evm,Evar.Set.empty) car rel
  else gett env (evm,Evar.Set.empty) car rel

let setoid_reflexivity =
  setoid_proof "reflexive"
    (fun env evm car rel -> 
     tac_open (poly_proof PropGlobal.get_reflexive_proof
			  TypeGlobal.get_reflexive_proof
			  env evm car rel)
	      (fun c -> tclCOMPLETE (apply c)))
    (reflexivity_red true)

let setoid_symmetry =
  setoid_proof "symmetric"
    (fun env evm car rel -> 
      tac_open
	(poly_proof PropGlobal.get_symmetric_proof TypeGlobal.get_symmetric_proof
	   env evm car rel)
	(fun c -> apply c))
    (symmetry_red true)
    
let setoid_transitivity c =
  setoid_proof "transitive"
    (fun env evm car rel ->
      tac_open (poly_proof PropGlobal.get_transitive_proof TypeGlobal.get_transitive_proof
	   env evm car rel)
	(fun proof -> match c with
	| None -> eapply proof
	| Some c -> apply_with_bindings (proof,ImplicitBindings [ c ])))
    (transitivity_red true c)
    
let setoid_symmetry_in id =
  let open Tacmach.New in
  Proofview.Goal.enter begin fun gl ->
  let sigma = project gl in
  let ctype = pf_unsafe_type_of gl (mkVar id) in
  let binders,concl = decompose_prod_assum sigma ctype in
  let (equiv, args) = decompose_app sigma concl in
  let rec split_last_two = function
    | [c1;c2] -> [],(c1, c2)
    | x::y::z -> let l,res = split_last_two (y::z) in x::l, res
    | _ -> user_err Pp.(str "Cannot find an equivalence relation to rewrite.")
  in
  let others,(c1,c2) = split_last_two args in
  let he,c1,c2 =  mkApp (equiv, Array.of_list others),c1,c2 in
  let new_hyp' =  mkApp (he, [| c2 ; c1 |]) in
  let new_hyp = it_mkProd_or_LetIn new_hyp'  binders in
    (tclTHENLAST
      (Tactics.assert_after_replacing id new_hyp)
      (tclTHENLIST [ intros; setoid_symmetry; apply (mkVar id); Tactics.assumption ]))
  end

let _ = Hook.set Tactics.setoid_reflexivity setoid_reflexivity
let _ = Hook.set Tactics.setoid_symmetry setoid_symmetry
let _ = Hook.set Tactics.setoid_symmetry_in setoid_symmetry_in
let _ = Hook.set Tactics.setoid_transitivity setoid_transitivity

let get_lemma_proof f env evm x y = 
  let (evm, _), c = f env (evm,Evar.Set.empty) x y in
    evm, c

let get_reflexive_proof =
  get_lemma_proof PropGlobal.get_reflexive_proof

let get_symmetric_proof = 
  get_lemma_proof PropGlobal.get_symmetric_proof

let get_transitive_proof = 
  get_lemma_proof PropGlobal.get_transitive_proof
  
