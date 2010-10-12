(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4deps: "parsing/grammar.cma" i*)

open Pp
open Util
open Names
open Nameops
open Namegen
open Term
open Termops
open Sign
open Reduction
open Proof_type
open Declarations
open Tacticals
open Tacmach
open Evar_refiner
open Tactics
open Pattern
open Clenv
open Auto
open Rawterm
open Hiddentac
open Typeclasses
open Typeclasses_errors
open Classes
open Topconstr
open Pfedit
open Command
open Libnames
open Evd
open Compat

(** Typeclass-based generalized rewriting. *)

let check_required_library d =
  let d' = List.map id_of_string d in
  let dir = make_dirpath (List.rev d') in
  if not (Library.library_is_loaded dir) then
    error ("Library "^(list_last d)^" has to be required first.")

let classes_dirpath =
  make_dirpath (List.map id_of_string ["Classes";"Coq"])

let init_setoid () =
  if is_dirpath_prefix_of classes_dirpath (Lib.cwd ()) then ()
  else check_required_library ["Coq";"Setoids";"Setoid"]

let proper_class =
  lazy (class_info (Nametab.global (Qualid (dummy_loc, qualid_of_string "Coq.Classes.Morphisms.Proper"))))

let proper_proxy_class =
  lazy (class_info (Nametab.global (Qualid (dummy_loc, qualid_of_string "Coq.Classes.Morphisms.ProperProxy"))))

let proper_proj = lazy (mkConst (Option.get (snd (List.hd (Lazy.force proper_class).cl_projs))))

let make_dir l = make_dirpath (List.map id_of_string (List.rev l))

let try_find_global_reference dir s =
  let sp = Libnames.make_path (make_dir ("Coq"::dir)) (id_of_string s) in
    Nametab.global_of_path sp

let try_find_reference dir s =
  constr_of_global (try_find_global_reference dir s)

let gen_constant dir s = Coqlib.gen_constant "rewrite" dir s
let coq_eq = lazy(gen_constant ["Init"; "Logic"] "eq")
let coq_f_equal = lazy (gen_constant ["Init"; "Logic"] "f_equal")
let coq_all = lazy (gen_constant ["Init"; "Logic"] "all")
let impl = lazy (gen_constant ["Program"; "Basics"] "impl")
let arrow = lazy (gen_constant ["Program"; "Basics"] "arrow")

let reflexive_type = lazy (try_find_reference ["Classes"; "RelationClasses"] "Reflexive")
let reflexive_proof = lazy (try_find_reference ["Classes"; "RelationClasses"] "reflexivity")

let symmetric_type = lazy (try_find_reference ["Classes"; "RelationClasses"] "Symmetric")
let symmetric_proof = lazy (try_find_reference ["Classes"; "RelationClasses"] "symmetry")

let transitive_type = lazy (try_find_reference ["Classes"; "RelationClasses"] "Transitive")
let transitive_proof = lazy (try_find_reference ["Classes"; "RelationClasses"] "transitivity")

let coq_inverse = lazy (gen_constant (* ["Classes"; "RelationClasses"] "inverse" *)
			   ["Program"; "Basics"] "flip")

let inverse car rel = mkApp (Lazy.force coq_inverse, [| car ; car; mkProp; rel |])
(* let inverse car rel = mkApp (Lazy.force coq_inverse, [| car ; car; new_Type (); rel |]) *)

let forall_relation = lazy (gen_constant ["Classes"; "Morphisms"] "forall_relation")
let pointwise_relation = lazy (gen_constant ["Classes"; "Morphisms"] "pointwise_relation")

let respectful = lazy (gen_constant ["Classes"; "Morphisms"] "respectful")

let default_relation = lazy (gen_constant ["Classes"; "SetoidTactics"] "DefaultRelation")

let subrelation = lazy (gen_constant ["Classes"; "RelationClasses"] "subrelation")
let do_subrelation = lazy (gen_constant ["Classes"; "Morphisms"] "do_subrelation")
let apply_subrelation = lazy (gen_constant ["Classes"; "Morphisms"] "apply_subrelation")

let coq_relation = lazy (gen_constant ["Relations";"Relation_Definitions"] "relation")
let mk_relation a = mkApp (Lazy.force coq_relation, [| a |])
(* let mk_relation a = mkProd (Anonymous, a, mkProd (Anonymous, a, new_Type ())) *)

let rewrite_relation_class = lazy (gen_constant ["Classes"; "RelationClasses"] "RewriteRelation")

let arrow_morphism a b =
  if isprop a && isprop b then
    Lazy.force impl
  else Lazy.force arrow

let proper_type = lazy (constr_of_global (Lazy.force proper_class).cl_impl)

let proper_proxy_type = lazy (constr_of_global (Lazy.force proper_proxy_class).cl_impl)

let is_applied_rewrite_relation env sigma rels t =
  match kind_of_term t with
  | App (c, args) when Array.length args >= 2 ->
      let head = if isApp c then fst (destApp c) else c in
	if eq_constr (Lazy.force coq_eq) head then None
	else
	  (try
	      let params, args = array_chop (Array.length args - 2) args in
	      let env' = Environ.push_rel_context rels env in
	      let evd, evar = Evarutil.new_evar sigma env' (new_Type ()) in
	      let inst = mkApp (Lazy.force rewrite_relation_class, [| evar; mkApp (c, params) |]) in
	      let _ = Typeclasses.resolve_one_typeclass env' evd inst in
		Some (it_mkProd_or_LetIn t rels)
	  with _ -> None)
  | _ -> None

let _ =
  Equality.register_is_applied_rewrite_relation is_applied_rewrite_relation

let split_head = function
    hd :: tl -> hd, tl
  | [] -> assert(false)

let new_cstr_evar (goal,cstr) env t =
  let cstr', t = Evarutil.new_evar cstr env t in
    (goal, cstr'), t

let build_signature evars env m (cstrs : (types * types option) option list)
    (finalcstr : (types * types option) option) =
  let new_evar evars env t =
    new_cstr_evar evars env
      (* ~src:(dummy_loc, ImplicitArg (ConstRef (Lazy.force respectful), (n, Some na))) *) t
  in
  let mk_relty evars env ty obj =
    match obj with
      | None | Some (_, None) ->
	  let relty = mk_relation ty in
	    new_evar evars env relty
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
	      if obj = None then evars, mkProd(na, ty, b), arg', (ty, None) :: cstrs
	      else error "build_signature: no constraint can apply on a dependent argument"
      | _, obj :: _ -> anomaly "build_signature: not enough products"
      | _, [] ->
	  (match finalcstr with
	  | None | Some (_, None) ->
	      let t = Reductionops.nf_betaiota (fst evars) ty in
	      let evars, rel = mk_relty evars env t None in
		evars, t, rel, [t, Some rel]
	  | Some (t, Some rel) -> evars, t, rel, [t, Some rel])
  in aux env evars m cstrs

let proper_proof env evars carrier relation x =
  let goal = mkApp (Lazy.force proper_proxy_type, [| carrier ; relation; x |])
  in new_cstr_evar evars env goal

let find_class_proof proof_type proof_method env evars carrier relation =
  try
    let goal = mkApp (Lazy.force proof_type, [| carrier ; relation |]) in
    let evars, c = Typeclasses.resolve_one_typeclass env evars goal in
      mkApp (Lazy.force proof_method, [| carrier; relation; c |])
  with e when Logic.catchable_exception e -> raise Not_found

let get_reflexive_proof env = find_class_proof reflexive_type reflexive_proof env
let get_symmetric_proof env = find_class_proof symmetric_type symmetric_proof env
let get_transitive_proof env = find_class_proof transitive_type transitive_proof env

exception FoundInt of int

let array_find (arr: 'a array) (pred: int -> 'a -> bool): int =
  try
    for i=0 to Array.length arr - 1 do if pred i (arr.(i)) then raise (FoundInt i) done;
    raise Not_found
  with FoundInt i -> i

type hypinfo = {
  cl : clausenv;
  prf : constr;
  car : constr;
  rel : constr;
  l2r : bool;
  c1 : constr;
  c2 : constr;
  c  : constr with_bindings option;
  abs : (constr * types) option;
}

let evd_convertible env evd x y =
  try ignore(Evarconv.the_conv_x env x y evd); true
  with _ -> false

let rec decompose_app_rel env evd t = 
  match kind_of_term t with
  | App (f, args) -> 
      if Array.length args > 1 then 
	let fargs, args = array_chop (Array.length args - 2) args in
	  mkApp (f, fargs), args
      else 
	let (f', args) = decompose_app_rel env evd args.(0) in
	let ty = Typing.type_of env evd args.(0) in
	let f'' = mkLambda (Name (id_of_string "x"), ty,
	  mkLambda (Name (id_of_string "y"), lift 1 ty,
	    mkApp (lift 2 f, [| mkApp (lift 2 f', [| mkRel 2; mkRel 1 |]) |])))
	in (f'', args)
  | _ -> error "The term provided is not an applied relation."

let decompose_applied_relation env sigma (c,l) left2right =
  let ctype = Typing.type_of env sigma c in
  let find_rel ty =
    let eqclause = Clenv.make_clenv_binding_env_apply env sigma None (c,ty) l in
    let (equiv, args) = decompose_app_rel env sigma (Clenv.clenv_type eqclause) in
    let c1 = args.(0) and c2 = args.(1) in 
    let ty1, ty2 =
      Typing.type_of env eqclause.evd c1, Typing.type_of env eqclause.evd c2
    in
      if not (evd_convertible env eqclause.evd ty1 ty2) then None
      else
	Some { cl=eqclause; prf=(Clenv.clenv_value eqclause);
	       car=ty1; rel = equiv;
	       l2r=left2right; c1=c1; c2=c2; c=Some (c,l); abs=None }
  in
    match find_rel ctype with
    | Some c -> c
    | None ->
	let ctx,t' = Reductionops.splay_prod_assum env sigma ctype in (* Search for underlying eq *)
	match find_rel (it_mkProd_or_LetIn t' ctx) with
	| Some c -> c
	| None -> error "The term does not end with an applied homogeneous relation."

let rewrite_unif_flags = {
  Unification.modulo_conv_on_closed_terms = None;
  Unification.use_metas_eagerly = true;
  Unification.modulo_delta = empty_transparent_state;
  Unification.resolve_evars = true;
  Unification.use_evars_pattern_unification = true;
  Unification.modulo_eta = true
}

let conv_transparent_state = (Idpred.empty, Cpred.full)

let rewrite2_unif_flags = {
  Unification.modulo_conv_on_closed_terms = Some conv_transparent_state;
  Unification.use_metas_eagerly = true;
  Unification.modulo_delta = empty_transparent_state;
  Unification.resolve_evars = true;
  Unification.use_evars_pattern_unification = true;
  Unification.modulo_eta = true
}

let convertible env evd x y =
  Reductionops.is_conv env evd x y

let allowK = true

let refresh_hypinfo env sigma hypinfo =
  if hypinfo.abs = None then
    let {l2r=l2r; c=c;cl=cl} = hypinfo in
      match c with
	| Some c ->
	    (* Refresh the clausenv to not get the same meta twice in the goal. *)
	    decompose_applied_relation env cl.evd c l2r;
	| _ -> hypinfo
  else hypinfo

let unify_eqn env sigma hypinfo t =
  if isEvar t then None
  else try
    let {cl=cl; prf=prf; car=car; rel=rel; l2r=l2r; c1=c1; c2=c2; c=c; abs=abs} = !hypinfo in
    let left = if l2r then c1 else c2 in
    let env', prf, c1, c2, car, rel =
      match abs with
      | Some (absprf, absprfty) ->
	  let env' = clenv_unify allowK ~flags:rewrite_unif_flags CONV left t cl in
	    env', prf, c1, c2, car, rel
      | None ->
	  let env' =
	    try clenv_unify allowK ~flags:rewrite_unif_flags CONV left t cl
	    with Pretype_errors.PretypeError _ ->
	      (* For Ring essentially, only when doing setoid_rewrite *)
	      clenv_unify allowK ~flags:rewrite2_unif_flags CONV left t cl
	  in
	  let env' = Clenvtac.clenv_pose_dependent_evars true env' in
	  let evd' = Typeclasses.resolve_typeclasses ~fail:true env'.env env'.evd in
	  let env' = { env' with evd = evd' } in
	  let nf c = Evarutil.nf_evar evd' (Clenv.clenv_nf_meta env' c) in
	  let c1 = nf c1 and c2 = nf c2
	  and car = nf car and rel = nf rel
	  and prf = nf (Clenv.clenv_value env') in
	  let ty1 = Typing.type_of env'.env env'.evd c1
	  and ty2 = Typing.type_of env'.env env'.evd c2
	  in
	    if convertible env env'.evd ty1 ty2 then (
	      if occur_meta prf then
		hypinfo := refresh_hypinfo env sigma !hypinfo;
	      env', prf, c1, c2, car, rel)
	    else raise Reduction.NotConvertible
    in
    let res =
      if l2r then (prf, (car, rel, c1, c2))
      else
	try (mkApp (get_symmetric_proof env Evd.empty car rel,
		   [| c1 ; c2 ; prf |]),
	    (car, rel, c2, c1))
	with Not_found ->
	  (prf, (car, inverse car rel, c2, c1))
    in Some (env', res)
  with e when Class_tactics.catchable e -> None

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

let rec decomp_pointwise n c =
  if n = 0 then c
  else
    match kind_of_term c with
    | App (f, [| a; b; relb |]) when eq_constr f (Lazy.force pointwise_relation) ->
	decomp_pointwise (pred n) relb
    | App (f, [| a; b; arelb |]) when eq_constr f (Lazy.force forall_relation) ->
	decomp_pointwise (pred n) (Reductionops.beta_applist (arelb, [mkRel 1]))
    | _ -> raise (Invalid_argument "decomp_pointwise")
	
let rec apply_pointwise rel = function
  | arg :: args ->
      (match kind_of_term rel with
      | App (f, [| a; b; relb |]) when eq_constr f (Lazy.force pointwise_relation) ->
	  apply_pointwise relb args
      | App (f, [| a; b; arelb |]) when eq_constr f (Lazy.force forall_relation) ->
	  apply_pointwise (Reductionops.beta_applist (arelb, [arg])) args
      | _ -> raise (Invalid_argument "apply_pointwise"))
  | [] -> rel

let pointwise_or_dep_relation n t car rel =
  if noccurn 1 car then
    mkApp (Lazy.force pointwise_relation, [| t; lift (-1) car; lift (-1) rel |])
  else
    mkApp (Lazy.force forall_relation, 
	  [| t; mkLambda (n, t, car); mkLambda (n, t, rel) |])

let lift_cstr env sigma evars (args : constr list) c ty cstr =
  let start env car =
    match cstr with
    | None | Some (_, None) ->
	Evarutil.e_new_evar evars env (mk_relation car)
    | Some (ty, Some rel) -> rel
  in
  let rec aux env prod n = 
    if n = 0 then start env prod
    else
      match kind_of_term (Reduction.whd_betadeltaiota env prod) with
      | Prod (na, ty, b) ->
	  if noccurn 1 b then
	    let b' = lift (-1) b in
	    let rb = aux env b' (pred n) in
	      mkApp (Lazy.force pointwise_relation, [| ty; b'; rb |])
	  else
	    let rb = aux (Environ.push_rel (na, None, ty) env) b (pred n) in
	      mkApp (Lazy.force forall_relation, 
		    [| ty; mkLambda (na, ty, b); mkLambda (na, ty, rb) |])
      | _ -> raise Not_found
  in 
  let rec find env c ty = function
    | [] -> None
    | arg :: args ->
	try Some (aux env ty (succ (List.length args)), c, ty, arg :: args)
	with Not_found ->
	  find env (mkApp (c, [| arg |])) (prod_applist ty [arg]) args
  in find env c ty args

let unlift_cstr env sigma = function
  | None -> None
  | Some codom -> Some (decomp_pointwise 1 codom)

type rewrite_flags = { under_lambdas : bool; on_morphisms : bool }

let default_flags = { under_lambdas = true; on_morphisms = true; }

type evars = evar_map * evar_map (* goal evars, constraint evars *)

type rewrite_proof = 
  | RewPrf of constr * constr
  | RewCast of cast_kind

let get_rew_rel = function RewPrf (rel, prf) -> Some rel | _ -> None

type rewrite_result_info = {
  rew_car : constr;
  rew_from : constr;
  rew_to : constr;
  rew_prf : rewrite_proof;
  rew_evars : evars;
}

type rewrite_result = rewrite_result_info option

type strategy = Environ.env -> evar_map -> constr -> types ->
  constr option -> evars -> rewrite_result option

let get_rew_prf r = match r.rew_prf with
  | RewPrf (rel, prf) -> prf 
  | RewCast c ->
      mkCast (mkApp (Coqlib.build_coq_eq_refl (), [| r.rew_car; r.rew_from |]),
	     c, mkApp (Coqlib.build_coq_eq (), [| r.rew_car; r.rew_from; r.rew_to |]))

let resolve_subrelation env sigma car rel prf rel' res =
  if eq_constr rel rel' then res
  else
(*   try let evd' = Evarconv.the_conv_x env rel rel' res.rew_evars in *)
(* 	{ res with rew_evars = evd' } *)
(*   with NotConvertible -> *)
    let app = mkApp (Lazy.force subrelation, [|car; rel; rel'|]) in
    let evars, subrel = new_cstr_evar res.rew_evars env app in
    let appsub = mkApp (subrel, [| res.rew_from ; res.rew_to ; prf |]) in
      { res with
	rew_prf = RewPrf (rel', appsub);
	rew_evars = evars }

let resolve_morphism env sigma oldt m ?(fnewt=fun x -> x) args args' cstr evars =
  let evars, morph_instance, proj, sigargs, m', args, args' =
    let first = try (array_find args' (fun i b -> b <> None)) 
      with Not_found -> raise (Invalid_argument "resolve_morphism") in
    let morphargs, morphobjs = array_chop first args in
    let morphargs', morphobjs' = array_chop first args' in
    let appm = mkApp(m, morphargs) in
    let appmtype = Typing.type_of env sigma appm in
    let cstrs = List.map (Option.map (fun r -> r.rew_car, get_rew_rel r.rew_prf)) (Array.to_list morphobjs') in
      (* Desired signature *)
    let evars, appmtype', signature, sigargs = 
      build_signature evars env appmtype cstrs cstr
    in
      (* Actual signature found *)
    let cl_args = [| appmtype' ; signature ; appm |] in
    let app = mkApp (Lazy.force proper_type, cl_args) in
    let env' = Environ.push_named
      (id_of_string "do_subrelation", Some (Lazy.force do_subrelation), Lazy.force apply_subrelation)
      env
    in
    let evars, morph = new_cstr_evar evars env' app in
      evars, morph, morph, sigargs, appm, morphobjs, morphobjs'
  in
  let projargs, subst, evars, respars, typeargs =
    array_fold_left2
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
		  [ get_rew_prf r; r.rew_to; x ] @ acc, subst, evars, sigargs, r.rew_to :: typeargs')
	  | None ->
	      if y <> None then error "Cannot rewrite the argument of a dependent function";
	      x :: acc, x :: subst, evars, sigargs, x :: typeargs')
      ([], [], evars, sigargs, []) args args'
  in
  let proof = applistc proj (List.rev projargs) in
  let newt = applistc m' (List.rev typeargs) in
    match respars with
	[ a, Some r ] -> evars, proof, a, r, oldt, fnewt newt
      | _ -> assert(false)

let apply_constraint env sigma car rel prf cstr res =
  match cstr with
  | None -> res
  | Some r -> resolve_subrelation env sigma car rel prf r res

let eq_env x y = x == y

let apply_rule hypinfo loccs : strategy =
  let (nowhere_except_in,occs) = loccs in
  let is_occ occ =
    if nowhere_except_in then List.mem occ occs else not (List.mem occ occs) in
  let occ = ref 0 in
    fun env sigma t ty cstr evars ->
      if not (eq_env !hypinfo.cl.env env) then hypinfo := refresh_hypinfo env sigma !hypinfo;
      let unif = unify_eqn env sigma hypinfo t in
	if unif <> None then incr occ;
	match unif with
	| Some (env', (prf, (car, rel, c1, c2))) when is_occ !occ ->
	    begin
	      if eq_constr t c2 then Some None
	      else
		let goalevars = Evd.evar_merge (fst evars)
		  (Evd.undefined_evars env'.evd)
		in
		let res = { rew_car = ty; rew_from = c1;
			    rew_to = c2; rew_prf = RewPrf (rel, prf); rew_evars = goalevars, snd evars }
		in Some (Some (apply_constraint env sigma car rel prf cstr res))
	    end
	| _ -> None

let apply_lemma (evm,c) left2right loccs : strategy =
  fun env sigma ->
    let evars = Evd.merge sigma evm in
    let hypinfo = ref (decompose_applied_relation env evars c left2right) in
      apply_rule hypinfo loccs env sigma

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

open Elimschemes

let reset_env env =
  let env' = Global.env_of_context (Environ.named_context_val env) in
    Environ.push_rel_context (Environ.rel_context env) env'
      
let fold_match ?(force=false) env sigma c =
  let (ci, p, c, brs) = destCase c in
  let cty = Retyping.get_type_of env sigma c in
  let dep, pred, exists, sk = 
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
      if sortp = InProp then
	if sortc = InProp then
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
    let pars, args = list_chop ci.ci_npar args in
    let meths = List.map (fun br -> br) (Array.to_list brs) in
      applist (mkConst sk, pars @ [pred] @ meths @ args @ [c])
  in 
    sk, (if exists then env else reset_env env), app
      
let unfold_match env sigma sk app =
  match kind_of_term app with
  | App (f', args) when f' = mkConst sk ->
      let v = Environ.constant_value_def (Global.env ()) sk in
	Reductionops.whd_beta sigma (mkApp (v, args))
  | _ -> app
    
let subterm all flags (s : strategy) : strategy =
  let rec aux env sigma t ty cstr evars =
    let cstr' = Option.map (fun c -> (ty, Some c)) cstr in
      match kind_of_term t with
      | App (m, args) ->
	  let rewrite_args success =
	    let args', evars', progress =
	      Array.fold_left
		(fun (acc, evars, progress) arg ->
		  if progress <> None && not all then (None :: acc, evars, progress)
		  else
		    let res = s env sigma arg (Typing.type_of env sigma arg) None evars in
		      match res with
		      | Some None -> (None :: acc, evars, if progress = None then Some false else progress)
		      | Some (Some r) -> (Some r :: acc, r.rew_evars, Some true)
		      | None -> (None :: acc, evars, progress))
		([], evars, success) args
	    in
	      match progress with
	      | None -> None
	      | Some false -> Some None
	      | Some true ->
		  let args' = Array.of_list (List.rev args') in
		  let evars', prf, car, rel, c1, c2 = resolve_morphism env sigma t m args args' cstr' evars' in
		  let res = { rew_car = ty; rew_from = c1;
			      rew_to = c2; rew_prf = RewPrf (rel, prf);
			      rew_evars = evars' } 
		  in
		    Some (Some res)
	  in
	    if flags.on_morphisms then
	      let evarsref = ref (snd evars) in
	      let mty = Typing.type_of env sigma m in
	      let cstr', m, mty, argsl, args = 
		let argsl = Array.to_list args in
		  match lift_cstr env sigma evarsref argsl m mty None with
		  | Some (cstr', m, mty, args) -> Some cstr', m, mty, args, Array.of_list args
		  | None -> None, m, mty, argsl, args
	      in
	      let m' = s env sigma m mty cstr' (fst evars, !evarsref) in
		match m' with
		| None -> rewrite_args None (* Standard path, try rewrite on arguments *)
		| Some None -> rewrite_args (Some false)
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
		      match prf with
		      | RewPrf (rel, prf) ->
			  Some (Some (apply_constraint env sigma res.rew_car rel prf cstr res))
		      | _ -> Some (Some res)
	    else rewrite_args None
	      
      | Prod (n, x, b) when noccurn 1 b ->
	  let b = subst1 mkProp b in
	  let tx = Typing.type_of env sigma x and tb = Typing.type_of env sigma b in
	  let res = aux env sigma (mkApp (arrow_morphism tx tb, [| x; b |])) ty cstr evars in
	    (match res with
	    | Some (Some r) -> Some (Some { r with rew_to = unfold_impl r.rew_to })
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

      | Prod (n, dom, codom) when eq_constr ty mkProp ->
	  let lam = mkLambda (n, dom, codom) in
	  let res = aux env sigma (mkApp (Lazy.force coq_all, [| dom; lam |])) ty cstr evars in
	    (match res with
	    | Some (Some r) -> Some (Some { r with rew_to = unfold_all r.rew_to })
	    | _ -> res)

      | Lambda (n, t, b) when flags.under_lambdas ->
	  let env' = Environ.push_rel (n, None, t) env in
	  let b' = s env' sigma b (Typing.type_of env' sigma b) (unlift_cstr env sigma cstr) evars in
	    (match b' with
	    | Some (Some r) ->
		let prf = match r.rew_prf with
		  | RewPrf (rel, prf) ->
		      let rel = pointwise_or_dep_relation n t r.rew_car rel in
		      let prf = mkLambda (n, t, prf) in
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
	  let cty = Typing.type_of env sigma c in
	  let cstr' = Some (mkApp (Lazy.force coq_eq, [| cty |])) in
	  let c' = s env sigma c cty cstr' evars in
	    (match c' with
	    | Some (Some r) ->
		Some (Some (make_leibniz_proof (mkCase (ci, lift 1 p, mkRel 1, Array.map (lift 1) brs)) ty r))
	    | x ->
		if array_for_all ((=) 0) ci.ci_cstr_ndecls then
		  let cstr = Some (mkApp (Lazy.force coq_eq, [| ty |])) in
		  let found, brs' = Array.fold_left (fun (found, acc) br ->
		    if found <> None then (found, fun x -> lift 1 br :: acc x)
		    else
		      match s env sigma br ty cstr evars with
		      | Some (Some r) -> (Some r, fun x -> mkRel 1 :: acc x)
		      | _ -> (None, fun x -> lift 1 br :: acc x))
		    (None, fun x -> []) brs
		  in
		    match found with
		    | Some r ->
			let ctxc = mkCase (ci, lift 1 p, lift 1 c, Array.of_list (List.rev (brs' x))) in
			  Some (Some (make_leibniz_proof ctxc ty r))
		    | None -> x
		else
		  match try Some (fold_match env sigma t) with Not_found -> None with
		  | None -> x
		  | Some (cst, _, t') ->
		      match aux env sigma t' ty cstr evars with
		      | Some (Some prf) -> Some (Some { prf with
			  rew_from = t; rew_to = unfold_match env sigma cst prf.rew_to })
		      | x' -> x)

      | _ -> if all then Some None else None
  in aux

let all_subterms = subterm true default_flags
let one_subterm = subterm false default_flags

(** Requires transitivity of the rewrite step, if not a reduction.
    Not tail-recursive. *)

let transitivity env sigma (res : rewrite_result_info) (next : strategy) : rewrite_result option =
  match next env sigma res.rew_to res.rew_car (get_rew_rel res.rew_prf) res.rew_evars with
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

    let fail : strategy =
      fun env sigma t ty cstr evars -> None

    let id : strategy =
      fun env sigma t ty cstr evars -> Some None

    let refl : strategy =
      fun env sigma t ty cstr evars ->
	let evars, rel = match cstr with
	  | None -> new_cstr_evar evars env (mk_relation ty)
	  | Some r -> evars, r
	in
	let evars, proof =
	  let mty = mkApp (Lazy.force proper_proxy_type, [| ty ; rel; t |]) in
	    new_cstr_evar evars env mty
	in
	  Some (Some { rew_car = ty; rew_from = t; rew_to = t;
		       rew_prf = RewPrf (rel, proof); rew_evars = evars })

    let progress (s : strategy) : strategy =
      fun env sigma t ty cstr evars ->
	match s env sigma t ty cstr evars with
	| None -> None
	| Some None -> None
	| r -> r

    let seq fst snd : strategy =
      fun env sigma t ty cstr evars ->
	match fst env sigma t ty cstr evars with
	| None -> None
	| Some None -> snd env sigma t ty cstr evars
	| Some (Some res) -> transitivity env sigma res snd

    let choice fst snd : strategy =
      fun env sigma t ty cstr evars ->
	match fst env sigma t ty cstr evars with
	| None -> snd env sigma t ty cstr evars
	| res -> res

    let try_ str : strategy = choice str id

    let fix (f : strategy -> strategy) : strategy =
      let rec aux env = f (fun env -> aux env) env in aux

    let any (s : strategy) : strategy =
      fix (fun any -> try_ (seq s any))

    let repeat (s : strategy) : strategy =
      seq s (any s)

    let bu (s : strategy) : strategy =
      fix (fun s' -> seq (choice (progress (all_subterms s')) s) (try_ s'))

    let td (s : strategy) : strategy =
      fix (fun s' -> seq (choice s (progress (all_subterms s'))) (try_ s'))

    let innermost (s : strategy) : strategy =
      fix (fun ins -> choice (one_subterm ins) s)

    let outermost (s : strategy) : strategy =
      fix (fun out -> choice s (one_subterm out))

    let lemmas cs : strategy =
      List.fold_left (fun tac (l,l2r) ->
	choice tac (apply_lemma l l2r (false,[])))
	fail cs

    let inj_open c = (Evd.empty,c)

    let old_hints (db : string) : strategy =
      let rules = Autorewrite.find_rewrites db in
	lemmas (List.map (fun hint -> (inj_open (hint.Autorewrite.rew_lemma, NoBindings), hint.Autorewrite.rew_l2r)) rules)

    let hints (db : string) : strategy =
      fun env sigma t ty cstr evars ->
      let rules = Autorewrite.find_matches db t in
	lemmas (List.map (fun hint -> (inj_open (hint.Autorewrite.rew_lemma, NoBindings), hint.Autorewrite.rew_l2r)) rules)
	    env sigma t ty cstr evars

    let reduce (r : Redexpr.red_expr) : strategy =
      let rfn, ckind = Redexpr.reduction_of_red_expr r in
	fun env sigma t ty cstr evars ->
	  let t' = rfn env sigma t in
	    if eq_constr t' t then
	      Some None
	    else
	      Some (Some { rew_car = ty; rew_from = t; rew_to = t';
			   rew_prf = RewCast ckind; rew_evars = evars })
	  

end

(** The strategy for a single rewrite, dealing with occurences. *)

let rewrite_strat flags occs hyp =
  let app = apply_rule hyp occs in
  let rec aux () =
    Strategies.choice app (subterm true flags (fun env -> aux () env))
  in aux ()

let rewrite_with {it = c; sigma = evm} left2right loccs : strategy =
  fun env sigma ->
    let evars = Evd.merge sigma evm in
    let hypinfo = ref (decompose_applied_relation env evars c left2right) in
      rewrite_strat default_flags loccs hypinfo env sigma

let apply_strategy (s : strategy) env sigma concl cstr evars =
  let res =
    s env sigma concl (Typing.type_of env sigma concl)
      (Option.map snd cstr) !evars
  in
    match res with
    | None -> None
    | Some None -> Some None
    | Some (Some res) ->
	evars := res.rew_evars;
	Some (Some (res.rew_prf, (res.rew_car, res.rew_from, res.rew_to)))

let split_evars_once sigma evd =
  Evd.fold (fun ev evi deps ->
    if Intset.mem ev deps then
      Intset.union (Class_tactics.evars_of_evi evi) deps
    else deps) evd sigma

let existentials_of_evd evd =
  Evd.fold (fun ev evi acc -> Intset.add ev acc) evd Intset.empty

let evd_of_existentials evd exs =
  Intset.fold (fun i acc ->
    let evi = Evd.find evd i in
      Evd.add acc i evi) exs Evd.empty

let split_evars sigma evd =
  let rec aux deps =
    let deps' = split_evars_once deps evd in
      if Intset.equal deps' deps then
	evd_of_existentials evd deps
      else aux deps'
  in aux (existentials_of_evd sigma)

let merge_evars (goal,cstr) = Evd.merge goal cstr
let solve_constraints env evars =
  Typeclasses.resolve_typeclasses env ~split:false ~fail:true (merge_evars evars)

let nf_zeta =
  Reductionops.clos_norm_flags (Closure.RedFlags.mkflags [Closure.RedFlags.fZETA])

let map_rewprf f = function
  | RewPrf (rel, prf) -> RewPrf (f rel, f prf)
  | RewCast c -> RewCast c

exception RewriteFailure

let cl_rewrite_clause_aux ?(abs=None) strat goal_meta clause gl =
  let concl, is_hyp =
    match clause with
	Some id -> pf_get_hyp_typ gl id, Some id
      | None -> pf_concl gl, None
  in
  let cstr =
    let sort = mkProp in
    let impl = Lazy.force impl in
      match is_hyp with
      | None -> (sort, inverse sort impl)
      | Some _ -> (sort, impl)
  in
  let sigma = project gl in
  let evars = ref (Evd.create_evar_defs sigma, Evd.empty) in
  let env = pf_env gl in
  let eq = apply_strategy strat env sigma concl (Some cstr) evars in
    match eq with
    | Some (Some (p, (car, oldt, newt))) ->
	(try
	    let cstrevars = !evars in
	    let evars = solve_constraints env cstrevars in
	    let p = map_rewprf 
	      (fun p -> nf_zeta env evars (Evarutil.nf_evar evars p)) 
	      p 
	    in
	    let newt = Evarutil.nf_evar evars newt in
	    let abs = Option.map (fun (x, y) ->
	      Evarutil.nf_evar evars x, Evarutil.nf_evar evars y) abs in
	    let undef = split_evars (fst cstrevars) evars in
	    let rewtac =
	      match is_hyp with
	      | Some id ->
		  (match p with
		  | RewPrf (rel, p) ->
		      let term =
			match abs with
			| None -> p
			| Some (t, ty) ->
			    mkApp (mkLambda (Name (id_of_string "lemma"), ty, p), [| t |])
		      in
			cut_replacing id newt
			  (Tacmach.refine_no_check (mkApp (term, [| mkVar id |])))
		  | RewCast c ->
		      change_in_hyp None newt (id, InHypTypeOnly))
		    
	      | None ->
		  (match p with
		  | RewPrf (rel, p) ->
		      (match abs with
		      | None ->
			  let name = next_name_away_with_default "H" Anonymous (pf_ids_of_hyps gl) in
			    tclTHENLAST
			      (Tacmach.internal_cut_no_check false name newt)
			      (tclTHEN (Tactics.revert [name]) (Tacmach.refine_no_check p))
		      | Some (t, ty) ->
			  Tacmach.refine_no_check
			    (mkApp (mkLambda (Name (id_of_string "newt"), newt,
					     mkLambda (Name (id_of_string "lemma"), ty,
						      mkApp (p, [| mkRel 2 |]))),
				   [| mkMeta goal_meta; t |])))
		  | RewCast c -> 
		      change_in_concl None newt)
	    in
	    let evartac =
	      if not (Evd.is_empty undef) then
		Refiner.tclEVARS evars
	      else tclIDTAC
	    in tclTHENLIST [evartac; rewtac] gl
	  with
	  | Loc.Exc_located (_, TypeClassError (env, (UnsatisfiableConstraints _ as e)))
	  | TypeClassError (env, (UnsatisfiableConstraints _ as e)) ->
	      Refiner.tclFAIL_lazy 0
		(lazy (str"setoid rewrite failed: unable to satisfy the rewriting constraints."
			++ fnl () ++ Himsg.explain_typeclass_error env e)) gl)
    | Some None ->
	tclFAIL 0 (str"setoid rewrite failed: no progress made") gl
    | None -> raise RewriteFailure

let cl_rewrite_clause_strat strat clause gl =
  init_setoid ();
  let meta = Evarutil.new_meta() in
  let gl = { gl with sigma = Typeclasses.mark_unresolvables gl.sigma } in
    try cl_rewrite_clause_aux strat meta clause gl
    with RewriteFailure ->
      tclFAIL 0 (str"setoid rewrite failed: strategy failed") gl

let cl_rewrite_clause l left2right occs clause gl =
  cl_rewrite_clause_strat (rewrite_with l left2right occs) clause gl

open Pp
open Pcoq
open Names
open Tacexpr
open Tacinterp
open Termops
open Genarg
open Extraargs

let occurrences_of = function
  | n::_ as nl when n < 0 -> (false,List.map abs nl)
  | nl ->
      if List.exists (fun n -> n < 0) nl then
	error "Illegal negative occurrence number.";
      (true,nl)

let pr_strategy _ _ _ (s : strategy) = Pp.str "<strategy>"

let interp_strategy ist gl c = c
let glob_strategy ist l = l
let subst_strategy evm l = l

let apply_constr_expr c l2r occs = fun env sigma ->
  let evd, c = Constrintern.interp_open_constr sigma env c in
    apply_lemma (evd, (c, NoBindings)) l2r occs env sigma

let interp_constr_list env sigma =
  List.map (fun c -> 
	      let evd, c = Constrintern.interp_open_constr sigma env c in
		(evd, (c, NoBindings)), true)

open Pcoq

let _ =
  (Genarg.create_arg "strategy" :
      ((strategy, Genarg.tlevel) Genarg.abstract_argument_type *
	  (strategy, Genarg.glevel) Genarg.abstract_argument_type *
	  (strategy, Genarg.rlevel) Genarg.abstract_argument_type))


ARGUMENT EXTEND rewstrategy TYPED AS strategy
    PRINTED BY pr_strategy
    INTERPRETED BY interp_strategy
    GLOBALIZED BY glob_strategy
    SUBSTITUTED BY subst_strategy

    [ constr(c) ] -> [ apply_constr_expr c true all_occurrences ]
  | [ "<-" constr(c) ] -> [ apply_constr_expr c false all_occurrences ]
  | [ "subterms" rewstrategy(h) ] -> [ all_subterms h ]
  | [ "subterm" rewstrategy(h) ] -> [ one_subterm h ]
  | [ "innermost" rewstrategy(h) ] -> [ Strategies.innermost h ]
  | [ "outermost" rewstrategy(h) ] -> [ Strategies.outermost h ]
  | [ "bottomup" rewstrategy(h) ] -> [ Strategies.bu h ]
  | [ "topdown" rewstrategy(h) ] -> [ Strategies.td h ]
  | [ "id" ] -> [ Strategies.id ]
  | [ "refl" ] -> [ Strategies.refl ]
  | [ "progress" rewstrategy(h) ] -> [ Strategies.progress h ]
  | [ "fail" ] -> [ Strategies.fail ]
  | [ "try" rewstrategy(h) ] -> [ Strategies.try_ h ]
  | [ "any" rewstrategy(h) ] -> [ Strategies.any h ]
  | [ "repeat" rewstrategy(h) ] -> [ Strategies.repeat h ]
  | [ rewstrategy(h) ";" rewstrategy(h') ] -> [ Strategies.seq h h' ]
  | [ "(" rewstrategy(h) ")" ] -> [ h ]
  | [ "choice" rewstrategy(h) rewstrategy(h') ] -> [ Strategies.choice h h' ]
  | [ "old_hints" preident(h) ] -> [ Strategies.old_hints h ]
  | [ "hints" preident(h) ] -> [ Strategies.hints h ]
  | [ "terms" constr_list(h) ] -> [ fun env sigma -> 
      Strategies.lemmas (interp_constr_list env sigma h) env sigma ]
  | [ "eval" red_expr(r) ] -> [ fun env sigma -> 
      Strategies.reduce (Tacinterp.interp_redexp env sigma r) env sigma ]
END

TACTIC EXTEND class_rewrite
| [ "clrewrite" orient(o) constr_with_bindings(c) "in" hyp(id) "at" occurrences(occ) ] -> [ cl_rewrite_clause c o (occurrences_of occ) (Some id) ]
| [ "clrewrite" orient(o) constr_with_bindings(c) "at" occurrences(occ) "in" hyp(id) ] -> [ cl_rewrite_clause c o (occurrences_of occ) (Some id) ]
| [ "clrewrite" orient(o) constr_with_bindings(c) "in" hyp(id) ] -> [ cl_rewrite_clause c o all_occurrences (Some id) ]
| [ "clrewrite" orient(o) constr_with_bindings(c) "at" occurrences(occ) ] -> [ cl_rewrite_clause c o (occurrences_of occ) None ]
| [ "clrewrite" orient(o) constr_with_bindings(c) ] -> [ cl_rewrite_clause c o all_occurrences None ]
    END

TACTIC EXTEND class_rewrite_strat
| [ "clrewrite_strat" rewstrategy(s) ] -> [ cl_rewrite_clause_strat s None ]
(* | [ "clrewrite_strat" strategy(s) "in" hyp(id) ] -> [ cl_rewrite_clause_strat s (Some id) ] *)
END


let clsubstitute o c =
  let is_tac id = match kind_of_term (fst c.it) with Var id' when id' = id -> true | _ -> false in
    Tacticals.onAllHypsAndConcl
      (fun cl ->
	match cl with
	  | Some id when is_tac id -> tclIDTAC
	  | _ -> tclTRY (cl_rewrite_clause c o all_occurrences cl))

TACTIC EXTEND substitute
| [ "substitute" orient(o) constr_with_bindings(c) ] -> [ clsubstitute o c ]
END


(* Compatibility with old Setoids *)

TACTIC EXTEND setoid_rewrite
   [ "setoid_rewrite" orient(o) constr_with_bindings(c) ]
   -> [ cl_rewrite_clause c o all_occurrences None ]
 | [ "setoid_rewrite" orient(o) constr_with_bindings(c) "in" hyp(id) ] ->
      [ cl_rewrite_clause c o all_occurrences (Some id)]
 | [ "setoid_rewrite" orient(o) constr_with_bindings(c) "at" occurrences(occ) ] ->
      [ cl_rewrite_clause c o (occurrences_of occ) None]
 | [ "setoid_rewrite" orient(o) constr_with_bindings(c) "at" occurrences(occ) "in" hyp(id)] ->
      [ cl_rewrite_clause c o (occurrences_of occ) (Some id)]
 | [ "setoid_rewrite" orient(o) constr_with_bindings(c) "in" hyp(id) "at" occurrences(occ)] ->
      [ cl_rewrite_clause c o (occurrences_of occ) (Some id)]
END

(* let solve_obligation lemma =  *)
(*   tclTHEN (Tacinterp.interp (Tacexpr.TacAtom (dummy_loc, Tacexpr.TacAnyConstructor None))) *)
(*     (eapply_with_bindings (Constrintern.interp_constr Evd.empty (Global.env()) lemma, NoBindings)) *)

let mkappc s l = CAppExpl (dummy_loc,(None,(Libnames.Ident (dummy_loc,id_of_string s))),l)

let declare_an_instance n s args =
  ((dummy_loc,Name n), Explicit,
  CAppExpl (dummy_loc, (None, Qualid (dummy_loc, qualid_of_string s)),
	   args))

let declare_instance a aeq n s = declare_an_instance n s [a;aeq]

let anew_instance binders instance fields =
  new_instance binders instance (CRecord (dummy_loc,None,fields)) ~generalize:false None

let declare_instance_refl binders a aeq n lemma =
  let instance = declare_instance a aeq (add_suffix n "_Reflexive") "Coq.Classes.RelationClasses.Reflexive"
  in anew_instance binders instance
       [(Ident (dummy_loc,id_of_string "reflexivity"),lemma)]

let declare_instance_sym binders a aeq n lemma =
  let instance = declare_instance a aeq (add_suffix n "_Symmetric") "Coq.Classes.RelationClasses.Symmetric"
  in anew_instance binders instance
       [(Ident (dummy_loc,id_of_string "symmetry"),lemma)]

let declare_instance_trans binders a aeq n lemma =
  let instance = declare_instance a aeq (add_suffix n "_Transitive") "Coq.Classes.RelationClasses.Transitive"
  in anew_instance binders instance
       [(Ident (dummy_loc,id_of_string "transitivity"),lemma)]

let declare_relation ?(binders=[]) a aeq n refl symm trans =
  init_setoid ();
  let instance = declare_instance a aeq (add_suffix n "_relation") "Coq.Classes.RelationClasses.RewriteRelation"
  in ignore(anew_instance binders instance []);
  match (refl,symm,trans) with
      (None, None, None) -> ()
    | (Some lemma1, None, None) ->
	ignore (declare_instance_refl binders a aeq n lemma1)
    | (None, Some lemma2, None) ->
	ignore (declare_instance_sym binders a aeq n lemma2)
    | (None, None, Some lemma3) ->
	ignore (declare_instance_trans binders a aeq n lemma3)
    | (Some lemma1, Some lemma2, None) ->
	ignore (declare_instance_refl binders a aeq n lemma1);
	ignore (declare_instance_sym binders a aeq n lemma2)
    | (Some lemma1, None, Some lemma3) ->
	let _lemma_refl = declare_instance_refl binders a aeq n lemma1 in
	let _lemma_trans = declare_instance_trans binders a aeq n lemma3 in
	let instance = declare_instance a aeq n "Coq.Classes.RelationClasses.PreOrder"
	in ignore(
	    anew_instance binders instance
	      [(Ident (dummy_loc,id_of_string "PreOrder_Reflexive"), lemma1);
	       (Ident (dummy_loc,id_of_string "PreOrder_Transitive"),lemma3)])
    | (None, Some lemma2, Some lemma3) ->
	let _lemma_sym = declare_instance_sym binders a aeq n lemma2 in
	let _lemma_trans = declare_instance_trans binders a aeq n lemma3 in
	let instance = declare_instance a aeq n "Coq.Classes.RelationClasses.PER"
	in ignore(
	    anew_instance binders instance
	      [(Ident (dummy_loc,id_of_string "PER_Symmetric"), lemma2);
	       (Ident (dummy_loc,id_of_string "PER_Transitive"),lemma3)])
     | (Some lemma1, Some lemma2, Some lemma3) ->
	let _lemma_refl = declare_instance_refl binders a aeq n lemma1 in
	let _lemma_sym = declare_instance_sym binders a aeq n lemma2 in
	let _lemma_trans = declare_instance_trans binders a aeq n lemma3 in
	let instance = declare_instance a aeq n "Coq.Classes.RelationClasses.Equivalence"
	in ignore(
	  anew_instance binders instance
	    [(Ident (dummy_loc,id_of_string "Equivalence_Reflexive"), lemma1);
	     (Ident (dummy_loc,id_of_string "Equivalence_Symmetric"), lemma2);
	     (Ident (dummy_loc,id_of_string "Equivalence_Transitive"), lemma3)])

type 'a binders_argtype = (local_binder list, 'a) Genarg.abstract_argument_type

let _, _, rawwit_binders =
 (Genarg.create_arg "binders" :
    Genarg.tlevel binders_argtype *
    Genarg.glevel binders_argtype *
    Genarg.rlevel binders_argtype)

open Pcoq.Constr

VERNAC COMMAND EXTEND AddRelation
  | [ "Add" "Relation" constr(a) constr(aeq) "reflexivity" "proved" "by" constr(lemma1)
	"symmetry" "proved" "by" constr(lemma2) "as" ident(n) ] ->
      [ declare_relation a aeq n (Some lemma1) (Some lemma2) None ]

  | [ "Add" "Relation" constr(a) constr(aeq) "reflexivity" "proved" "by" constr(lemma1)
	"as" ident(n) ] ->
      [ declare_relation a aeq n (Some lemma1) None None ]
  | [ "Add" "Relation" constr(a) constr(aeq)  "as" ident(n) ] ->
      [ declare_relation a aeq n None None None ]
END

VERNAC COMMAND EXTEND AddRelation2
    [ "Add" "Relation" constr(a) constr(aeq) "symmetry" "proved" "by" constr(lemma2)
      "as" ident(n) ] ->
      [ declare_relation a aeq n None (Some lemma2) None ]
  | [ "Add" "Relation" constr(a) constr(aeq) "symmetry" "proved" "by" constr(lemma2) "transitivity" "proved" "by" constr(lemma3)  "as" ident(n) ] ->
      [ declare_relation a aeq n None (Some lemma2) (Some lemma3) ]
END

VERNAC COMMAND EXTEND AddRelation3
    [ "Add" "Relation" constr(a) constr(aeq) "reflexivity" "proved" "by" constr(lemma1)
      "transitivity" "proved" "by" constr(lemma3) "as" ident(n) ] ->
      [ declare_relation a aeq n (Some lemma1) None (Some lemma3) ]
  | [ "Add" "Relation" constr(a) constr(aeq) "reflexivity" "proved" "by" constr(lemma1)
      "symmetry" "proved" "by" constr(lemma2) "transitivity" "proved" "by" constr(lemma3)
      "as" ident(n) ] ->
      [ declare_relation a aeq n (Some lemma1) (Some lemma2) (Some lemma3) ]
  | [ "Add" "Relation" constr(a) constr(aeq) "transitivity" "proved" "by" constr(lemma3)
	"as" ident(n) ] ->
      [ declare_relation a aeq n None None (Some lemma3) ]
END

VERNAC COMMAND EXTEND AddParametricRelation
  | [ "Add" "Parametric" "Relation" binders(b) ":" constr(a) constr(aeq)
	"reflexivity" "proved" "by" constr(lemma1)
	"symmetry" "proved" "by" constr(lemma2) "as" ident(n) ] ->
      [ declare_relation ~binders:b a aeq n (Some lemma1) (Some lemma2) None ]
  | [ "Add" "Parametric" "Relation" binders(b) ":" constr(a) constr(aeq)
	"reflexivity" "proved" "by" constr(lemma1)
	"as" ident(n) ] ->
      [ declare_relation ~binders:b a aeq n (Some lemma1) None None ]
  | [ "Add" "Parametric" "Relation" binders(b) ":" constr(a) constr(aeq)  "as" ident(n) ] ->
      [ declare_relation ~binders:b a aeq n None None None ]
END

VERNAC COMMAND EXTEND AddParametricRelation2
    [ "Add" "Parametric" "Relation" binders(b) ":" constr(a) constr(aeq) "symmetry" "proved" "by" constr(lemma2)
      "as" ident(n) ] ->
      [ declare_relation ~binders:b a aeq n None (Some lemma2) None ]
  | [ "Add" "Parametric" "Relation" binders(b) ":" constr(a) constr(aeq) "symmetry" "proved" "by" constr(lemma2) "transitivity" "proved" "by" constr(lemma3)  "as" ident(n) ] ->
      [ declare_relation ~binders:b a aeq n None (Some lemma2) (Some lemma3) ]
END

VERNAC COMMAND EXTEND AddParametricRelation3
    [ "Add" "Parametric" "Relation" binders(b) ":" constr(a) constr(aeq) "reflexivity" "proved" "by" constr(lemma1)
      "transitivity" "proved" "by" constr(lemma3) "as" ident(n) ] ->
      [ declare_relation ~binders:b a aeq n (Some lemma1) None (Some lemma3) ]
  | [ "Add" "Parametric" "Relation" binders(b) ":" constr(a) constr(aeq) "reflexivity" "proved" "by" constr(lemma1)
      "symmetry" "proved" "by" constr(lemma2) "transitivity" "proved" "by" constr(lemma3)
      "as" ident(n) ] ->
      [ declare_relation ~binders:b a aeq n (Some lemma1) (Some lemma2) (Some lemma3) ]
  | [ "Add" "Parametric" "Relation" binders(b) ":" constr(a) constr(aeq) "transitivity" "proved" "by" constr(lemma3)
	"as" ident(n) ] ->
      [ declare_relation ~binders:b a aeq n None None (Some lemma3) ]
END

let cHole = CHole (dummy_loc, None)

open Entries
open Libnames

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
  let typ = Typing.type_of (Global.env ()) Evd.empty term in
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
	      mkApp (f, fst (array_chop (Array.length args - 2) args))
	  | _ -> typ
      in aux init
    in
    let ctx,ccl = Reductionops.splay_prod_n (Global.env()) Evd.empty (3 * n) typ
    in it_mkProd_or_LetIn ccl ctx
  in
  let typ = it_mkProd_or_LetIn typ ctx in
  let cst =
    { const_entry_body = term;
      const_entry_type = Some typ;
      const_entry_opaque = false;
      const_entry_boxed = false;
      const_entry_inline_code = false }
  in
    ignore(Declare.declare_constant n (Entries.DefinitionEntry cst, Decl_kinds.IsDefinition Decl_kinds.Definition))

let build_morphism_signature m =
  let env = Global.env () in
  let m = Constrintern.interp_constr Evd.empty env m in
  let t = Typing.type_of env Evd.empty m in
  let isevars = ref (Evd.empty, Evd.empty) in
  let cstrs =
    let rec aux t =
      match kind_of_term t with
	| Prod (na, a, b) ->
	    None :: aux b
	| _ -> []
    in aux t
  in
  let evars, t', sig_, cstrs = build_signature !isevars env t cstrs None in
  let _ = isevars := evars in
  let _ = List.iter
    (fun (ty, rel) ->
      Option.iter (fun rel ->
	let default = mkApp (Lazy.force default_relation, [| ty; rel |]) in
	let evars,c = new_cstr_evar !isevars env default in
	  isevars := evars)
	rel)
    cstrs
  in
  let morph =
    mkApp (Lazy.force proper_type, [| t; sig_; m |])
  in
  let evd = solve_constraints env !isevars in
  let m = Evarutil.nf_evar evd morph in
    Evarutil.check_evars env Evd.empty evd m; m

let default_morphism sign m =
  let env = Global.env () in
  let t = Typing.type_of env Evd.empty m in
  let evars, _, sign, cstrs =
    build_signature (Evd.empty,Evd.empty) env t (fst sign) (snd sign)
  in
  let morph =
    mkApp (Lazy.force proper_type, [| t; sign; m |])
  in
  let evars, mor = resolve_one_typeclass env (merge_evars evars) morph in
    mor, proper_projection mor morph

let add_setoid binders a aeq t n =
  init_setoid ();
  let _lemma_refl = declare_instance_refl binders a aeq n (mkappc "Seq_refl" [a;aeq;t]) in
  let _lemma_sym = declare_instance_sym binders a aeq n (mkappc "Seq_sym" [a;aeq;t]) in
  let _lemma_trans = declare_instance_trans binders a aeq n (mkappc "Seq_trans" [a;aeq;t]) in
  let instance = declare_instance a aeq n "Coq.Classes.RelationClasses.Equivalence"
  in ignore(
    anew_instance binders instance
      [(Ident (dummy_loc,id_of_string "Equivalence_Reflexive"), mkappc "Seq_refl" [a;aeq;t]);
       (Ident (dummy_loc,id_of_string "Equivalence_Symmetric"), mkappc "Seq_sym" [a;aeq;t]);
       (Ident (dummy_loc,id_of_string "Equivalence_Transitive"), mkappc "Seq_trans" [a;aeq;t])])

let add_morphism_infer glob m n =
  init_setoid ();
  let instance_id = add_suffix n "_Proper" in
  let instance = build_morphism_signature m in
    if Lib.is_modtype () then
      let cst = Declare.declare_constant ~internal:Declare.KernelSilent instance_id
				(Entries.ParameterEntry (instance,false), Decl_kinds.IsAssumption Decl_kinds.Logical)
      in
	add_instance (Typeclasses.new_instance (Lazy.force proper_class) None glob (ConstRef cst));
	declare_projection n instance_id (ConstRef cst)
    else
      let kind = Decl_kinds.Global, Decl_kinds.DefinitionBody Decl_kinds.Instance in
	Flags.silently
	  (fun () ->
	    Lemmas.start_proof instance_id kind instance
	      (fun _ -> function
		Libnames.ConstRef cst ->
		  add_instance (Typeclasses.new_instance (Lazy.force proper_class) None
				   glob (ConstRef cst));
		  declare_projection n instance_id (ConstRef cst)
		| _ -> assert false);
	    Pfedit.by (Tacinterp.interp <:tactic< Coq.Classes.SetoidTactics.add_morphism_tactic>>)) ();
	Flags.if_verbose (fun x -> msg (Printer.pr_open_subgoals x)) ()

let add_morphism glob binders m s n =
  init_setoid ();
  let instance_id = add_suffix n "_Proper" in
  let instance =
    ((dummy_loc,Name instance_id), Explicit,
    CAppExpl (dummy_loc,
	     (None, Qualid (dummy_loc, Libnames.qualid_of_string "Coq.Classes.Morphisms.Proper")),
	     [cHole; s; m]))
  in
  let tac = Tacinterp.interp <:tactic<add_morphism_tactic>> in
    ignore(new_instance ~global:glob binders instance (CRecord (dummy_loc,None,[]))
	      ~generalize:false ~tac ~hook:(declare_projection n instance_id) None)

VERNAC COMMAND EXTEND AddSetoid1
   [ "Add" "Setoid" constr(a) constr(aeq) constr(t) "as" ident(n) ] ->
     [ add_setoid [] a aeq t n ]
  | [ "Add" "Parametric" "Setoid" binders(binders) ":" constr(a) constr(aeq) constr(t) "as" ident(n) ] ->
     [	add_setoid binders a aeq t n ]
  | [ "Add" "Morphism" constr(m) ":" ident(n) ] ->
      [ add_morphism_infer (not (Vernacexpr.use_section_locality ())) m n ]
  | [ "Add" "Morphism" constr(m) "with" "signature" lconstr(s) "as" ident(n) ] ->
      [ add_morphism (not (Vernacexpr.use_section_locality ())) [] m s n ]
  | [ "Add" "Parametric" "Morphism" binders(binders) ":" constr(m)
	"with" "signature" lconstr(s) "as" ident(n) ] ->
      [ add_morphism (not (Vernacexpr.use_section_locality ())) binders m s n ]
END

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

let unification_rewrite l2r c1 c2 cl car rel but gl =
  let env = pf_env gl in
  let (evd',c') =
    try
      (* ~flags:(false,true) to allow to mark occurrences that must not be
         rewritten simply by replacing them with let-defined definitions
         in the context *)
      Unification.w_unify_to_subterm ~flags:rewrite_unif_flags env ((if l2r then c1 else c2),but) cl.evd
    with
	Pretype_errors.PretypeError _ ->
	  (* ~flags:(true,true) to make Ring work (since it really
             exploits conversion) *)
	  Unification.w_unify_to_subterm ~flags:rewrite2_unif_flags
	    env ((if l2r then c1 else c2),but) cl.evd
  in
  let evd' = Typeclasses.resolve_typeclasses ~fail:false env evd' in
  let cl' = {cl with evd = evd'} in
  let cl' = Clenvtac.clenv_pose_dependent_evars true cl' in
  let nf c = Evarutil.nf_evar ( cl'.evd) (Clenv.clenv_nf_meta cl' c) in
  let c1 = if l2r then nf c' else nf c1
  and c2 = if l2r then nf c2 else nf c'
  and car = nf car and rel = nf rel in
  check_evar_map_of_evars_defs cl'.evd;
  let prf = nf (Clenv.clenv_value cl') and prfty = nf (Clenv.clenv_type cl') in
  let cl' = { cl' with templval = mk_freelisted prf ; templtyp = mk_freelisted prfty } in
    {cl=cl'; prf=(mkRel 1); car=car; rel=rel; l2r=l2r; c1=c1; c2=c2; c=None; abs=Some (prf, prfty)}

let get_hyp gl evars (c,l) clause l2r =
  let hi = decompose_applied_relation (pf_env gl) evars (c,l) l2r in
  let but = match clause with Some id -> pf_get_hyp_typ gl id | None -> pf_concl gl in
    unification_rewrite hi.l2r hi.c1 hi.c2 hi.cl hi.car hi.rel but gl

let general_rewrite_flags = { under_lambdas = false; on_morphisms = true }

let apply_lemma gl (c,l) cl l2r occs =
  let sigma = project gl in
  let hypinfo = ref (get_hyp gl sigma (c,l) cl l2r) in
  let app = apply_rule hypinfo occs in
  let rec aux () =
    Strategies.choice app (subterm true general_rewrite_flags (fun env -> aux () env))
  in !hypinfo, aux ()

let general_s_rewrite cl l2r occs (c,l) ~new_goals gl =
  let meta = Evarutil.new_meta() in
  let hypinfo, strat = apply_lemma gl (c,l) cl l2r occs in
    try
      tclWEAK_PROGRESS 
	(tclTHEN
            (Refiner.tclEVARS hypinfo.cl.evd)
            (cl_rewrite_clause_aux ~abs:hypinfo.abs strat meta cl)) gl
    with RewriteFailure ->
      let {l2r=l2r; c1=x; c2=y} = hypinfo in
	raise (Pretype_errors.PretypeError
		  (pf_env gl,
		  Pretype_errors.NoOccurrenceFound ((if l2r then x else y), cl)))

let general_s_rewrite_clause x =
  init_setoid ();
  match x with
    | None -> general_s_rewrite None
    | Some id -> general_s_rewrite (Some id)

let _ = Equality.register_general_rewrite_clause general_s_rewrite_clause

(** [setoid_]{reflexivity,symmetry,transitivity} tactics *)

let not_declared env ty rel =
  tclFAIL 0 (str" The relation " ++ Printer.pr_constr_env env rel ++ str" is not a declared " ++
		str ty ++ str" relation. Maybe you need to require the Setoid library")

let setoid_proof gl ty fn fallback =
  let env = pf_env gl in
    try
      let rel, args = decompose_app_rel env (project gl) (pf_concl gl) in
      let evm, car = project gl, pf_type_of gl args.(0) in
	fn env evm car rel gl
    with e ->
      try fallback gl
      with Hipattern.NoEquationFound ->
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
      | Some c -> apply_with_bindings (proof,Rawterm.ImplicitBindings [ c ]))
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

let _ = Tactics.register_setoid_reflexivity setoid_reflexivity
let _ = Tactics.register_setoid_symmetry setoid_symmetry
let _ = Tactics.register_setoid_symmetry_in setoid_symmetry_in
let _ = Tactics.register_setoid_transitivity setoid_transitivity

TACTIC EXTEND setoid_symmetry
   [ "setoid_symmetry" ] -> [ setoid_symmetry ]
 | [ "setoid_symmetry" "in" hyp(n) ] -> [ setoid_symmetry_in n ]
END

TACTIC EXTEND setoid_reflexivity
[ "setoid_reflexivity" ] -> [ setoid_reflexivity ]
END

TACTIC EXTEND setoid_transitivity
  [ "setoid_transitivity" constr(t) ] -> [ setoid_transitivity (Some t) ]
| [ "setoid_etransitivity" ] -> [ setoid_transitivity None ]
END

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
	let app = mkApp (arrow_morphism tyhd (subst1 mkProp tyconcl), [| ty; (subst1 mkProp concl) |]) in
	  it_mkProd_or_LetIn app tl
    | _ -> ctype
  in convert_hyp_no_check (id, b, ctype') gl

TACTIC EXTEND implify
[ "implify" hyp(n) ] -> [ implify n ]
END

let rec fold_matches env sigma c =
  map_constr_with_full_binders Environ.push_rel 
    (fun env c ->
      match kind_of_term c with
      | Case _ ->
          let cst, env, c' = fold_match ~force:true env sigma c in
	    fold_matches env sigma c'
      | _ -> fold_matches env sigma c)
    env c

TACTIC EXTEND fold_match
[ "fold_match" constr(c) ] -> [ fun gl -> 
  let _, _, c' = fold_match ~force:true (pf_env gl) (project gl) c in
    change (Some (snd (pattern_of_constr (project gl) c))) c' onConcl gl ]
END

TACTIC EXTEND fold_matches
| [ "fold_matches" constr(c) ] -> [ fun gl -> 
  let c' = fold_matches (pf_env gl) (project gl) c in
    change (Some (snd (pattern_of_constr (project gl) c))) c' onConcl gl ]
END
