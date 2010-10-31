(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Created by Hugo Herbelin for Coq V7 by isolating the coercion
   mechanism out of the type inference algorithm in file trad.ml from
   Coq V6.3, Nov 1999; The coercion mechanism was implemented in
   trad.ml by Amokrane Saïbi, May 1996 *)
(* Addition of products and sorts in canonical structures by Pierre
   Corbineau, Feb 2008 *)
(* Turned into an abstract compilation unit by Matthieu Sozeau, March 2006 *)

open Util
open Names
open Term
open Reductionops
open Environ
open Typeops
open Pretype_errors
open Classops
open Recordops
open Evarutil
open Evarconv
open Retyping
open Evd
open Termops

module type S = sig
  (*s Coercions. *)

  (* [inh_app_fun env evd j] coerces [j] to a function; i.e. it
     inserts a coercion into [j], if needed, in such a way it gets as
     type a product; it returns [j] if no coercion is applicable *)
  val inh_app_fun :
    env -> evar_map -> unsafe_judgment -> evar_map * unsafe_judgment

  (* [inh_coerce_to_sort env evd j] coerces [j] to a type; i.e. it
     inserts a coercion into [j], if needed, in such a way it gets as
     type a sort; it fails if no coercion is applicable *)
  val inh_coerce_to_sort : loc ->
    env -> evar_map -> unsafe_judgment -> evar_map * unsafe_type_judgment

  (* [inh_coerce_to_base env evd j] coerces [j] to its base type; i.e. it
     inserts a coercion into [j], if needed, in such a way it gets as
     type its base type (the notion depends on the coercion system) *)
  val inh_coerce_to_base : loc ->
    env -> evar_map -> unsafe_judgment -> evar_map * unsafe_judgment

  (* [inh_coerce_to_prod env evars t] coerces [t] to a product type *)
  val inh_coerce_to_prod : loc ->
    env -> evar_map -> type_constraint_type -> evar_map * type_constraint_type

  (* [inh_conv_coerce_to loc env evd j t] coerces [j] to an object of type
     [t]; i.e. it inserts a coercion into [j], if needed, in such a way [t] and
     [j.uj_type] are convertible; it fails if no coercion is applicable *)
  val inh_conv_coerce_to : loc ->
    env -> evar_map -> unsafe_judgment -> type_constraint_type -> evar_map * unsafe_judgment

  val inh_conv_coerce_rigid_to : loc ->
    env -> evar_map -> unsafe_judgment -> type_constraint_type -> evar_map * unsafe_judgment

  (* [inh_conv_coerces_to loc env evd t t'] checks if an object of type [t]
     is coercible to an object of type [t'] adding evar constraints if needed;
     it fails if no coercion exists *)
  val inh_conv_coerces_to : loc ->
    env -> evar_map -> types -> type_constraint_type -> evar_map

  (* [inh_pattern_coerce_to loc env evd pat ind1 ind2] coerces the Cases
     pattern [pat] typed in [ind1] into a pattern typed in [ind2];
     raises [Not_found] if no coercion found *)
  val inh_pattern_coerce_to :
    loc  -> Rawterm.cases_pattern -> inductive -> inductive -> Rawterm.cases_pattern
end

module Default = struct
  (* Typing operations dealing with coercions *)
  exception NoCoercion

  (* Here, funj is a coercion therefore already typed in global context *)
  let apply_coercion_args env argl funj =
    let rec apply_rec acc typ = function
      | [] -> { uj_val = applist (j_val funj,argl);
		uj_type = typ }
      | h::restl ->
	  (* On devrait pouvoir s'arranger pour qu'on n'ait pas Ã  faire hnf_constr *)
  	  match kind_of_term (whd_betadeltaiota env Evd.empty typ) with
	    | Prod (_,c1,c2) ->
		(* Typage garanti par l'appel à app_coercion*)
		apply_rec (h::acc) (subst1 h c2) restl
	    | _ -> anomaly "apply_coercion_args"
    in
      apply_rec [] funj.uj_type argl

  (* appliquer le chemin de coercions de patterns p *)
  let apply_pattern_coercion loc pat p =
    List.fold_left
      (fun pat (co,n) ->
	 let f i = if i<n then Rawterm.PatVar (loc, Anonymous) else pat in
	   Rawterm.PatCstr (loc, co, list_tabulate f (n+1), Anonymous))
      pat p

  (* raise Not_found if no coercion found *)
  let inh_pattern_coerce_to loc pat ind1 ind2 =
    let p = lookup_pattern_path_between (ind1,ind2) in
      apply_pattern_coercion loc pat p

  let saturate_evd env evd =
    Typeclasses.resolve_typeclasses
      ~onlyargs:true ~split:true ~fail:false env evd

  (* appliquer le chemin de coercions p à hj *)
  let apply_coercion env sigma p hj typ_cl =
    try
      fst (List.fold_left
             (fun (ja,typ_cl) i ->
		let fv,isid = coercion_value i in
		let argl = (class_args_of env sigma typ_cl)@[ja.uj_val] in
		let jres = apply_coercion_args env argl fv in
		  (if isid then
		     { uj_val = ja.uj_val; uj_type = jres.uj_type }
		   else
		     jres),
		jres.uj_type)
             (hj,typ_cl) p)
    with _ -> anomaly "apply_coercion"

  let inh_app_fun env evd j =
    let t = whd_betadeltaiota env evd j.uj_type in
      match kind_of_term t with
	| Prod (_,_,_) -> (evd,j)
	| Evar ev ->
	    let (evd',t) = define_evar_as_product evd ev in
	      (evd',{ uj_val = j.uj_val; uj_type = t })
	| _ ->
      	    let t,p =
	      lookup_path_to_fun_from env evd j.uj_type in
	      (evd,apply_coercion env evd p j t)

  let inh_app_fun env evd j =
    try inh_app_fun env evd j
    with Not_found ->
      try inh_app_fun env (saturate_evd env evd) j
      with Not_found -> (evd, j)

  let inh_tosort_force loc env evd j =
    try
      let t,p = lookup_path_to_sort_from env evd j.uj_type in
      let j1 = apply_coercion env evd p j t in
      let j2 = on_judgment_type (whd_evar evd) j1 in
        (evd,type_judgment env j2)
    with Not_found ->
      error_not_a_type_loc loc env evd j

  let inh_coerce_to_sort loc env evd j =
    let typ = whd_betadeltaiota env evd j.uj_type in
      match kind_of_term typ with
	| Sort s -> (evd,{ utj_val = j.uj_val; utj_type = s })
	| Evar ev when not (is_defined_evar evd ev) ->
	    let (evd',s) = define_evar_as_sort evd ev in
	      (evd',{ utj_val = j.uj_val; utj_type = s })
	| _ ->
	    inh_tosort_force loc env evd j

  let inh_coerce_to_base loc env evd j = (evd, j)
  let inh_coerce_to_prod loc env evd t = (evd, t)

  let inh_coerce_to_fail env evd rigidonly v t c1 =
    if rigidonly & not (Heads.is_rigid env c1 && Heads.is_rigid env t)
    then
      raise NoCoercion
    else
    let v', t' =
      try
	let t2,t1,p = lookup_path_between env evd (t,c1) in
	  match v with
	      Some v ->
		let j =
		  apply_coercion env evd p
		    {uj_val = v; uj_type = t} t2 in
		  Some j.uj_val, j.uj_type
	    | None -> None, t
      with Not_found -> raise NoCoercion
    in
      try (the_conv_x_leq env t' c1 evd, v')
      with Reduction.NotConvertible -> raise NoCoercion

  let rec inh_conv_coerce_to_fail loc env evd rigidonly v t c1 =
    try (the_conv_x_leq env t c1 evd, v)
    with Reduction.NotConvertible ->
    try inh_coerce_to_fail env evd rigidonly v t c1
    with NoCoercion ->
    match
      kind_of_term (whd_betadeltaiota env evd t),
      kind_of_term (whd_betadeltaiota env evd c1)
    with
    | Prod (name,t1,t2), Prod (_,u1,u2) ->
        (* Conversion did not work, we may succeed with a coercion. *)
        (* We eta-expand (hence possibly modifying the original term!) *)
	(* and look for a coercion c:u1->t1 s.t. fun x:u1 => v' (c x)) *)
	(* has type forall (x:u1), u2 (with v' recursively obtained) *)
        (* Note: we retupe the term because sort-polymorphism may have *)
        (* weaken its type *)
	let name = match name with
	  | Anonymous -> Name (id_of_string "x")
	  | _ -> name in
	let env1 = push_rel (name,None,u1) env in
	let (evd', v1) =
	  inh_conv_coerce_to_fail loc env1 evd rigidonly
            (Some (mkRel 1)) (lift 1 u1) (lift 1 t1) in
        let v1 = Option.get v1 in
	let v2 = Option.map (fun v -> beta_applist (lift 1 v,[v1])) v in
	let t2 = match v2 with
	  | None -> subst_term v1 t2
	  | Some v2 -> Retyping.get_type_of env1 evd' v2 in
	let (evd'',v2') = inh_conv_coerce_to_fail loc env1 evd' rigidonly v2 t2 u2 in
	(evd'', Option.map (fun v2' -> mkLambda (name, u1, v2')) v2')
    | _ -> raise NoCoercion

  (* Look for cj' obtained from cj by inserting coercions, s.t. cj'.typ = t *)
  let inh_conv_coerce_to_gen rigidonly loc env evd cj (n, t) =
    match n with
	None ->
	  let (evd', val') =
	    try
	      inh_conv_coerce_to_fail loc env evd rigidonly (Some cj.uj_val) cj.uj_type t
	    with NoCoercion ->
	      let evd = saturate_evd env evd in
		try
		  inh_conv_coerce_to_fail loc env evd rigidonly (Some cj.uj_val) cj.uj_type t
		with NoCoercion ->
		  error_actual_type_loc loc env evd cj t
	  in
	  let val' = match val' with Some v -> v | None -> assert(false) in
	    (evd',{ uj_val = val'; uj_type = t })
      | Some (init, cur) -> (evd, cj)

  let inh_conv_coerce_to = inh_conv_coerce_to_gen false
  let inh_conv_coerce_rigid_to = inh_conv_coerce_to_gen true


    let inh_conv_coerces_to loc env (evd : evar_map) t (abs, t') = evd
      (* Still problematic, as it changes unification
      let nabsinit, nabs =
	match abs with
	    None -> 0, 0
	  | Some (init, cur) -> init, cur
      in
	try
	  let (rels, rng) =
	    (* a little more effort to get products is needed *)
	    try decompose_prod_n nabs t
	    with _ ->
	      if !Flags.debug then
		msg_warning (str "decompose_prod_n failed");
	      raise (Invalid_argument "Coercion.inh_conv_coerces_to")
	  in
	    (* The final range free variables must have been replaced by evars, we accept only that evars
	       in rng are applied to free vars. *)
	    if noccur_with_meta 0 (succ nabsinit) rng then (
	      let env', t, t' =
		let env' = List.fold_right (fun (n, t) env -> push_rel (n, None, t) env) rels env in
		  env', rng, lift nabs t'
	      in
		try
		  pi1 (inh_conv_coerce_to_fail loc env' evd None t t')
		with NoCoercion ->
		  evd) (* Maybe not enough information to unify *)
	      (*let sigma =  evd in
		error_cannot_coerce env' sigma (t, t'))*)
	    else evd
	with Invalid_argument _ -> evd	  *)
end
