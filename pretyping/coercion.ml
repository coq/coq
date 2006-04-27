(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(* $Id$ *)

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

module type S = sig
  (*s Coercions. *)
  
  (* [inh_app_fun env isevars j] coerces [j] to a function; i.e. it
     inserts a coercion into [j], if needed, in such a way it gets as
     type a product; it returns [j] if no coercion is applicable *)
  val inh_app_fun :
    env -> evar_defs -> unsafe_judgment -> evar_defs * unsafe_judgment
    
  (* [inh_coerce_to_sort env isevars j] coerces [j] to a type; i.e. it
     inserts a coercion into [j], if needed, in such a way it gets as
     type a sort; it fails if no coercion is applicable *)
  val inh_coerce_to_sort : loc ->
    env -> evar_defs -> unsafe_judgment -> evar_defs * unsafe_type_judgment
    
  (* [inh_conv_coerce_to loc env isevars j t] coerces [j] to an object of type 
     [t]; i.e. it inserts a coercion into [j], if needed, in such a way [t] and
     [j.uj_type] are convertible; it fails if no coercion is applicable *)
  val inh_conv_coerce_to : loc -> 
    env -> evar_defs -> unsafe_judgment -> type_constraint_type -> evar_defs * unsafe_judgment
    

  (* [inh_conv_coerces_to loc env isevars t t'] checks if an object of type [t]
     is coercible to an object of type [t'] adding evar constraints if needed;
     it fails if no coercion exists *)
  val inh_conv_coerces_to : loc -> 
    env -> evar_defs -> types -> type_constraint_type -> evar_defs

  (* [inh_pattern_coerce_to loc env isevars pat ind1 ind2] coerces the Cases
     pattern [pat] typed in [ind1] into a pattern typed in [ind2];
     raises [Not_found] if no coercion found *)
  val inh_pattern_coerce_to :
    loc  -> Rawterm.cases_pattern -> inductive -> inductive -> Rawterm.cases_pattern
end

module Default = struct
  (* Typing operations dealing with coercions *)
  exception NoCoercion

  let class_of1 env sigma t = class_of env sigma (nf_evar sigma t)

  (* Here, funj is a coercion therefore already typed in global context *)
  let apply_coercion_args env argl funj =
    let rec apply_rec acc typ = function
      | [] -> { uj_val = applist (j_val funj,argl);
		uj_type = typ }
      | h::restl ->
	  (* On devrait pouvoir s'arranger pour qu'on n'ait pas à faire hnf_constr *)
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
    let i1 = inductive_class_of ind1 in
    let i2 = inductive_class_of ind2 in
    let p = lookup_pattern_path_between (i1,i2) in
      apply_pattern_coercion loc pat p

  (* appliquer le chemin de coercions p à hj *)

  let apply_coercion env p hj typ_cl =
    try 
      fst (List.fold_left
             (fun (ja,typ_cl) i -> 
		let fv,isid = coercion_value i in
		let argl = (class_args_of typ_cl)@[ja.uj_val] in
		let jres = apply_coercion_args env argl fv in
		  (if isid then 
		     { uj_val = ja.uj_val; uj_type = jres.uj_type }
		   else 
		     jres),
		jres.uj_type)
             (hj,typ_cl) p)
    with _ -> anomaly "apply_coercion"

  let inh_app_fun env isevars j = 
    let t = whd_betadeltaiota env (evars_of isevars) j.uj_type in
      match kind_of_term t with
	| Prod (_,_,_) -> (isevars,j)
	| Evar ev when not (is_defined_evar isevars ev) ->
	    let (isevars',t) = define_evar_as_arrow isevars ev in
	      (isevars',{ uj_val = j.uj_val; uj_type = t })
	| _ ->
       	    (try
 	       let t,i1 = class_of1 env (evars_of isevars) j.uj_type in
      	       let p = lookup_path_to_fun_from i1 in
		 (isevars,apply_coercion env p j t)
	     with Not_found -> (isevars,j))

  let inh_tosort_force loc env isevars j =
    try
      let t,i1 = class_of1 env (evars_of isevars) j.uj_type in
      let p = lookup_path_to_sort_from i1 in
      let j1 = apply_coercion env p j t in 
	(isevars,type_judgment env (j_nf_evar (evars_of isevars) j1))
    with Not_found ->
      error_not_a_type_loc loc env (evars_of isevars) j

  let inh_coerce_to_sort loc env isevars j =
    let typ = whd_betadeltaiota env (evars_of isevars) j.uj_type in
      match kind_of_term typ with
	| Sort s -> (isevars,{ utj_val = j.uj_val; utj_type = s })
	| Evar ev when not (is_defined_evar isevars ev) ->
	    let (isevars',s) = define_evar_as_sort isevars ev in
	      (isevars',{ utj_val = j.uj_val; utj_type = s })
	| _ ->
	    inh_tosort_force loc env isevars j

  let inh_coerce_to_fail env isevars c1 v t =
    let v', t' =
      try 
	let t1,i1 = class_of1 env (evars_of isevars) c1 in
	let t2,i2 = class_of1 env (evars_of isevars) t in
	let p = lookup_path_between (i2,i1) in
	  match v with
	      Some v -> 
		let j = apply_coercion env p {uj_val = v; uj_type = t} t2 in
		  Some j.uj_val, j.uj_type
	    | None -> None, t
      with Not_found -> raise NoCoercion 
    in
      try (the_conv_x_leq env t' c1 isevars, v', t')
      with Reduction.NotConvertible -> raise NoCoercion
  open Pp
  let rec inh_conv_coerce_to_fail loc env isevars v t c1 =
    try (the_conv_x_leq env t c1 isevars, v, t)
    with Reduction.NotConvertible ->
      (try 
	 inh_coerce_to_fail env isevars c1 v t
	 with NoCoercion ->
	   (match kind_of_term (whd_betadeltaiota env (evars_of isevars) t),
	      kind_of_term (whd_betadeltaiota env (evars_of isevars) c1) with
		| Prod (_,t1,t2), Prod (name,u1,u2) -> 
		    let v' = option_map (whd_betadeltaiota env (evars_of isevars)) v in
		    let (evd',b) =
		      match v' with 
			  Some v' ->
			    (match kind_of_term v' with
			       | Lambda (x,v1,v2) ->
				   (try the_conv_x env v1 u1 isevars, Some (x, v1, v2)  (* leq v1 u1? *)
				    with Reduction.NotConvertible -> (isevars, None))
			       | _  -> (isevars, None))
			| None -> (isevars, None)
		    in 
		      (match b with
			   Some (x, v1, v2) ->
			     let env1 = push_rel (x,None,v1) env in
			     let (evd'', v2', t2') = inh_conv_coerce_to_fail loc env1 evd'
						       (Some v2) t2 u2 in
			       (evd'', option_map (fun v2' -> mkLambda (x, v1, v2')) v2', 
				mkProd (x, v1, t2'))
			 | None ->
			     (* Mismatch on t1 and u1 or not a lambda: we eta-expand *)
			     (* we look for a coercion c:u1->t1 s.t. [name:u1](v' (c x)) *)
			     (* has type (name:u1)u2 (with v' recursively obtained) *)
			     let name = (match name with 
					   | Anonymous -> Name (id_of_string "x")
					   | _ -> name) in
			     let env1 = push_rel (name,None,u1) env in
			     let (evd', v1', t1') =
			       inh_conv_coerce_to_fail loc env1 isevars
				 (Some (mkRel 1)) (lift 1 u1) (lift 1 t1) 
			     in
			     let (evd'', v2', t2') = 
			       let v2 =
				 match v with 
				     Some v -> option_map (fun v1' -> mkApp (lift 1 v, [|v1'|])) v1'
				   | None -> None
			       and evd', t2 =
				 match v1' with 
				     Some v1' -> evd', subst1 v1' t2
				   | None -> 
				       let evd', ev = new_evar evd' env ~src:(loc, InternalHole) t1' in
					 evd', subst1 ev t2
			       in
				 inh_conv_coerce_to_fail loc env1 evd' v2 t2 u2
			     in
			       (evd'', option_map (fun v2' -> mkLambda (name, u1, v2')) v2',
				mkProd (name, u1, t2')))
		| _ -> raise NoCoercion))
	
  (* Look for cj' obtained from cj by inserting coercions, s.t. cj'.typ = t *)
  let inh_conv_coerce_to loc env isevars cj (n, t) =
    match n with
	None ->
	  let (evd', val', type') = 
	    try 
	      inh_conv_coerce_to_fail loc env isevars (Some cj.uj_val) cj.uj_type t
	    with NoCoercion ->
	      let sigma = evars_of isevars in
		error_actual_type_loc loc env sigma cj t
	  in
	  let val' = match val' with Some v -> v | None -> assert(false) in
	  let nf = nf_isevar evd' in
	    (evd',{ uj_val = nf val'; uj_type = nf t })
      | Some (init, cur) -> (isevars, cj)
      
    let inh_conv_coerces_to loc env (isevars : evar_defs) t (abs, t') = isevars
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
	      if !Options.debug then
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
		  pi1 (inh_conv_coerce_to_fail loc env' isevars None t t')
		with NoCoercion ->
		  isevars) (* Maybe not enough information to unify *)
	      (*let sigma = evars_of isevars in
		error_cannot_coerce env' sigma (t, t'))*)
	    else isevars
	with Invalid_argument _ -> isevars	  *)
end
