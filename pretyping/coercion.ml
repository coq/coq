(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)
(* $Id$ *)

open Util
open Names
open Term
open Reduction
open Environ
open Typeops
open Pretype_errors
open Classops
open Recordops
open Evarutil
open Evarconv
open Retyping

(* Typing operations dealing with coercions *)

let class_of1 env sigma t = class_of env sigma (nf_evar sigma t)

(* Here, funj is a coercion therefore already typed in global context *)
let apply_coercion_args env argl funj =
  let rec apply_rec acc typ = function
    | [] -> { uj_val = applist (j_val funj,argl);
              uj_type = typ }
    | h::restl ->
      (* On devrait pouvoir s'arranger pour qu'on ait pas à faire hnf_constr *)
  	match kind_of_term (whd_betadeltaiota env Evd.empty typ) with
	  | IsProd (_,c1,c2) -> 
              (* Typage garanti par l'appel a app_coercion*)
	      apply_rec (h::acc) (subst1 h c2) restl
	  | _ -> anomaly "apply_coercion_args"
  in 
  apply_rec [] funj.uj_type argl

(* appliquer le chemin de coercions p a` hj *)

exception NoCoercion

let apply_coercion env p hj typ_cl =
  if !compter then begin
    nbpathc := !nbpathc +1; 
    nbcoer := !nbcoer + (List.length p)
  end;
  try 
    fst (List.fold_left
           (fun (ja,typ_cl) i -> 
              let fv,b = coercion_value i in
              let argl = (class_args_of typ_cl)@[ja.uj_val] in
              let jres = apply_coercion_args env argl fv in
              (if b then 
		 { uj_val = ja.uj_val; uj_type = jres.uj_type }
               else 
		 jres),
	      jres.uj_type)
           (hj,typ_cl) p)
  with _ -> anomaly "apply_coercion"

let inh_app_fun env isevars j = 
  let t = whd_betadeltaiota env (evars_of isevars) j.uj_type in
  match kind_of_term t with
    | IsProd (_,_,_) -> j
    | IsEvar ev when not (is_defined_evar isevars ev) ->
	let (sigma',t) = define_evar_as_arrow (evars_of isevars) ev in
	evars_reset_evd sigma' isevars;
	{ uj_val = j.uj_val; uj_type = t }
    | _ ->
       	(try
 	   let t,i1 = class_of1 env (evars_of isevars) j.uj_type in
      	   let p = lookup_path_to_fun_from i1 in
           apply_coercion env p j t
	 with Not_found -> j)

let inh_tosort_force env isevars j =
  try
    let t,i1 = class_of1 env (evars_of isevars) j.uj_type in
    let p = lookup_path_to_sort_from i1 in
    apply_coercion env p j t 
  with Not_found -> 
    j

let inh_coerce_to_sort env isevars j =
  let typ = whd_betadeltaiota env (evars_of isevars) j.uj_type in
  match kind_of_term typ with
    | IsSort s -> { utj_val = j.uj_val; utj_type = s }
    | IsEvar ev when not (is_defined_evar isevars ev) ->
	let (sigma', s) = define_evar_as_sort (evars_of isevars) ev in
	evars_reset_evd sigma' isevars;
	{ utj_val = j.uj_val; utj_type = s }
    | _ ->
        let j1 = inh_tosort_force env isevars j in 
	type_judgment env (evars_of isevars) j1 

let inh_coerce_to_fail env isevars c1 hj =
  let hj' =
    try 
      let t1,i1 = class_of1 env (evars_of isevars) c1 in
      let t2,i2 = class_of1 env (evars_of isevars) hj.uj_type in
      let p = lookup_path_between (i2,i1) in
      apply_coercion env p hj t2
    with Not_found -> raise NoCoercion 
  in
  if the_conv_x_leq env isevars hj'.uj_type c1 then 
    hj'
  else
    raise NoCoercion

let rec inh_conv_coerce_to_fail env isevars hj c1 =
  let {uj_val = v; uj_type = t} = hj in
  if the_conv_x_leq env isevars t c1 then hj
  else 
    try 
      inh_coerce_to_fail env isevars c1 hj
    with NoCoercion ->  (* try ... with _ -> ... is BAD *)
      (match kind_of_term (whd_betadeltaiota env (evars_of isevars) t),
	     kind_of_term (whd_betadeltaiota env (evars_of isevars) c1) with
	 | IsProd (_,t1,t2), IsProd (name,u1,u2) -> 
             let v' = whd_betadeltaiota env (evars_of isevars) v in
             if (match kind_of_term v' with
                   | IsLambda (_,v1,v2) ->
                       the_conv_x env isevars v1 u1 (* leq v1 u1? *)
                   | _  -> false)
             then 
	       let (x,v1,v2) = destLambda v' in
               let env1 = push_rel_assum (x,v1) env in
               let h2 = inh_conv_coerce_to_fail env1 isevars 
			  {uj_val = v2; uj_type = t2 } u2 in
               fst (abs_rel env (evars_of isevars) x v1 h2)
             else 
               (* Mismatch on t1 and u1 or not a lambda: we eta-expand *)
               (* we look for a coercion c:u1->t1 s.t. [name:u1](v' (c x)) *)
               (* has type (name:u1)u2 (with v' recursively obtained) *)
               let name = (match name with 
			     | Anonymous -> Name (id_of_string "x")
                             | _ -> name) in
               let env1 = push_rel_assum (name,u1) env in
               let h1 =
		 inh_conv_coerce_to_fail env1 isevars
		   {uj_val = mkRel 1; uj_type = (lift 1 u1) }
                   (lift 1 t1) in
               let h2 = inh_conv_coerce_to_fail env1 isevars
			 { uj_val = mkApp (lift 1 v, [|h1.uj_val|]);
                           uj_type = subst1 h1.uj_val t2 }
                          u2
	       in
	       fst (abs_rel env (evars_of isevars) name u1 h2)
	 | _ -> raise NoCoercion)

(* Look for cj' obtained from cj by inserting coercions, s.t. cj'.typ = t *)
let inh_conv_coerce_to loc env isevars cj t =
  let cj' = 
    try 
      inh_conv_coerce_to_fail env isevars cj t
    with NoCoercion ->
      let sigma = evars_of isevars in
      error_actual_type_loc loc env sigma cj t
  in
  { uj_val = cj'.uj_val; uj_type = t }

(* [inh_apply_rel_list loc env isevars args f tycon] tries to type [(f
   args)] of type [tycon] (if any) by inserting coercions in front of
   each arg$_i$, if necessary *)

let inh_apply_rel_list apploc env isevars argjl (funloc,funj) tycon =
  let rec apply_rec env n resj = function
    | [] -> resj
    | (loc,hj)::restjl ->
        let sigma = evars_of isevars in
	let resj = inh_app_fun env isevars resj in
        let ntyp = whd_betadeltaiota env sigma resj.uj_type in
      	match kind_of_term ntyp with
          | IsProd (na,c1,c2) ->
              let hj' =
		try 
		  inh_conv_coerce_to_fail env isevars hj c1
		with NoCoercion ->
                  error_cant_apply_bad_type_loc apploc env sigma
		    (1,c1,hj.uj_type) resj (List.map snd restjl) in
	      let newresj =
      		{ uj_val = applist (j_val resj, [j_val hj']);
		  uj_type = subst1 hj'.uj_val c2 } in
	      apply_rec (push_rel_assum (na,c1) env) (n+1) newresj restjl
          | _ ->
              error_cant_apply_not_functional_loc 
		(Rawterm.join_loc funloc loc) env sigma resj
                (List.map snd restjl)
  in 
  apply_rec env 1 funj argjl

