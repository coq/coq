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
open Termops

(* Typing operations dealing with coercions *)

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

exception NoCoercion

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
    | Prod (_,_,_) -> j
    | Evar ev when not (is_defined_evar isevars ev) ->
	let t = define_evar_as_arrow isevars ev in
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
    | Sort s -> { utj_val = j.uj_val; utj_type = s }
    | Evar ev when not (is_defined_evar isevars ev) ->
	let s = define_evar_as_sort isevars ev in
	{ utj_val = j.uj_val; utj_type = s }
    | _ ->
        let j1 = inh_tosort_force env isevars j in 
	type_judgment env (j_nf_evar (evars_of isevars) j1) 

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
	 | Prod (_,t1,t2), Prod (name,u1,u2) -> 
             let v' = whd_betadeltaiota env (evars_of isevars) v in
             if (match kind_of_term v' with
                   | Lambda (_,v1,v2) ->
                       the_conv_x env isevars v1 u1 (* leq v1 u1? *)
                   | _  -> false)
             then 
	       let (x,v1,v2) = destLambda v' in
               let env1 = push_rel (x,None,v1) env in
               let h2 = inh_conv_coerce_to_fail env1 isevars 
			  {uj_val = v2; uj_type = t2 } u2 in
               { uj_val = mkLambda (x, v1, h2.uj_val);
                 uj_type = mkProd (x, v1, h2.uj_type) }
             else 
               (* Mismatch on t1 and u1 or not a lambda: we eta-expand *)
               (* we look for a coercion c:u1->t1 s.t. [name:u1](v' (c x)) *)
               (* has type (name:u1)u2 (with v' recursively obtained) *)
               let name = (match name with 
			     | Anonymous -> Name (id_of_string "x")
                             | _ -> name) in
               let env1 = push_rel (name,None,u1) env in
               let h1 =
		 inh_conv_coerce_to_fail env1 isevars
		   {uj_val = mkRel 1; uj_type = (lift 1 u1) }
                   (lift 1 t1) in
               let h2 = inh_conv_coerce_to_fail env1 isevars
			 { uj_val = mkApp (lift 1 v, [|h1.uj_val|]);
                           uj_type = subst_term h1.uj_val t2 }
                          u2
	       in
               { uj_val = mkLambda (name, u1, h2.uj_val);
                 uj_type = mkProd (name, u1, h2.uj_type) }
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
          | Prod (na,c1,c2) ->
              let hj' =
		try 
		  inh_conv_coerce_to_fail env isevars hj c1
		with NoCoercion ->
                  error_cant_apply_bad_type_loc apploc env sigma
		    (1,c1,hj.uj_type) resj (List.map snd restjl) in
	      let newresj =
      		{ uj_val = applist (j_val resj, [j_val hj']);
		  uj_type = subst1 hj'.uj_val c2 } in
	      apply_rec (push_rel (na,None,c1) env) (n+1) newresj restjl
          | _ ->
              error_cant_apply_not_functional_loc 
		(join_loc funloc loc) env sigma resj
                (List.map snd restjl)
  in 
  apply_rec env 1 funj argjl

