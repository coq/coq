(* $Id$ *)

open Util
(* open Generic *)
open Names
open Term
open Reduction
open Environ
open Typeops
open Pretype_errors
open Classops
open Recordops
open Evarconv
open Retyping

(* Typing operations dealing with coercions *)

let class_of1 env sigma t = class_of env sigma (nf_ise1 sigma t)

let j_nf_ise env sigma {uj_val=v;uj_type=t} =
  { uj_val = nf_ise1 sigma v; 
    uj_type = nf_ise1 sigma t }

let jl_nf_ise env sigma = List.map (j_nf_ise env sigma)

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
              let fv,b = coe_value i in
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
  let t = whd_betadeltaiota env !isevars j.uj_type in
  match kind_of_term t with
    | IsProd (_,_,_) -> j
    | _ ->
       	(try
 	   let t,i1 = class_of1 env !isevars j.uj_type in
      	   let p = lookup_path_to_fun_from i1 in
           apply_coercion env p j t
	 with Not_found -> j)

let inh_tosort_force env isevars j =
  try
    let t,i1 = class_of1 env !isevars j.uj_type in
    let p = lookup_path_to_sort_from i1 in
    apply_coercion env p j t 
  with Not_found -> 
    j

let inh_coerce_to_sort env isevars j =
  let typ = whd_betadeltaiota env !isevars j.uj_type in
  match kind_of_term typ with
    | IsSort s -> { utj_val = j.uj_val; utj_type = s }
    | _ ->
        let j1 = inh_tosort_force env isevars j in 
	type_judgment env !isevars j1 

let inh_coerce_to_fail env isevars c1 hj =
  let hj' =
    try 
      let t1,i1 = class_of1 env !isevars c1 in
      let t2,i2 = class_of1 env !isevars hj.uj_type in
      let p = lookup_path_between (i2,i1) in
      apply_coercion env p hj t2
    with Not_found -> raise NoCoercion 
  in
  if the_conv_x_leq env isevars hj'.uj_type c1 then 
    hj'
  else
    raise NoCoercion

let rec inh_conv_coerce_to_fail env isevars c1 hj =
  let {uj_val = v; uj_type = t} = hj in
  if the_conv_x_leq env isevars t c1 then hj
  else 
    try 
      inh_coerce_to_fail env isevars c1 hj
    with NoCoercion ->  (* try ... with _ -> ... is BAD *)
      (match kind_of_term (whd_betadeltaiota env !isevars t),
	     kind_of_term (whd_betadeltaiota env !isevars c1) with
	 | IsProd (_,t1,t2), IsProd (name,u1,u2) -> 
             let v' = whd_betadeltaiota env !isevars v in
             if (match kind_of_term v' with
                   | IsLambda (_,v1,v2) ->
                       the_conv_x env isevars v1 u1 (* leq v1 u1? *)
                   | _  -> false)
             then 
	       let (x,v1,v2) = destLambda v' in
               let env1 = push_rel_assum (x,v1) env in
               let h2 = inh_conv_coerce_to_fail env isevars u2
			  {uj_val = v2; uj_type = t2 } in
               fst (abs_rel env !isevars x v1 h2)
             else 
               let name = (match name with 
			     | Anonymous -> Name (id_of_string "x")
                             | _ -> name) in
               let env1 = push_rel_assum (name,u1) env in
               let h1 = 
		 inh_conv_coerce_to_fail env isevars t1
		   {uj_val = mkRel 1; 
		    uj_type = u1 } in
               let h2 = inh_conv_coerce_to_fail env isevars u2  
			 { uj_val = mkApp (lift 1 v, [|h1.uj_val|]);
                           uj_type = subst1 h1.uj_val t2 }
	       in
	       fst (abs_rel env !isevars name u1 h2)
	 | _ -> raise NoCoercion)

let inh_conv_coerce_to loc env isevars cj t =
  let cj' = 
    try 
      inh_conv_coerce_to_fail env isevars t cj 
    with NoCoercion -> 
      let rcj = j_nf_ise env !isevars cj in
      let at = nf_ise1 !isevars t in
      error_actual_type_loc loc env rcj.uj_val rcj.uj_type at
  in
  { uj_val = cj'.uj_val;
    uj_type = t }

(* [inh_apply_rel_list loc env isevars args f tycon] tries to type [(f
   args)] of type [tycon] (if any) by inserting coercions in front of
   each arg$_i$, if necessary *)

let inh_apply_rel_list apploc env isevars argjl funj tycon =
  let rec apply_rec env n acc typ = function
    | [] -> 
	let resj =
      	  { uj_val = applist (j_val funj, List.rev acc);
	    uj_type = typ } 
      	in
      	(match tycon with 
	   | Some typ' ->
               (try inh_conv_coerce_to_fail env isevars typ' resj
          	with NoCoercion -> resj) (* try ... with _ -> ... is BAD *)
	   | None -> resj)

    | hj::restjl ->
      	match kind_of_term (whd_betadeltaiota env !isevars typ) with
          | IsProd (na,c1,c2) ->
              let hj' =
		(try 
		   inh_conv_coerce_to_fail env isevars c1 hj 
		 with NoCoercion ->
                   error_cant_apply_bad_type_loc apploc env 
		     (n,nf_ise1 !isevars c1,
		      nf_ise1 !isevars hj.uj_type)
		     (j_nf_ise env !isevars funj)
		     (jl_nf_ise env !isevars argjl))
	      in
	      apply_rec (push_rel_assum (na,c1) env)
		(n+1) ((j_val hj')::acc) (subst1 hj'.uj_val c2) restjl
          | _ ->
              error_cant_apply_not_functional_loc apploc env
	      	(j_nf_ise env !isevars funj) (jl_nf_ise env !isevars argjl)
  in 
  apply_rec env 1 [] funj.uj_type argjl

