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

open Global
open Scoq
open Coqlib
open Printer
open Subtac_errors
open Context
open Eterm
open Pp

let pair_of_array a = (a.(0), a.(1))
let make_name s = Name (id_of_string s)

exception NoCoercion

let rec disc_subset x = 
  match kind_of_term x with
    | App (c, l) ->
	(match kind_of_term c with
	     Ind i ->
	       let len = Array.length l in
	       let sig_ = Lazy.force sig_ in
		 if len = 2 && i = Term.destInd sig_.typ
		 then
		   let (a, b) = pair_of_array l in
		     Some (a, b)
		 else None
	   | _ -> None)
    | _ -> None
	
and disc_exist env x =
  trace (str "Disc_exist: " ++ my_print_constr env x);
  match kind_of_term x with
    | App (c, l) ->
	(match kind_of_term c with
	     Construct c ->	       
	       if c = Term.destConstruct (Lazy.force sig_).intro
	       then Some (l.(0), l.(1), l.(2), l.(3))
	       else None
	   | _ -> None)
    | _ -> None


let disc_proj_exist env x =
  trace (str "disc_proj_exist: " ++ my_print_constr env x);
  match kind_of_term x with
    | App (c, l) ->
	(if Term.eq_constr c (Lazy.force sig_).proj1 
	   && Array.length l = 3 
	 then disc_exist env l.(2)
	 else None)
    | _ -> None


let sort_rel s1 s2 = 
  match s1, s2 with
      Prop Pos, Prop Pos -> Prop Pos
    | Prop Pos, Prop Null -> Prop Null
    | Prop Null, Prop Null -> Prop Null
    | Prop Null, Prop Pos -> Prop Pos
    | Type _, Prop Pos -> Prop Pos
    | Type _, Prop Null -> Prop Null
    | _, Type _ -> s2

let rec mu env isevars t =   
  let rec aux v = 
    match disc_subset v with
      Some (u, p) -> 
	let f, ct = aux u in
	  (Some (fun x ->		   
		   app_opt f (mkApp ((Lazy.force sig_).proj1, 
				     [| u; p; x |]))),
	   ct)
    | None -> (None, t)
  in aux t

and coerce loc env nonimplicit isevars (x : Term.constr) (y : Term.constr) 
    : (Term.constr -> Term.constr) option 
    =
  trace (str "Coerce called for " ++ (my_print_constr env x) ++ 
	 str " and "++ my_print_constr env y);

  let rec coerce_unify env x y =
    if e_cumul env isevars x y then (
      trace (str "Unified " ++ (my_print_constr env x) ++ 
	     str " and "++ my_print_constr env y);
      None
    ) else coerce' env x y (* head recutions needed *)
  and coerce' env x y : (Term.constr -> Term.constr) option =
    let subco () = subset_coerce env x y in
      trace (str "coerce' from " ++ (my_print_constr env x) ++ 
	     str " to "++ my_print_constr env y);
      match (kind_of_term x, kind_of_term y) with
	| Sort s, Sort s' -> 
	    (match s, s' with
		 Prop x, Prop y when x = y -> None
	       | Prop _, Type _ -> None
	       | Type x, Type y when x = y -> None (* false *)
	       | _ -> subco ())
	| Prod (name, a, b), Prod (name', a', b') ->
	    let c1 = coerce_unify env a' a in
	    let env' = push_rel (name', None, a') env in
	    let c2 = coerce_unify env' b b' in
	      (match c1, c2 with
		   None, None -> failwith "subtac.coerce': Should have detected equivalence earlier"
		 | _, _ ->
		     Some
		       (fun f -> 
			  mkLambda (name', a',
				    app_opt c2
				      (mkApp (Term.lift 1 f, 
					      [| app_opt c1 (mkRel 1) |])))))
		
	| App (c, l), App (c', l') ->
	    (match kind_of_term c, kind_of_term c' with
		 Ind i, Ind i' ->
		   let len = Array.length l in
		   let existS = Lazy.force existS in
		     if len = Array.length l' && len = 2
		       && i = i' && i = Term.destInd existS.typ 
		     then
		       begin (* Sigma types *)
			 debug 1 (str "In coerce sigma types");
			 let (a, pb), (a', pb') = 
			   pair_of_array l, pair_of_array l' 
			 in
			 let c1 = coerce_unify env a a' in
			 let remove_head c = 
			   let (_, _, x) = Term.destProd c in
			     x
			 in
			 let b, b' = remove_head pb, remove_head pb' in
			 let env' = push_rel (make_name "x", None, a) env in
			 let c2 = coerce_unify env' b b' in
			   match c1, c2 with
			       None, None -> None
			     | _, _ ->
				 Some 
				   (fun x ->
				      let x, y = 
					app_opt c1 (mkApp (existS.proj1,
							   [| a; pb; x |])),
					app_opt c2 (mkApp (existS.proj2, 
							   [| a; pb'; x |]))
				      in
					mkApp (existS.intro, [| x ; y |]))
		       end
		     else subco ()
	       | _ ->  subco ())
	| _, _ ->  subco ()

  and subset_coerce env x y =
    match disc_subset x with
	Some (u, p) -> 
	  let c = coerce_unify env u y in
	  let f x = 
	    app_opt c (mkApp ((Lazy.force sig_).proj1, 
			      [| u; p; x |]))
	  in Some f
      | None ->
	  match disc_subset y with
	    Some (u, p) ->
	      let c = coerce_unify env x u in
		Some 
		  (fun x ->
		     let cx = app_opt c x in
		     let evar = make_existential dummy_loc env nonimplicit isevars (mkApp (p, [| cx |]))
		     in
		       (mkApp 
			  ((Lazy.force sig_).intro, 
			   [| u; p; cx; evar |])))
	    | None -> raise NoCoercion
  in coerce_unify env x y

let coerce_itf loc env nonimplicit isevars hj c1 =
  let {uj_val = v; uj_type = t} = hj in
  let evars = ref isevars in
  let coercion = coerce loc env nonimplicit evars t c1 in
    !evars, {uj_val = app_opt coercion v;
	     uj_type = t}
      
(* Taken from pretyping/coercion.ml *)

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

let inh_coerce_to_fail env isevars c1 hj =
  let hj' =
    try 
      let t1,i1 = class_of1 env (evars_of isevars) c1 in
      let t2,i2 = class_of1 env (evars_of isevars) hj.uj_type in
      let p = lookup_path_between (i2,i1) in
      apply_coercion env p hj t2
    with Not_found -> raise NoCoercion 
  in
  try (the_conv_x_leq env hj'.uj_type c1 isevars, hj')
  with Reduction.NotConvertible -> raise NoCoercion

let rec inh_conv_coerce_to_fail env isevars hj c1 =
  let {uj_val = v; uj_type = t} = hj in
  try (the_conv_x_leq env t c1 isevars, hj)
  with Reduction.NotConvertible ->
    (try 
      inh_coerce_to_fail env isevars c1 hj
    with NoCoercion ->
      (match kind_of_term (whd_betadeltaiota env (evars_of isevars) t),
	     kind_of_term (whd_betadeltaiota env (evars_of isevars) c1) with
	 | Prod (_,t1,t2), Prod (name,u1,u2) -> 
             let v' = whd_betadeltaiota env (evars_of isevars) v in
             let (evd',b) =
               match kind_of_term v' with
                 | Lambda (_,v1,v2) ->
                     (try the_conv_x env v1 u1 isevars, true  (* leq v1 u1? *)
                     with Reduction.NotConvertible -> (isevars, false))
                 | _  -> (isevars,false) in
             if b
             then 
	       let (x,v1,v2) = destLambda v' in
               let env1 = push_rel (x,None,v1) env in
               let (evd'',h2) = inh_conv_coerce_to_fail env1 evd'
			  {uj_val = v2; uj_type = t2 } u2 in
               (evd'',{ uj_val = mkLambda (x, v1, h2.uj_val);
                 uj_type = mkProd (x, v1, h2.uj_type) })
             else 
               (* Mismatch on t1 and u1 or not a lambda: we eta-expand *)
               (* we look for a coercion c:u1->t1 s.t. [name:u1](v' (c x)) *)
               (* has type (name:u1)u2 (with v' recursively obtained) *)
               let name = (match name with 
			     | Anonymous -> Name (id_of_string "x")
                             | _ -> name) in
               let env1 = push_rel (name,None,u1) env in
               let (evd',h1) =
		 inh_conv_coerce_to_fail env1 isevars
		   {uj_val = mkRel 1; uj_type = (lift 1 u1) }
                   (lift 1 t1) in
               let (evd'',h2) = inh_conv_coerce_to_fail env1 evd'
			 { uj_val = mkApp (lift 1 v, [|h1.uj_val|]);
                           uj_type = subst1 h1.uj_val t2 }
                          u2
	       in
               (evd'',
                { uj_val = mkLambda (name, u1, h2.uj_val);
                  uj_type = mkProd (name, u1, h2.uj_type) })
	 | _ -> raise NoCoercion))

(* Look for cj' obtained from cj by inserting coercions, s.t. cj'.typ = t *)
let inh_conv_coerce_to loc env nonimplicit isevars cj t =
  let (evd',cj') = 
    try 
      inh_conv_coerce_to_fail env isevars cj t
    with NoCoercion ->
      try
	coerce_itf loc env nonimplicit isevars cj t
      with NoCoercion ->
	let sigma = evars_of isevars in
	  error_actual_type_loc loc env sigma cj t
  in
  (evd',{ uj_val = cj'.uj_val; uj_type = t })
