(* -*- compile-command: "make -C ../.. bin/coqtop.byte" -*- *)
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
open Subtac_utils
open Coqlib
open Printer
open Subtac_errors
open Eterm
open Pp

let pair_of_array a = (a.(0), a.(1))
let make_name s = Name (id_of_string s)

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
  match kind_of_term x with
  | App (c, l) ->
      (match kind_of_term c with
      Construct c ->
	if c = Term.destConstruct (Lazy.force sig_).intro
	then Some (l.(0), l.(1), l.(2), l.(3))
	else None
      | _ -> None)
  | _ -> None

module Coercion = struct

  exception NoSubtacCoercion

  let disc_proj_exist env x =
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

  let hnf env isevars c = whd_betadeltaiota env ( !isevars) c

  let lift_args n sign =
    let rec liftrec k = function
      | t::sign -> liftn n k t :: (liftrec (k-1) sign)
      | [] -> []
    in
      liftrec (List.length sign) sign

  let rec mu env isevars t =
    let isevars = ref isevars in
    let rec aux v =
      let v = hnf env isevars v in
      match disc_subset v with
	  Some (u, p) ->
	    let f, ct = aux u in
	      (Some (fun x ->
		       app_opt f (mkApp ((Lazy.force sig_).proj1,
					 [| u; p; x |]))),
	       ct)
	| None -> (None, v)
    in aux t

  and coerce loc env isevars (x : Term.constr) (y : Term.constr)
      : (Term.constr -> Term.constr) option
      =
    let x = nf_evar ( !isevars) x and y = nf_evar ( !isevars) y in
    let rec coerce_unify env x y =
      let x = hnf env isevars x and y = hnf env isevars y in
	try
	  isevars := the_conv_x_leq env x y !isevars;
	  None
	with Reduction.NotConvertible -> coerce' env x y
    and coerce' env x y : (Term.constr -> Term.constr) option =
      let subco () = subset_coerce env isevars x y in
      let dest_prod c =
	match Reductionops.splay_prod_n env ( !isevars) 1 c with
	| [(na,b,t)], c -> (na,t), c
	| _ -> raise NoSubtacCoercion
      in
      let rec coerce_application typ typ' c c' l l' =
	let len = Array.length l in
	let rec aux tele typ typ' i co =
	  if i < len then
	    let hdx = l.(i) and hdy = l'.(i) in
	      try isevars := the_conv_x_leq env hdx hdy !isevars;
		let (n, eqT), restT = dest_prod typ in
		let (n', eqT'), restT' = dest_prod typ' in
		aux (hdx :: tele) (subst1 hdx restT) (subst1 hdy restT') (succ i) co
	      with Reduction.NotConvertible ->
		let (n, eqT), restT = dest_prod typ in
		let (n', eqT'), restT' = dest_prod typ' in
		let _ =
		  try isevars := the_conv_x_leq env eqT eqT' !isevars
		  with Reduction.NotConvertible -> raise NoSubtacCoercion
		in
		(* Disallow equalities on arities *)
		if Reduction.is_arity env eqT then raise NoSubtacCoercion;
		let restargs = lift_args 1
		  (List.rev (Array.to_list (Array.sub l (succ i) (len - (succ i)))))
		in
		let args = List.rev (restargs @ mkRel 1 :: lift_args 1 tele) in
		let pred = mkLambda (n, eqT, applistc (lift 1 c) args) in
		let eq = mkApp (Lazy.force eq_ind, [| eqT; hdx; hdy |]) in
		let evar = make_existential loc env isevars eq in
		let eq_app x = mkApp (Lazy.force eq_rect,
				      [| eqT; hdx; pred; x; hdy; evar|]) in
		  aux (hdy :: tele) (subst1 hdx restT) (subst1 hdy restT') (succ i)  (fun x -> eq_app (co x))
	  else Some co
	in
	  if isEvar c || isEvar c' then
	    (* Second-order unification needed. *)
	    raise NoSubtacCoercion;
	  aux [] typ typ' 0 (fun x -> x)
      in
	match (kind_of_term x, kind_of_term y) with
	  | Sort s, Sort s' ->
	      (match s, s' with
		   Prop x, Prop y when x = y -> None
		 | Prop _, Type _ -> None
		 | Type x, Type y when x = y -> None (* false *)
		 | _ -> subco ())
	  | Prod (name, a, b), Prod (name', a', b') ->
	      let name' = Name (Namegen.next_ident_away (id_of_string "x") (Termops.ids_of_context env)) in
	      let env' = push_rel (name', None, a') env in
	      let c1 = coerce_unify env' (lift 1 a') (lift 1 a) in
		(* env, x : a' |- c1 : lift 1 a' > lift 1 a *)
	      let coec1 = app_opt c1 (mkRel 1) in
		(* env, x : a' |- c1[x] : lift 1 a *)
	      let c2 = coerce_unify env' (subst1 coec1 (liftn 1 2 b)) b' in
		(* env, x : a' |- c2 : b[c1[x]/x]] > b' *)
		(match c1, c2 with
		| None, None -> None
		| _, _ ->
		    Some
		      (fun f ->
			mkLambda (name', a',
				 app_opt c2
				   (mkApp (Term.lift 1 f, [| coec1 |])))))

	  | App (c, l), App (c', l') ->
	      (match kind_of_term c, kind_of_term c' with
		   Ind i, Ind i' -> (* Inductive types *)
		     let len = Array.length l in
		     let existS = Lazy.force existS in
		     let prod = Lazy.force prod in
		       (* Sigma types *)
		       if len = Array.length l' && len = 2 && i = i'
			 && (i = Term.destInd existS.typ || i = Term.destInd prod.typ)
		       then
			 if i = Term.destInd existS.typ
			 then
			   begin
			     let (a, pb), (a', pb') =
			       pair_of_array l, pair_of_array l'
			     in
			     let c1 = coerce_unify env a a' in
			     let rec remove_head a c =
			       match kind_of_term c with
				 | Lambda (n, t, t') -> c, t'
				     (*| Prod (n, t, t') -> t'*)
				 | Evar (k, args) ->
				     let (evs, t) = Evarutil.define_evar_as_lambda !isevars (k,args) in
				       isevars := evs;
				       let (n, dom, rng) = destLambda t in
				       let (domk, args) = destEvar dom in
					 isevars := define domk a !isevars;
					 t, rng
				 | _ -> raise NoSubtacCoercion
			     in
			     let (pb, b), (pb', b') = remove_head a pb, remove_head a' pb' in
			     let env' = push_rel (make_name "x", None, a) env in
			     let c2 = coerce_unify env' b b' in
			       match c1, c2 with
				   None, None ->
				     None
				 | _, _ ->
				     Some
				       (fun x ->
					  let x, y =
					    app_opt c1 (mkApp (existS.proj1,
							       [| a; pb; x |])),
					    app_opt c2 (mkApp (existS.proj2,
							       [| a; pb; x |]))
					  in
					    mkApp (existS.intro, [| a'; pb'; x ; y |]))
			   end
			 else
			   begin
			     let (a, b), (a', b') =
			       pair_of_array l, pair_of_array l'
			     in
			     let c1 = coerce_unify env a a' in
			     let c2 = coerce_unify env b b' in
			       match c1, c2 with
				   None, None -> None
				 | _, _ ->
				     Some
				       (fun x ->
					  let x, y =
					    app_opt c1 (mkApp (prod.proj1,
							       [| a; b; x |])),
					    app_opt c2 (mkApp (prod.proj2,
							       [| a; b; x |]))
					  in
					    mkApp (prod.intro, [| a'; b'; x ; y |]))
			   end
		       else
			 if i = i' && len = Array.length l' then
			   let evm =  !isevars in
			     (try subco ()
			       with NoSubtacCoercion ->
				 let typ = Typing.type_of env evm c in
				 let typ' = Typing.type_of env evm c' in
				   (* 			     if not (is_arity env evm typ) then *)
				   coerce_application typ typ' c c' l l')
			       (* 			     else subco () *)
			 else
			   subco ()
		 | x, y when x = y ->
		     if Array.length l = Array.length l' then
		       let evm =  !isevars in
		       let lam_type = Typing.type_of env evm c in
		       let lam_type' = Typing.type_of env evm c' in
(* 			 if not (is_arity env evm lam_type) then ( *)
			 coerce_application lam_type lam_type' c c' l l'
(* 			 ) else subco () *)
		     else subco ()
		 | _ -> subco ())
	  | _, _ ->  subco ()

    and subset_coerce env isevars x y =
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
			 let evar = make_existential loc env isevars (mkApp (p, [| cx |]))
			 in
			   (mkApp
			      ((Lazy.force sig_).intro,
			       [| u; p; cx; evar |])))
	      | None ->
		  raise NoSubtacCoercion
		    (*isevars := Evd.add_conv_pb (Reduction.CONV, x, y) !isevars;
		  None*)
    in coerce_unify env x y

  let coerce_itf loc env isevars v t c1 =
    let evars = ref isevars in
    let coercion = coerce loc env evars t c1 in
      !evars, Option.map (app_opt coercion) v

  (* Taken from pretyping/coercion.ml *)

  (* Typing operations dealing with coercions *)

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
  exception NoCoercion

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

  let inh_app_fun env isevars j =
    let t = whd_betadeltaiota env ( isevars) j.uj_type in
      match kind_of_term t with
	| Prod (_,_,_) -> (isevars,j)
	| Evar ev when not (is_defined_evar isevars ev) ->
	    let (isevars',t) = define_evar_as_product isevars ev in
	      (isevars',{ uj_val = j.uj_val; uj_type = t })
	| _ ->
       	    (try
      	       let t,p =
		 lookup_path_to_fun_from env ( isevars) j.uj_type in
		 (isevars,apply_coercion env ( isevars) p j t)
	     with Not_found ->
	       try
		 let coercef, t = mu env isevars t in
		   (isevars, { uj_val = app_opt coercef j.uj_val; uj_type = t })
	       with NoSubtacCoercion | NoCoercion ->
		 (isevars,j))

  let inh_tosort_force loc env isevars j =
    try
      let t,p = lookup_path_to_sort_from env ( isevars) j.uj_type in
      let j1 = apply_coercion env ( isevars) p j t in
	(isevars,type_judgment env (j_nf_evar ( isevars) j1))
    with Not_found ->
      error_not_a_type_loc loc env ( isevars) j

  let inh_coerce_to_sort loc env isevars j =
    let typ = whd_betadeltaiota env ( isevars) j.uj_type in
      match kind_of_term typ with
	| Sort s -> (isevars,{ utj_val = j.uj_val; utj_type = s })
	| Evar ev when not (is_defined_evar isevars ev) ->
	    let (isevars',s) = define_evar_as_sort isevars ev in
	      (isevars',{ utj_val = j.uj_val; utj_type = s })
	| _ ->
	    inh_tosort_force loc env isevars j

  let inh_coerce_to_base loc env isevars j =
    let typ = whd_betadeltaiota env ( isevars) j.uj_type in
    let ct, typ' = mu env isevars typ in
      isevars, { uj_val = app_opt ct j.uj_val;
		 uj_type = typ' }

  let inh_coerce_to_prod loc env isevars t =
    let typ = whd_betadeltaiota env ( isevars) (snd t) in
    let _, typ' = mu env isevars typ in
      isevars, (fst t, typ')

  let inh_coerce_to_fail env evd rigidonly v t c1 =
    if rigidonly & not (Heads.is_rigid env c1 && Heads.is_rigid env t)
    then
      raise NoCoercion
    else
    let v', t' =
      try
	let t2,t1,p = lookup_path_between env ( evd) (t,c1) in
	  match v with
	      Some v ->
		let j = apply_coercion env ( evd) p
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
      kind_of_term (whd_betadeltaiota env ( evd) t),
      kind_of_term (whd_betadeltaiota env ( evd) c1)
    with
    | Prod (name,t1,t2), Prod (_,u1,u2) ->
        (* Conversion did not work, we may succeed with a coercion. *)
        (* We eta-expand (hence possibly modifying the original term!) *)
	(* and look for a coercion c:u1->t1 s.t. fun x:u1 => v' (c x)) *)
	(* has type forall (x:u1), u2 (with v' recursively obtained) *)
	let name = match name with
	  | Anonymous -> Name (id_of_string "x")
	  | _ -> name in
	let env1 = push_rel (name,None,u1) env in
	let (evd', v1) =
	  inh_conv_coerce_to_fail loc env1 evd rigidonly
            (Some (mkRel 1)) (lift 1 u1) (lift 1 t1) in
        let v1 = Option.get v1 in
	let v2 = Option.map (fun v -> beta_applist (lift 1 v,[v1])) v in
        let t2 = Termops.subst_term v1 t2 in
	let (evd'',v2') = inh_conv_coerce_to_fail loc env1 evd' rigidonly v2 t2 u2 in
	(evd'', Option.map (fun v2' -> mkLambda (name, u1, v2')) v2')
    | _ -> raise NoCoercion

  (* Look for cj' obtained from cj by inserting coercions, s.t. cj'.typ = t *)
  let inh_conv_coerce_to_gen rigidonly loc env evd cj ((n, t) as _tycon) =
    match n with
	None ->
	  let (evd', val') =
	    try
	      inh_conv_coerce_to_fail loc env evd rigidonly
		(Some (nf_isevar evd cj.uj_val))
		(nf_isevar evd cj.uj_type) (nf_isevar evd t)
	    with NoCoercion ->
	      let sigma =  evd in
		try
		  coerce_itf loc env evd (Some cj.uj_val) cj.uj_type t
		with NoSubtacCoercion ->
		  error_actual_type_loc loc env sigma cj t
	  in
	  let val' = match val' with Some v -> v | None -> assert(false) in
	    (evd',{ uj_val = val'; uj_type = t })
      | Some (init, cur) ->
	  (evd, cj)

  let inh_conv_coerce_to = inh_conv_coerce_to_gen false
  let inh_conv_coerce_rigid_to = inh_conv_coerce_to_gen true

  let inh_conv_coerces_to loc env isevars t ((abs, t') as _tycon) =
    let nabsinit, nabs =
      match abs with
	  None -> 0, 0
	| Some (init, cur) -> init, cur
    in
      try
	let rels, rng = Reductionops.splay_prod_n env ( isevars) nabs t in
	(* The final range free variables must have been replaced by evars, we accept only that evars
	   in rng are applied to free vars. *)
	if noccur_with_meta 1 (succ nabs) rng then (
	  let env', t, t' =
	    let env' = push_rel_context rels env in
	      env', rng, lift nabs t'
	  in
	    try
	      fst (try inh_conv_coerce_to_fail loc env' isevars false None t t'
		   with NoCoercion ->
		     coerce_itf loc env' isevars None t t')
	    with NoSubtacCoercion ->
	      let sigma =  isevars in
		error_cannot_coerce env' sigma (t, t'))
	else isevars
      with _ -> isevars
end
