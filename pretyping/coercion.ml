(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
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

open Errors
open Util
open Names
open Term
open Vars
open Reductionops
open Environ
open Typeops
open Pretype_errors
open Classops
open Evarutil
open Evarconv
open Evd
open Termops
open Globnames

let use_typeclasses_for_conversion = ref true

let _ =
  Goptions.declare_bool_option
    { Goptions.optsync  = true;
      optdepr  = false;
      optname  = "use typeclass resolution during conversion";
      optkey   = ["Typeclass"; "Resolution"; "For"; "Conversion"];
      optread  = (fun () -> !use_typeclasses_for_conversion);
      optwrite = (fun b -> use_typeclasses_for_conversion := b) }


(* Typing operations dealing with coercions *)
exception NoCoercion
exception NoCoercionNoUnifier of evar_map * unification_error

(* Here, funj is a coercion therefore already typed in global context *)
let apply_coercion_args env evd check isproj argl funj =
  let evdref = ref evd in
  let rec apply_rec acc typ = function
    | [] ->
      if isproj then
	let cst = fst (destConst (j_val funj)) in
	let p = Projection.make cst false in
	let pb = lookup_projection p env in
	let args = List.skipn pb.Declarations.proj_npars argl in
	let hd, tl = match args with hd :: tl -> hd, tl | [] -> assert false in
	  { uj_val = applist (mkProj (p, hd), tl);
	    uj_type = typ }
      else
	{ uj_val = applist (j_val funj,argl);
	  uj_type = typ }
    | h::restl -> (* On devrait pouvoir s'arranger pour qu'on n'ait pas a faire hnf_constr *)
      match kind_of_term (whd_betadeltaiota env evd typ) with
      | Prod (_,c1,c2) ->
        if check && not (e_cumul env evdref (Retyping.get_type_of env evd h) c1) then
	  raise NoCoercion;
        apply_rec (h::acc) (subst1 h c2) restl
      | _ -> anomaly (Pp.str "apply_coercion_args")
  in
  let res = apply_rec [] funj.uj_type argl in
    !evdref, res

(* appliquer le chemin de coercions de patterns p *)
let apply_pattern_coercion loc pat p =
  List.fold_left
    (fun pat (co,n) ->
       let f i = if i<n then Glob_term.PatVar (loc, Anonymous) else pat in
	 Glob_term.PatCstr (loc, co, List.init (n+1) f, Anonymous))
    pat p

(* raise Not_found if no coercion found *)
let inh_pattern_coerce_to loc env pat ind1 ind2 =
  let p = lookup_pattern_path_between env (ind1,ind2) in
    apply_pattern_coercion loc pat p

(* Program coercions *)

open Program

let make_existential loc ?(opaque = Evar_kinds.Define true) env evdref c =
  Evarutil.e_new_evar env evdref ~src:(loc, Evar_kinds.QuestionMark opaque) c

let app_opt env evdref f t =
  whd_betaiota !evdref (app_opt f t)

let pair_of_array a = (a.(0), a.(1))

let disc_subset x =
  match kind_of_term x with
  | App (c, l) ->
      (match kind_of_term c with
       Ind (i,_) ->
	 let len = Array.length l in
	 let sigty = delayed_force sig_typ in
	   if Int.equal len 2 && eq_ind i (Globnames.destIndRef sigty)
	   then
	     let (a, b) = pair_of_array l in
	       Some (a, b)
	   else None
       | _ -> None)
  | _ -> None

exception NoSubtacCoercion
  
let hnf env evd c = whd_betadeltaiota env evd c
let hnf_nodelta env evd c = whd_betaiota evd c

let lift_args n sign =
  let rec liftrec k = function
    | t::sign -> liftn n k t :: (liftrec (k-1) sign)
    | [] -> []
  in
    liftrec (List.length sign) sign

let mu env evdref t =
  let rec aux v =
    let v' = hnf env !evdref v in
      match disc_subset v' with
      Some (u, p) ->
	let f, ct = aux u in
	let p = hnf_nodelta env !evdref p in
	  (Some (fun x ->
		   app_opt env evdref 
		     f (papp evdref sig_proj1 [| u; p; x |])),
	   ct)
      | None -> (None, v)
  in aux t

and coerce loc env evdref (x : Term.constr) (y : Term.constr)
    : (Term.constr -> Term.constr) option
    =
  let rec coerce_unify env x y =
    let x = hnf env !evdref x and y = hnf env !evdref y in
      try
	evdref := the_conv_x_leq env x y !evdref;
	None
      with UnableToUnify _ -> coerce' env x y
  and coerce' env x y : (Term.constr -> Term.constr) option =
    let subco () = subset_coerce env evdref x y in
    let dest_prod c =
      match Reductionops.splay_prod_n env ( !evdref) 1 c with
      | [(na,b,t)], c -> (na,t), c
      | _ -> raise NoSubtacCoercion
    in
    let coerce_application typ typ' c c' l l' =
      let len = Array.length l in
      let rec aux tele typ typ' i co =
	if i < len then
	  let hdx = l.(i) and hdy = l'.(i) in
	    try evdref := the_conv_x_leq env hdx hdy !evdref;
	      let (n, eqT), restT = dest_prod typ in
	      let (n', eqT'), restT' = dest_prod typ' in
		aux (hdx :: tele) (subst1 hdx restT) (subst1 hdy restT') (succ i) co
	    with UnableToUnify _ ->
	      let (n, eqT), restT = dest_prod typ in
	      let (n', eqT'), restT' = dest_prod typ' in
	      let _ =
		try evdref := the_conv_x_leq env eqT eqT' !evdref
		with UnableToUnify _ -> raise NoSubtacCoercion
	      in
		(* Disallow equalities on arities *)
		if Reduction.is_arity env eqT then raise NoSubtacCoercion;
		let restargs = lift_args 1
		  (List.rev (Array.to_list (Array.sub l (succ i) (len - (succ i)))))
		in
		let args = List.rev (restargs @ mkRel 1 :: List.map (lift 1) tele) in
		let pred = mkLambda (n, eqT, applistc (lift 1 c) args) in
		let eq = papp evdref coq_eq_ind [| eqT; hdx; hdy |] in
		let evar = make_existential loc env evdref eq in
		let eq_app x = papp evdref coq_eq_rect
		  [| eqT; hdx; pred; x; hdy; evar|] 
		in
		  aux (hdy :: tele) (subst1 hdx restT) 
		    (subst1 hdy restT') (succ i)  (fun x -> eq_app (co x))
	else Some (fun x -> 
	  let term = co x in
	    Typing.solve_evars env evdref term)
      in
	if isEvar c || isEvar c' then
	  (* Second-order unification needed. *)
	  raise NoSubtacCoercion;
	aux [] typ typ' 0 (fun x -> x)
    in
      match (kind_of_term x, kind_of_term y) with
      | Sort s, Sort s' ->
        (match s, s' with
	| Prop x, Prop y when x == y -> None
	| Prop _, Type _ -> None
	| Type x, Type y when Univ.Universe.equal x y -> None (* false *)
	| _ -> subco ())
      | Prod (name, a, b), Prod (name', a', b') ->
	  let name' = 
	    Name (Namegen.next_ident_away Namegen.default_dependent_ident (Termops.ids_of_context env))
	  in
	  let env' = push_rel (name', None, a') env in
	  let c1 = coerce_unify env' (lift 1 a') (lift 1 a) in
	    (* env, x : a' |- c1 : lift 1 a' > lift 1 a *)
	  let coec1 = app_opt env' evdref c1 (mkRel 1) in
	    (* env, x : a' |- c1[x] : lift 1 a *)
	  let c2 = coerce_unify env' (subst1 coec1 (liftn 1 2 b)) b' in
	    (* env, x : a' |- c2 : b[c1[x]/x]] > b' *)
	    (match c1, c2 with
	     | None, None -> None
	     | _, _ ->
		 Some
		   (fun f ->
		      mkLambda (name', a',
				app_opt env' evdref c2
				  (mkApp (lift 1 f, [| coec1 |])))))

      | App (c, l), App (c', l') ->
	  (match kind_of_term c, kind_of_term c' with
	   Ind (i, u), Ind (i', u') -> (* Inductive types *)
	     let len = Array.length l in
	     let sigT = delayed_force sigT_typ in
	     let prod = delayed_force prod_typ in
	       (* Sigma types *)
	       if Int.equal len (Array.length l') && Int.equal len 2 && eq_ind i i'
		 && (eq_ind i (destIndRef sigT) || eq_ind i (destIndRef prod))
	       then
		 if eq_ind i (destIndRef sigT)
		 then
		   begin
		     let (a, pb), (a', pb') =
		       pair_of_array l, pair_of_array l'
		     in
		     let c1 = coerce_unify env a a' in
		     let remove_head a c =
		       match kind_of_term c with
		       | Lambda (n, t, t') -> c, t'
			   (*| Prod (n, t, t') -> t'*)
		       | Evar (k, args) ->
			   let (evs, t) = Evarutil.define_evar_as_lambda env !evdref (k,args) in
			     evdref := evs;
			     let (n, dom, rng) = destLambda t in
			     let dom = whd_evar !evdref dom in
			       if isEvar dom then
				 let (domk, args) = destEvar dom in
				   evdref := define domk a !evdref;
			       else ();
			       t, rng
		       | _ -> raise NoSubtacCoercion
		     in
		     let (pb, b), (pb', b') = remove_head a pb, remove_head a' pb' in
		     let env' = push_rel (Name Namegen.default_dependent_ident, None, a) env in
		     let c2 = coerce_unify env' b b' in
		       match c1, c2 with
		       | None, None -> None
		       | _, _ ->
			   Some
			     (fun x ->
				let x, y =
				  app_opt env' evdref c1 (papp evdref sigT_proj1
							    [| a; pb; x |]),
				  app_opt env' evdref c2 (papp evdref sigT_proj2
							  [| a; pb; x |])
				in
				  papp evdref sigT_intro [| a'; pb'; x ; y |])
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
				  app_opt env evdref c1 (papp evdref prod_proj1
							   [| a; b; x |]),
				  app_opt env evdref c2 (papp evdref prod_proj2
							   [| a; b; x |])
				in
				  papp evdref prod_intro [| a'; b'; x ; y |])
		   end
	       else
		 if eq_ind i i' && Int.equal len (Array.length l') then
		   let evm = !evdref in
		     (try subco ()
		      with NoSubtacCoercion ->
			let typ = Typing.type_of env evm c in
			let typ' = Typing.type_of env evm c' in
			  (* 			     if not (is_arity env evm typ) then *)
			  coerce_application typ typ' c c' l l')
		       (* 			     else subco () *)
		 else
		   subco ()
	   | x, y when Constr.equal c c' ->
	       if Int.equal (Array.length l) (Array.length l') then
		 let evm =  !evdref in
		 let lam_type = Typing.type_of env evm c in
		 let lam_type' = Typing.type_of env evm c' in
		   (* 			 if not (is_arity env evm lam_type) then ( *)
		   coerce_application lam_type lam_type' c c' l l'
		     (* 			 ) else subco () *)
	       else subco ()
	   | _ -> subco ())
      | _, _ ->  subco ()

  and subset_coerce env evdref x y =
    match disc_subset x with
    Some (u, p) ->
      let c = coerce_unify env u y in
      let f x =
	app_opt env evdref c (papp evdref sig_proj1 [| u; p; x |])
      in Some f
    | None ->
	match disc_subset y with
	Some (u, p) ->
	  let c = coerce_unify env x u in
	    Some
	      (fun x ->
		 let cx = app_opt env evdref c x in
		 let evar = make_existential loc env evdref (mkApp (p, [| cx |]))
		 in
		   (papp evdref sig_intro [| u; p; cx; evar |]))
	| None ->
	    raise NoSubtacCoercion
  in coerce_unify env x y

let coerce_itf loc env evd v t c1 =
  let evdref = ref evd in
  let coercion = coerce loc env evdref t c1 in
  let t = Option.map (app_opt env evdref coercion) v in
    !evdref, t

let saturate_evd env evd =
  Typeclasses.resolve_typeclasses
    ~filter:Typeclasses.no_goals ~split:false ~fail:false env evd

(* appliquer le chemin de coercions p à hj *)
let apply_coercion env sigma p hj typ_cl =
  try
    let j,t,evd = 
      List.fold_left
        (fun (ja,typ_cl,sigma) i ->
	  let ((fv,isid,isproj),ctx) = coercion_value i in
	  let sigma = Evd.merge_context_set Evd.univ_flexible sigma ctx in
	  let argl = (class_args_of env sigma typ_cl)@[ja.uj_val] in
	  let sigma, jres = 
	    apply_coercion_args env sigma true isproj argl fv 
	  in
	    (if isid then
	      { uj_val = ja.uj_val; uj_type = jres.uj_type }
	     else
	      jres),
	    jres.uj_type,sigma)
      (hj,typ_cl,sigma) p
    in evd, j
  with NoCoercion as e -> raise e
  | e when Errors.noncritical e -> anomaly (Pp.str "apply_coercion")

let inh_app_fun env evd j =
  let t = whd_betadeltaiota env evd j.uj_type in
    match kind_of_term t with
    | Prod (_,_,_) -> (evd,j)
    | Evar ev ->
	let (evd',t) = define_evar_as_product evd ev in
	  (evd',{ uj_val = j.uj_val; uj_type = t })
    | _ ->
      	try let t,p =
	  lookup_path_to_fun_from env evd j.uj_type in
	    apply_coercion env evd p j t
	with Not_found | NoCoercion when Flags.is_program_mode () ->
	  try
	    let evdref = ref evd in
	    let coercef, t = mu env evdref t in
	    let res = { uj_val = app_opt env evdref coercef j.uj_val; uj_type = t } in
	      (!evdref, res)
	  with NoSubtacCoercion | NoCoercion ->
	    (evd,j)

let inh_app_fun resolve_tc env evd j =
  try inh_app_fun env evd j
  with
  | Not_found when not resolve_tc 
    || not !use_typeclasses_for_conversion -> (evd, j)
  | Not_found ->
    try inh_app_fun env (saturate_evd env evd) j
    with Not_found -> (evd, j)

let inh_tosort_force loc env evd j =
  try
    let t,p = lookup_path_to_sort_from env evd j.uj_type in
    let evd,j1 = apply_coercion env evd p j t in
    let j2 = on_judgment_type (whd_evar evd) j1 in
      (evd,type_judgment env j2)
  with Not_found | NoCoercion ->
    error_not_a_type_loc loc env evd j

let inh_coerce_to_sort loc env evd j =
  let typ = whd_betadeltaiota env evd j.uj_type in
    match kind_of_term typ with
    | Sort s -> (evd,{ utj_val = j.uj_val; utj_type = s })
    | Evar ev when not (is_defined evd (fst ev)) ->
	let (evd',s) = define_evar_as_sort env evd ev in
	  (evd',{ utj_val = j.uj_val; utj_type = s })
    | _ ->
	inh_tosort_force loc env evd j

let inh_coerce_to_base loc env evd j =
  if Flags.is_program_mode () then
    let evdref = ref evd in
    let ct, typ' = mu env evdref j.uj_type in
    let res =
      { uj_val = app_opt env evdref ct j.uj_val;
	uj_type = typ' }
    in !evdref, res
  else (evd, j)

let inh_coerce_to_prod loc env evd t =
  if Flags.is_program_mode () then
    let evdref = ref evd in
    let _, typ' = mu env evdref t in
      !evdref, typ'
  else (evd, t)

let inh_coerce_to_fail env evd rigidonly v t c1 =
  if rigidonly && not (Heads.is_rigid env c1 && Heads.is_rigid env t)
  then
    raise NoCoercion
  else
    let evd, v', t' =
      try
	let t2,t1,p = lookup_path_between env evd (t,c1) in
	  match v with
	  | Some v ->
	    let evd,j =
	      apply_coercion env evd p
		{uj_val = v; uj_type = t} t2 in
	      evd, Some j.uj_val, j.uj_type
	  | None -> evd, None, t
      with Not_found -> raise NoCoercion
    in
      try (the_conv_x_leq env t' c1 evd, v')
      with UnableToUnify _ -> raise NoCoercion

let rec inh_conv_coerce_to_fail loc env evd rigidonly v t c1 =
  try (the_conv_x_leq env t c1 evd, v)
  with UnableToUnify (best_failed_evd,e) ->
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
          (* Note: we retype the term because sort-polymorphism may have *)
          (* weaken its type *)
	  let name = match name with
	    | Anonymous -> Name Namegen.default_dependent_ident
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
      | _ -> raise (NoCoercionNoUnifier (best_failed_evd,e))

(* Look for cj' obtained from cj by inserting coercions, s.t. cj'.typ = t *)
let inh_conv_coerce_to_gen resolve_tc rigidonly loc env evd cj t =
  let (evd', val') =
    try
      inh_conv_coerce_to_fail loc env evd rigidonly (Some cj.uj_val) cj.uj_type t
    with NoCoercionNoUnifier (best_failed_evd,e) ->
      try
	if Flags.is_program_mode () then
	  coerce_itf loc env evd (Some cj.uj_val) cj.uj_type t
	else raise NoSubtacCoercion
      with
      | NoSubtacCoercion when not resolve_tc || not !use_typeclasses_for_conversion ->
	  error_actual_type_loc loc env best_failed_evd cj t e
      | NoSubtacCoercion ->
	let evd' = saturate_evd env evd in
      	  try
	    if evd' == evd then 
	      error_actual_type_loc loc env best_failed_evd cj t e
	    else 
      	      inh_conv_coerce_to_fail loc env evd' rigidonly (Some cj.uj_val) cj.uj_type t
	  with NoCoercionNoUnifier (best_failed_evd,e) ->
	    error_actual_type_loc loc env best_failed_evd cj t e
  in
  let val' = match val' with Some v -> v | None -> assert(false) in
    (evd',{ uj_val = val'; uj_type = t })

let inh_conv_coerce_to resolve_tc = inh_conv_coerce_to_gen resolve_tc false
let inh_conv_coerce_rigid_to resolve_tc = inh_conv_coerce_to_gen resolve_tc true

let inh_conv_coerces_to loc env evd t t' =
  try
    fst (inh_conv_coerce_to_fail loc env evd true None t t')
  with NoCoercion ->
    evd (* Maybe not enough information to unify *)
      
