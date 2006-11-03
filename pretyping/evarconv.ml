(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Pp
open Util
open Names
open Term
open Closure
open Reduction
open Reductionops
open Termops
open Environ
open Typing
open Classops
open Recordops 
open Evarutil
open Libnames
open Evd

type flex_kind_of_term =
  | Rigid of constr 
  | MaybeFlexible of constr
  | Flexible of existential

let flex_kind_of_term c l =
  match kind_of_term c with
    | Const _ -> MaybeFlexible c
    | Rel n -> MaybeFlexible c
    | Var id -> MaybeFlexible c
    | Lambda _ when l<>[] -> MaybeFlexible c
    | LetIn _  -> MaybeFlexible c
    | Evar ev -> Flexible ev
    | _ -> Rigid c

let eval_flexible_term env c =
  match kind_of_term c with
  | Const c -> constant_opt_value env c
  | Rel n ->
      (try let (_,v,_) = lookup_rel n env in option_map (lift n) v
      with Not_found -> None)
  | Var id ->
      (try let (_,v,_) = lookup_named id env in v with Not_found -> None)
  | LetIn (_,b,_,c) -> Some (subst1 b c)
  | Lambda _ -> Some c
  | _ -> assert false
(*
let rec apprec_nobeta env sigma s =
  let (t,stack as s) = whd_state s in
  match kind_of_term (fst s) with
    | Case (ci,p,d,lf) ->
        let (cr,crargs) = whd_betadeltaiota_stack env sigma d in
        let rslt = mkCase (ci, p, applist (cr,crargs), lf) in
        if reducible_mind_case cr then 
	  apprec_nobeta env sigma (rslt, stack)
        else 
	  s
    | Fix fix ->
	  (match reduce_fix (whd_betadeltaiota_state env sigma) fix stack with
             | Reduced s -> apprec_nobeta env sigma s
	     | NotReducible -> s)
    | _ -> s

let evar_apprec_nobeta env isevars stack c =
  let rec aux s =
    let (t,stack as s') = apprec_nobeta env (evars_of isevars) s in
    match kind_of_term t with
      | Evar (n,_ as ev) when Evd.is_defined (evars_of isevars) n ->
	  aux (Evd.existential_value (evars_of isevars) ev, stack)
      | _ -> (t, list_of_stack stack)
  in aux (c, append_stack (Array.of_list stack) empty_stack)
*)

let evar_apprec env isevars stack c =
  let sigma = evars_of isevars in
  let rec aux s =
    let (t,stack) = Reductionops.apprec env sigma s in
    match kind_of_term t with
      | Evar (n,_ as ev) when Evd.is_defined sigma n ->
	  aux (Evd.existential_value sigma ev, stack)
      | _ -> (t, list_of_stack stack)
  in aux (c, append_stack_list stack empty_stack)

let apprec_nohdbeta env isevars c =
  let (t,stack as s) = Reductionops.whd_stack c in
  match kind_of_term t with
    | (Case _ | Fix _) -> evar_apprec env isevars [] c
    | _ -> s

(* [check_conv_record (t1,l1) (t2,l2)] tries to decompose the problem
   (t1 l1) = (t2 l2) into a problem

     l1 = params1@c1::extra_args1
     l2 = us2@extra_args2
     (t1 params1 c1) = (proji params (c xs))
     (t2 us2) = (cstr us)
     extra_args1 = extra_args2

   by finding a record R and an object c := [xs:bs](Build_R params v1..vn)
   with vi = (cstr us), for which we know that the i-th projection proji
   satisfies

      (proji params (c xs)) = (cstr us)

   Rem: such objects, usable for conversion, are defined in the objdef
   table; practically, it amounts to "canonically" equip t2 into a
   object c in structure R (since, if c1 were not an evar, the
   projection would have been reduced) *)

let check_conv_record (t1,l1) (t2,l2) =
  try
    let proji = global_of_constr t1 in
    let cstr = global_of_constr t2 in
    let { o_DEF = c; o_TABS = bs; o_TPARAMS = params; o_TCOMPS = us } = 
      lookup_canonical_conversion (proji, cstr) in
    let params1, c1, extra_args1 =
      match list_chop (List.length params) l1 with 
	| params1, c1::extra_args1 -> params1, c1, extra_args1
	| _ -> assert false in
    let us2,extra_args2 = list_chop (List.length us) l2 in
    c,bs,(params,params1),(us,us2),(extra_args1,extra_args2),c1
  with _ -> 
    raise Not_found

(* Precondition: one of the terms of the pb is an uninstantiated evar,
 * possibly applied to arguments. *)

let rec ise_try isevars = function
    [] -> assert false
  | [f] -> f isevars
  | f1::l ->
      let (isevars',b) = f1 isevars in
      if b then (isevars',b) else ise_try isevars l

let ise_and isevars l =
  let rec ise_and i = function
      [] -> assert false
    | [f] -> f i
    | f1::l ->
        let (i',b) = f1 i in
        if b then  ise_and i' l else (isevars,false) in
  ise_and isevars l

let ise_list2 isevars f l1 l2 =
  let rec ise_list2 i l1 l2 =
    match l1,l2 with
        [], [] -> (i, true)
      | [x], [y] -> f i x y
      | x::l1, y::l2 ->
          let (i',b) = f i x y in
          if b then ise_list2 i' l1 l2 else (isevars,false)
      | _ -> (isevars, false) in
  ise_list2 isevars l1 l2

let ise_array2 isevars f v1 v2 =
  let rec allrec i = function
    | -1 -> (i,true)
    | n ->
        let (i',b) = f i v1.(n) v2.(n) in
        if b then allrec i' (n-1) else (isevars,false)
  in 
  let lv1 = Array.length v1 in
  if lv1 = Array.length v2 then allrec isevars (pred lv1) 
  else (isevars,false)

let rec evar_conv_x env isevars pbty term1 term2 = 
  let sigma = evars_of isevars in
  let term1 = whd_castappevar sigma term1 in
  let term2 = whd_castappevar sigma term2 in
(*
  if eq_constr term1 term2 then 
    true
  else 
*)
  (* Maybe convertible but since reducing can erase evars which [evar_apprec]
     could have found, we do it only if the terms are free of evar.
     Note: incomplete heuristic... *)
  if is_ground_term isevars term1 && is_ground_term isevars term2 &
     is_fconv pbty env (evars_of isevars) term1 term2 then
      (isevars,true)
  else if is_undefined_evar isevars term1 then
    solve_simple_eqn evar_conv_x env isevars (pbty,destEvar term1,term2)
  else if is_undefined_evar isevars term2 then
    solve_simple_eqn evar_conv_x env isevars (pbty,destEvar term2,term1)
  else 
    let (t1,l1) = apprec_nohdbeta env isevars term1 in
    let (t2,l2) = apprec_nohdbeta env isevars term2 in
    evar_eqappr_x env isevars pbty (t1,l1) (t2,l2)

and evar_eqappr_x env isevars pbty (term1,l1 as appr1) (term2,l2 as appr2) =
  (* Evar must be undefined since we have whd_ised *)
  match (flex_kind_of_term term1 l1, flex_kind_of_term term2 l2) with
    | Flexible (sp1,al1 as ev1), Flexible (sp2,al2 as ev2) ->
	let f1 i =
	  if List.length l1 > List.length l2 then 
            let (deb1,rest1) = list_chop (List.length l1-List.length l2) l1 in
            ise_and i
              [(fun i -> solve_simple_eqn evar_conv_x env i
	        (pbty,ev2,applist(term1,deb1)));
              (fun i -> ise_list2 i
                  (fun i -> evar_conv_x env i CONV) rest1 l2)]
	  else
	    let (deb2,rest2) = list_chop (List.length l2-List.length l1) l2 in
            ise_and i
              [(fun i -> solve_simple_eqn evar_conv_x env i
	          (pbty,ev1,applist(term2,deb2)));
              (fun i -> ise_list2 i
                  (fun i -> evar_conv_x env i CONV) l1 rest2)]
	and f2 i =
          if sp1 = sp2 then
            ise_and i
            [(fun i -> ise_array2 i
                (fun i -> evar_conv_x env i CONV) al1 al2);
             (fun i -> ise_list2 i
                 (fun i -> evar_conv_x env i CONV) l1 l2)]
          else (i,false)
	in 
	ise_try isevars [f1; f2]

    | Flexible ev1, MaybeFlexible flex2 ->
	let f1 i =
	  if 
	    is_unification_pattern_evar ev1 l1 & 
	    not (occur_evar (fst ev1) (applist (term2,l2)))
	  then
	    (* Miller-Pfenning's patterns unification *)
	    (* Preserve generality (except that CCI has no eta-conversion) *)
	    let t2 = nf_evar (evars_of isevars) (applist(term2,l2)) in
	    let t2 = solve_pattern_eqn env l1 t2 in
	    solve_simple_eqn evar_conv_x env isevars (pbty,ev1,t2)
	  else if
            List.length l1 <= List.length l2
	  then
	    (* Try first-order unification *)
	    (* (heuristic that gives acceptable results in practice) *)
	    let (deb2,rest2) =
              list_chop (List.length l2-List.length l1) l2 in
            ise_and i
              (* First compare extra args for better failure message *)
              [(fun i -> ise_list2 i
                  (fun i -> evar_conv_x env i CONV) l1 rest2);
               (fun i -> evar_conv_x env i pbty term1 (applist(term2,deb2)))]
          else (i,false)
	and f4 i =
	  match eval_flexible_term env flex2 with
	    | Some v2 ->
		evar_eqappr_x env i pbty appr1 (evar_apprec env i l2 v2)
	    | None -> (i,false)
	in 
	ise_try isevars [f1; f4]

    | MaybeFlexible flex1, Flexible ev2 ->
	let f1 i =
	  if 
	    is_unification_pattern_evar ev2 l2 & 
	    not (occur_evar (fst ev2) (applist (term1,l1)))
	  then
	    (* Miller-Pfenning's patterns unification *)
	    (* Preserve generality (except that CCI has no eta-conversion) *)
	    let t1 = nf_evar (evars_of isevars) (applist(term1,l1)) in
	    let t1 = solve_pattern_eqn env l2 t1 in
	    solve_simple_eqn evar_conv_x env isevars (pbty,ev2,t1)
	  else if
       	    List.length l2 <= List.length l1
	  then
	    (* Try first-order unification *)
	    (* (heuristic that gives acceptable results in practice) *)
            let (deb1,rest1) = list_chop (List.length l1-List.length l2) l1 in
            ise_and i
            (* First compare extra args for better failure message *)
              [(fun i -> ise_list2 i
                  (fun i -> evar_conv_x env i CONV) rest1 l2);
               (fun i -> evar_conv_x env i pbty (applist(term1,deb1)) term2)]
          else (i,false)
	and f4 i =
	  match eval_flexible_term env flex1 with
	    | Some v1 ->
		evar_eqappr_x env i pbty (evar_apprec env i l1 v1) appr2
	    | None -> (i,false)
	in 
	ise_try isevars [f1; f4]

    | MaybeFlexible flex1, MaybeFlexible flex2 ->
	let f2 i =
          if flex1 = flex2 then
            ise_list2 i (fun i -> evar_conv_x env i CONV) l1 l2
          else (i,false)
	and f3 i =
	  (try conv_record env i
             (try check_conv_record appr1 appr2
	      with Not_found -> check_conv_record appr2 appr1)
           with Not_found -> (i,false))
	and f4 i =
          (* heuristic: unfold second argument first, exception made
             if the first argument is a beta-redex (expand a constant
             only if necessary) *)
          let val2 =
            match kind_of_term flex1 with
                Lambda _ -> None
              | _ -> eval_flexible_term env flex2 in
	  match val2 with
	    | Some v2 ->
		evar_eqappr_x env i pbty appr1 (evar_apprec env i l2 v2)
	    | None ->
		match eval_flexible_term env flex1 with
		  | Some v1 ->
		      evar_eqappr_x env i pbty (evar_apprec env i l1 v1) appr2
		  | None -> (i,false)
	in 
	ise_try isevars [f2; f3; f4]

    | Flexible ev1, Rigid _ ->
	if 
	  is_unification_pattern_evar ev1 l1 & 
	  not (occur_evar (fst ev1) (applist (term2,l2)))
	then
	  (* Miller-Pfenning's patterns unification *)
	  (* Preserve generality (except that CCI has no eta-conversion) *)
	  let t2 = nf_evar (evars_of isevars) (applist(term2,l2)) in
	  let t2 = solve_pattern_eqn env l1 t2 in
	  solve_simple_eqn evar_conv_x env isevars (pbty,ev1,t2)
	else
	  (* Postpone the use of an heuristic *)
	  add_conv_pb (pbty,applist(term1,l1),applist(term2,l2)) isevars,
	  true

    | Rigid _, Flexible ev2 ->
	if 
	  is_unification_pattern_evar ev2 l2 & 
	  not (occur_evar (fst ev2) (applist (term1,l1)))
	then
	  (* Miller-Pfenning's patterns unification *)
	  (* Preserve generality (except that CCI has no eta-conversion) *)
	  let t1 = nf_evar (evars_of isevars) (applist(term1,l1)) in
	  let t1 = solve_pattern_eqn env l2 t1 in
	  solve_simple_eqn evar_conv_x env isevars (pbty,ev2,t1)
	else
	  (* Postpone the use of an heuristic *)
	  add_conv_pb (pbty,applist(term1,l1),applist(term2,l2)) isevars,
	  true

    | MaybeFlexible flex1, Rigid _ ->
	let f3 i =
	  (try conv_record env i (check_conv_record appr1 appr2)
           with Not_found -> (i,false))
	and f4 i =
	  match eval_flexible_term env flex1 with
	    | Some v1 ->
 		evar_eqappr_x env i pbty (evar_apprec env i l1 v1) appr2
	    | None -> (i,false)
	in 
	ise_try isevars [f3; f4]
	     
    | Rigid _ , MaybeFlexible flex2 -> 
	let f3 i = 
	  (try conv_record env i (check_conv_record appr2 appr1)
           with Not_found -> (i,false))
	and f4 i =
	  match eval_flexible_term env flex2 with
	    | Some v2 ->
 		evar_eqappr_x env i pbty appr1 (evar_apprec env i l2 v2)
	    | None -> (i,false)
	in 
	ise_try isevars [f3; f4]

    | Rigid c1, Rigid c2 -> match kind_of_term c1, kind_of_term c2 with
	  
	| Cast (c1,_,_), _ -> evar_eqappr_x env isevars pbty (c1,l1) appr2

	| _, Cast (c2,_,_) -> evar_eqappr_x env isevars pbty appr1 (c2,l2)

	| Sort s1, Sort s2 when l1=[] & l2=[] ->
            (isevars,base_sort_cmp pbty s1 s2)

	| Lambda (na,c1,c'1), Lambda (_,c2,c'2) when l1=[] & l2=[] -> 
            ise_and isevars
              [(fun i -> evar_conv_x env i CONV c1 c2);
               (fun i ->
                 let c = nf_evar (evars_of i) c1 in
                 evar_conv_x (push_rel (na,None,c) env) i CONV c'1 c'2)]

	| LetIn (na,b1,t1,c'1), LetIn (_,b2,_,c'2) ->
	    let f1 i =
              ise_and i
                [(fun i -> evar_conv_x env i CONV b1 b2);
                 (fun i ->
                   let b = nf_evar (evars_of i) b1 in
	           let t = nf_evar (evars_of i) t1 in
                   evar_conv_x (push_rel (na,Some b,t) env) i pbty c'1 c'2);
                 (fun i -> ise_list2 i
                     (fun i -> evar_conv_x env i CONV) l1 l2)]
	    and f2 i =
              let appr1 = evar_apprec env i l1 (subst1 b1 c'1)
              and appr2 = evar_apprec env i l2 (subst1 b2 c'2)
	      in evar_eqappr_x env i pbty appr1 appr2
	    in 
	    ise_try isevars [f1; f2]

	| LetIn (_,b1,_,c'1), _ ->(* On fait commuter les args avec le Let *)
	     let appr1 = evar_apprec env isevars l1 (subst1 b1 c'1)
             in evar_eqappr_x env isevars pbty appr1 appr2

	| _, LetIn (_,b2,_,c'2) ->
	    let appr2 = evar_apprec env isevars l2 (subst1 b2 c'2)
            in evar_eqappr_x env isevars pbty appr1 appr2

	| Prod (n,c1,c'1), Prod (_,c2,c'2) when l1=[] & l2=[] -> 
            ise_and isevars
              [(fun i -> evar_conv_x env i CONV c1 c2);
               (fun i ->
 	         let c = nf_evar (evars_of i) c1 in
	         evar_conv_x (push_rel (n,None,c) env) i pbty c'1 c'2)]

	| Ind sp1, Ind sp2 ->
	    if sp1=sp2 then
              ise_list2 isevars (fun i -> evar_conv_x env i CONV) l1 l2
            else (isevars, false)

	| Construct sp1, Construct sp2 ->
	    if sp1=sp2 then
              ise_list2 isevars (fun i -> evar_conv_x env i CONV) l1 l2
            else (isevars, false)

	| Case (_,p1,c1,cl1), Case (_,p2,c2,cl2) ->
            ise_and isevars
              [(fun i -> evar_conv_x env i CONV p1 p2);
               (fun i -> evar_conv_x env i CONV c1 c2);
	       (fun i -> ise_array2 i
                   (fun i -> evar_conv_x env i CONV) cl1 cl2);
               (fun i -> ise_list2 i (fun i -> evar_conv_x env i CONV) l1 l2)]

	| Fix (li1,(_,tys1,bds1 as recdef1)), Fix (li2,(_,tys2,bds2)) ->
            if li1=li2 then
              ise_and isevars
                [(fun i -> ise_array2 i
                    (fun i -> evar_conv_x env i CONV) tys1 tys2);
                 (fun i -> ise_array2 i
		     (fun i -> evar_conv_x (push_rec_types recdef1 env) i CONV)
		     bds1 bds2);
	         (fun i -> ise_list2 i
                     (fun i -> evar_conv_x env i CONV) l1 l2)]
	    else (isevars,false)
	| CoFix (i1,(_,tys1,bds1 as recdef1)), CoFix (i2,(_,tys2,bds2)) ->
            if i1=i2  then
              ise_and isevars
                [(fun i -> ise_array2 i
                    (fun i -> evar_conv_x env i CONV) tys1 tys2);
                 (fun i -> ise_array2 i
		     (fun i -> evar_conv_x (push_rec_types recdef1 env) i CONV)
		     bds1 bds2);
                 (fun i -> ise_list2 i
                     (fun i -> evar_conv_x env i CONV) l1 l2)]
            else (isevars,false)

	| (Meta _ | Lambda _), _ -> (isevars,false)
	| _, (Meta _ | Lambda _) -> (isevars,false)

	| (Ind _ | Construct _ | Sort _ | Prod _), _ -> (isevars,false)
	| _, (Ind _ | Construct _ | Sort _ | Prod _) -> (isevars,false)

	| (App _ | Case _ | Fix _ | CoFix _), 
	  (App _ | Case _ | Fix _ | CoFix _) -> (isevars,false)

	| (Rel _ | Var _ | Const _ | Evar _), _ -> assert false
	| _, (Rel _ | Var _ | Const _ | Evar _) -> assert false

and conv_record env isevars (c,bs,(params,params1),(us,us2),(ts,ts1),c1) = 
  let (isevars',ks) =
    List.fold_left
      (fun (i,ks) b ->
	 let dloc = (dummy_loc,InternalHole) in
         let (i',ev) = new_evar i env ~src:dloc (substl ks b) in
	 (i', ev :: ks))
      (isevars,[]) bs
  in
  ise_and isevars'
    [(fun i ->
      ise_list2 i
        (fun i u1 u -> evar_conv_x env i CONV u1 (substl ks u))
        us2 us);
     (fun i ->
       ise_list2 i
         (fun i x1 x -> evar_conv_x env i CONV x1 (substl ks x))
         params1 params);
     (fun i -> ise_list2 i (fun i -> evar_conv_x env i CONV) ts ts1);
     (fun i -> evar_conv_x env i CONV c1 (applist (c,(List.rev ks))))]

let first_order_unification env isevars pbty (term1,l1) (term2,l2) =
  match kind_of_term term1, kind_of_term term2 with
    | Evar ev1,_ when List.length l1 <= List.length l2 ->
	let (deb2,rest2) = list_chop (List.length l2-List.length l1) l2 in
	ise_and isevars
          (* First compare extra args for better failure message *)
        [(fun i -> ise_list2 i (fun i -> evar_conv_x env i CONV) rest2 l1);
	(fun i ->
          (* Then instantiate evar unless already done by unifying args *)
	  let t2 = applist(term2,deb2) in
	  if is_defined_evar i ev1 then
	    evar_conv_x env i pbty t2 (mkEvar ev1)
	  else
	    solve_simple_eqn evar_conv_x env i (pbty,ev1,t2))]
    | _,Evar ev2 when List.length l2 <= List.length l1 ->
	let (deb1,rest1) = list_chop (List.length l1-List.length l2) l1 in
	ise_and isevars
          (* First compare extra args for better failure message *)
        [(fun i -> ise_list2 i (fun i -> evar_conv_x env i CONV) rest1 l2);
	(fun i ->
          (* Then instantiate evar unless already done by unifying args *)
	  let t1 = applist(term1,deb1) in
	  if is_defined_evar i ev2 then
	    evar_conv_x env i pbty t1 (mkEvar ev2)
	  else
	    solve_simple_eqn evar_conv_x env i (pbty,ev2,t1))]
    | _ -> 
	(* Some head evar have been instantiated *)
	evar_conv_x env isevars pbty (applist(term1,l1)) (applist(term2,l2))

let consider_remaining_unif_problems env isevars =
  let (isevars,pbs) = get_conv_pbs isevars (fun _ -> true) in
  List.fold_left
    (fun (isevars,b as p) (pbty,t1,t2) ->
      (* Pas le bon env pour le problème... *)
      if b then first_order_unification env isevars pbty 
	(apprec_nohdbeta env isevars (whd_castappevar (evars_of isevars) t1))
	(apprec_nohdbeta env isevars (whd_castappevar (evars_of isevars) t2))
      else p)
    (isevars,true)
    pbs

(* Main entry points *)

let the_conv_x     env t1 t2 isevars =
  match evar_conv_x env isevars CONV  t1 t2 with
      (evd',true) -> evd'
    | _ -> raise Reduction.NotConvertible

let the_conv_x_leq env t1 t2 isevars =
  match evar_conv_x env isevars CUMUL t1 t2 with
      (evd', true) -> evd'
    | _ -> raise Reduction.NotConvertible
 
let e_conv env isevars t1 t2 =
  match evar_conv_x env !isevars CONV t1 t2 with
      (evd',true) -> isevars := evd'; true
    | _ -> false

let e_cumul env isevars t1 t2 =
  match evar_conv_x env !isevars CUMUL t1 t2 with
      (evd',true) -> isevars := evd'; true
    | _ -> false
