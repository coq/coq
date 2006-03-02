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
open Closure
open Instantiate
open Environ
open Typing
open Classops
open Recordops 
open Evarutil
open Libnames

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
      (try let (_,v,_) = lookup_rel n env in option_app (lift n) v
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
	  aux (existential_value (evars_of isevars) ev, stack)
      | _ -> (t, list_of_stack stack)
  in aux (c, append_stack (Array.of_list stack) empty_stack)
*)

let evar_apprec env isevars stack c =
  let sigma = evars_of isevars in
  let rec aux s =
    let (t,stack as s') = Reductionops.apprec env sigma s in
    match kind_of_term t with
      | Evar (n,_ as ev) when Evd.is_defined sigma n ->
	  aux (existential_value sigma ev, stack)
      | _ -> (t, list_of_stack stack)
  in aux (c, append_stack (Array.of_list stack) empty_stack)

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

   by finding a record R and an object c := [xs:bs](Build_R a1..am v1..vn)
   with vi = (cstr us), for which we know that the i-th projection proji
   satisfies

      (proji params c) = (cstr us)

   Rem: such objects, usable for conversion, are defined in the objdef
   table; practically, it amounts to "canonically" equip t2 into a
   object c in structure R (since, if c1 were not an evar, the
   projection would have been reduced) *)

let check_conv_record (t1,l1) (t2,l2) =
  try
    let proji = reference_of_constr t1 in
    let cstr = reference_of_constr t2 in
    let { o_DEF = c; o_TABS = bs; o_TPARAMS = params; o_TCOMPS = us } = 
      objdef_info (proji, cstr) in
    let params1, c1, extra_args1 =
      match list_chop (List.length params) l1 with 
	| params1, c1::extra_args1 -> params1, c1, extra_args1
	| _ -> assert false in
    let us2,extra_args2 = list_chop (List.length us) l2 in
    c,bs,(params,params1),(us,us2),(extra_args1,extra_args2),c1
  with _ -> 
    raise Not_found


(* Precondition: one of the terms of the pb is an uninstanciated evar,
 * possibly applied to arguments. *)

let rec evar_conv_x env isevars pbty term1 term2 = 
  let sigma = evars_of isevars in
  let term1 = whd_castappevar sigma term1 in
  let term2 = whd_castappevar sigma term2 in
(*
  if eq_constr term1 term2 then 
    true
  else 
*)
  (* Maybe convertible but since reducing can erase evars which [evar_apprec]*)
  (* could have found, we do it only if the terms are free of evar  *)
  (not (has_undefined_isevars isevars term1) &
   not (has_undefined_isevars isevars term2) &
   is_fconv pbty env (evars_of isevars) term1 term2) 
  or
  if ise_undefined isevars term1 then
    solve_simple_eqn evar_conv_x env isevars (pbty,destEvar term1,term2)
  else if ise_undefined isevars term2 then
    solve_simple_eqn evar_conv_x env isevars (pbty,destEvar term2,term1)
  else 
    let (t1,l1) = apprec_nohdbeta env isevars term1 in
    let (t2,l2) = apprec_nohdbeta env isevars term2 in
    if (head_is_embedded_evar isevars t1 & not(is_eliminator t2))
      or (head_is_embedded_evar isevars t2 & not(is_eliminator t1))
    then 
      (add_conv_pb isevars (pbty,applist(t1,l1),applist(t2,l2)); true)
    else 
      evar_eqappr_x env isevars pbty (t1,l1) (t2,l2)

and evar_eqappr_x env isevars pbty (term1,l1 as appr1) (term2,l2 as appr2) =
  (* Evar must be undefined since we have whd_ised *)
  match (flex_kind_of_term term1 l1, flex_kind_of_term term2 l2) with
    | Flexible (sp1,al1 as ev1), Flexible (sp2,al2 as ev2) ->
	let f1 () =
	  if List.length l1 > List.length l2 then 
            let (deb1,rest1) = list_chop (List.length l1-List.length l2) l1 in
            solve_simple_eqn evar_conv_x env isevars 
	      (pbty,ev2,applist(term1,deb1))
            & list_for_all2eq (evar_conv_x env isevars CONV) rest1 l2
	  else
	    let (deb2,rest2) = list_chop (List.length l2-List.length l1) l2 in
	    solve_simple_eqn evar_conv_x env isevars
	      (pbty,ev1,applist(term2,deb2))
            & list_for_all2eq (evar_conv_x env isevars CONV) l1 rest2
	and f2 () =
          (sp1 = sp2)
	  & (array_for_all2 (evar_conv_x env isevars CONV) al1 al2)  
	  & (list_for_all2eq (evar_conv_x env isevars CONV) l1 l2)
	in 
	ise_try isevars [f1; f2]

    | Flexible ev1, MaybeFlexible flex2 ->
	let f1 () =
	  (List.length l1 <= List.length l2) &
	  let (deb2,rest2) = list_chop (List.length l2-List.length l1) l2 in
          (* First compare extra args for better failure message *)
          list_for_all2eq (evar_conv_x env isevars CONV) l1 rest2 &
	  evar_conv_x env isevars pbty term1 (applist(term2,deb2))
	and f4 () =
	  match eval_flexible_term env flex2 with
	    | Some v2 ->
		evar_eqappr_x env isevars pbty
		  appr1 (evar_apprec env isevars l2 v2)
	    | None -> false
	in 
	ise_try isevars [f1; f4]

    | MaybeFlexible flex1, Flexible ev2 ->
	let f1 () =
       	  (List.length l2 <= List.length l1) &
       	  let (deb1,rest1) = list_chop (List.length l1-List.length l2) l1 in
          (* First compare extra args for better failure message *)
          list_for_all2eq (evar_conv_x env isevars CONV) rest1 l2 &
	  evar_conv_x env isevars pbty (applist(term1,deb1)) term2
	and f4 () =
	  match eval_flexible_term env flex1 with
	    | Some v1 ->
		evar_eqappr_x env isevars pbty
		  (evar_apprec env isevars l1 v1) appr2
	    | None -> false
	in 
	ise_try isevars [f1; f4]

    | MaybeFlexible flex1, MaybeFlexible flex2 ->
	let f2 () =
          (flex1 = flex2)
	  & (List.length l1 = List.length l2)
	  & (list_for_all2eq (evar_conv_x env isevars CONV) l1 l2)
	and f3 () =
	  (try conv_record env isevars 
             (try check_conv_record appr1 appr2
	      with Not_found -> check_conv_record appr2 appr1)
           with _ -> false)
	and f4 () =
          (* heuristic: unfold second argument first, exception made
             if the first argument is a beta-redex (expand a constant
             only if necessary) *)
          let val2 =
            match kind_of_term flex1 with
                Lambda _ -> None
              | _ -> eval_flexible_term env flex2 in
	  match val2 with
	    | Some v2 ->
		evar_eqappr_x env isevars pbty
		  appr1 (evar_apprec env isevars l2 v2)
	    | None ->
		match eval_flexible_term env flex1 with
		  | Some v1 ->
		      evar_eqappr_x env isevars pbty
			(evar_apprec env isevars l1 v1) appr2
		  | None -> false
	in 
	ise_try isevars [f2; f3; f4]

    | Flexible ev1, Rigid _ ->
       	(List.length l1 <= List.length l2) &
       	let (deb2,rest2) = list_chop (List.length l2-List.length l1) l2 in
        (* First compare extra args for better failure message *)
        list_for_all2eq (evar_conv_x env isevars CONV) l1 rest2 &
	if is_defined_evar isevars ev1 then
	  evar_conv_x env isevars pbty (mkEvar ev1) (applist(term2,deb2))
	else
	  solve_simple_eqn evar_conv_x env isevars
	    (pbty,ev1,applist(term2,deb2))

    | Rigid _, Flexible ev2 ->
       	(List.length l2 <= List.length l1) &
       	let (deb1,rest1) = list_chop (List.length l1-List.length l2) l1 in
        (* First compare extra args for better failure message *)
        list_for_all2eq (evar_conv_x env isevars CONV) rest1 l2 &
	if is_defined_evar isevars ev2 then
	  evar_conv_x env isevars pbty (applist(term1,deb1)) (mkEvar ev2)
	else
	  solve_simple_eqn evar_conv_x env isevars
	    (pbty,ev2,applist(term1,deb1))
        

    | MaybeFlexible flex1, Rigid _ ->
	let f3 () =
	  (try conv_record env isevars (check_conv_record appr1 appr2)
           with _ -> false)
	and f4 () =
	  match eval_flexible_term env flex1 with
	    | Some v1 ->
 		evar_eqappr_x env isevars pbty
		  (evar_apprec env isevars l1 v1) appr2
	    | None -> false
	in 
	ise_try isevars [f3; f4]
	     
    | Rigid _ , MaybeFlexible flex2 -> 
	let f3 () = 
	  (try (conv_record env isevars (check_conv_record appr2 appr1))
           with _ -> false)
	and f4 () =
	  match eval_flexible_term env flex2 with
	    | Some v2 ->
 		evar_eqappr_x env isevars pbty
		  appr1 (evar_apprec env isevars l2 v2)
	    | None -> false
	in 
	ise_try isevars [f3; f4]

    | Rigid c1, Rigid c2 -> match kind_of_term c1, kind_of_term c2 with
	  
	| Cast (c1,_), _ -> evar_eqappr_x env isevars pbty (c1,l1) appr2

	| _, Cast (c2,_) -> evar_eqappr_x env isevars pbty appr1 (c2,l2)

	| Sort s1, Sort s2 when l1=[] & l2=[] -> base_sort_cmp pbty s1 s2

	| Lambda (na,c1,c'1), Lambda (_,c2,c'2) when l1=[] & l2=[] -> 
	    evar_conv_x env isevars CONV c1 c2
	    & 
	    (let c = nf_evar (evars_of isevars) c1 in
             evar_conv_x (push_rel (na,None,c) env) isevars CONV c'1 c'2)

	| LetIn (na,b1,t1,c'1), LetIn (_,b2,_,c'2) ->
	    let f1 () =
	      evar_conv_x env isevars CONV b1 b2
	      & 
              (let b = nf_evar (evars_of isevars) b1 in
	       let t = nf_evar (evars_of isevars) t1 in
               evar_conv_x (push_rel (na,Some b,t) env) isevars pbty c'1 c'2)
	      & (List.length l1 = List.length l2)
	      & (List.for_all2 (evar_conv_x env isevars CONV) l1 l2)
	    and f2 () =
              let appr1 = evar_apprec env isevars l1 (subst1 b1 c'1)
              and appr2 = evar_apprec env isevars l2 (subst1 b2 c'2)
	      in evar_eqappr_x env isevars pbty appr1 appr2
	    in 
	    ise_try isevars [f1; f2]

	| LetIn (_,b1,_,c'1), _ ->(* On fait commuter les args avec le Let *)
	     let appr1 = evar_apprec env isevars l1 (subst1 b1 c'1)
             in evar_eqappr_x env isevars pbty appr1 appr2

	| _, LetIn (_,b2,_,c'2) ->
	    let appr2 = evar_apprec env isevars l2 (subst1 b2 c'2)
            in evar_eqappr_x env isevars pbty appr1 appr2

	| Prod (n,c1,c'1), Prod (_,c2,c'2) when l1=[] & l2=[] -> 
            evar_conv_x env isevars CONV c1 c2
            & 
	    (let c = nf_evar (evars_of isevars) c1 in
	     evar_conv_x (push_rel (n,None,c) env) isevars pbty c'1 c'2)

	| Ind sp1, Ind sp2 ->
	    sp1=sp2
            & list_for_all2eq (evar_conv_x env isevars CONV) l1 l2
             
	| Construct sp1, Construct sp2 ->
	    sp1=sp2
            & list_for_all2eq (evar_conv_x env isevars CONV) l1 l2

	| Case (_,p1,c1,cl1), Case (_,p2,c2,cl2) ->
	    evar_conv_x env isevars CONV p1 p2
	    & evar_conv_x env isevars CONV c1 c2
	    & (array_for_all2 (evar_conv_x env isevars CONV) cl1 cl2)
	    & (list_for_all2eq (evar_conv_x env isevars CONV) l1 l2)

	| Fix (li1,(_,tys1,bds1 as recdef1)), Fix (li2,(_,tys2,bds2)) ->
	    li1=li2
	    & (array_for_all2 (evar_conv_x env isevars CONV) tys1 tys2)
	    & (array_for_all2
		 (evar_conv_x (push_rec_types recdef1 env) isevars CONV)
		 bds1 bds2)
	    & (list_for_all2eq (evar_conv_x env isevars CONV) l1 l2)
	     
	| CoFix (i1,(_,tys1,bds1 as recdef1)), CoFix (i2,(_,tys2,bds2)) ->
	    i1=i2 
	    & (array_for_all2 (evar_conv_x env isevars CONV) tys1 tys2)
	    & (array_for_all2
		 (evar_conv_x (push_rec_types recdef1 env) isevars CONV)
		 bds1 bds2)
	    & (list_for_all2eq (evar_conv_x env isevars CONV) l1 l2)

	| (Meta _ | Lambda _), _ -> false
	| _, (Meta _ | Lambda _) -> false

	| (Ind _ | Construct _ | Sort _ | Prod _), _ -> false
	| _, (Ind _ | Construct _ | Sort _ | Prod _) -> false

	| (App _ | Case _ | Fix _ | CoFix _), 
	  (App _ | Case _ | Fix _ | CoFix _) -> false

	| (Rel _ | Var _ | Const _ | Evar _), _ -> assert false
	| _, (Rel _ | Var _ | Const _ | Evar _) -> assert false

and conv_record env isevars (c,bs,(params,params1),(us,us2),(ts,ts1),c1) = 
  let ks =
    List.fold_left
      (fun ks b ->
	 let dloc = (dummy_loc,Rawterm.InternalHole) in
	 (new_isevar isevars env dloc (substl ks b)) :: ks)
      [] bs
  in
  (list_for_all2eq 
     (fun u1 u -> evar_conv_x env isevars CONV u1 (substl ks u))
     us2 us)
  &
  (list_for_all2eq 
     (fun x1 x -> evar_conv_x env isevars CONV x1 (substl ks x))
     params1 params)
  & (list_for_all2eq (evar_conv_x env isevars CONV) ts ts1)
  & (evar_conv_x env isevars CONV c1 (applist (c,(List.rev ks))))
    
let the_conv_x     env isevars t1 t2 = evar_conv_x env isevars CONV  t1 t2
let the_conv_x_leq env isevars t1 t2 = evar_conv_x env isevars CUMUL t1 t2
 
