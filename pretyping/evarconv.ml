
(* $Id$ *)

open Util
open Names
open Term
open Reduction
open Instantiate
open Environ
open Typing
open Classops
open Recordops 
open Evarutil


type flexible_term = FConst of constant | FRel of int | FVar of identifier 
type flex_kind_of_term =
  | Rigid of constr 
  | MaybeFlexible of flexible_term
  | Flexible of existential

let flex_kind_of_term c =
  match kind_of_term c with
    | IsConst c -> MaybeFlexible (FConst c)
    | IsRel n -> MaybeFlexible (FRel n)
    | IsVar id -> MaybeFlexible (FVar id)
    | IsEvar ev -> Flexible ev
    | _ -> Rigid c

let eval_flexible_term env = function
  | FConst c -> constant_opt_value env c
  | FRel n -> option_app (lift n) (lookup_rel_value n env)
  | FVar id -> lookup_named_value id env

let evar_apprec env isevars stack c =
  let rec aux s =
    let (t,stack as s') = Reduction.apprec env !isevars s in
    match kind_of_term t with
      | IsEvar (n,_ as ev) when Evd.is_defined !isevars n ->
	  aux (existential_value !isevars ev, stack)
      | _ -> (t, list_of_stack stack)
  in aux (c, append_stack (Array.of_list stack) empty_stack)

(* Precondition: one of the terms of the pb is an uninstanciated evar,
 * possibly applied to arguments. *)

let rec evar_conv_x env isevars pbty term1 term2 =
  let term1 = whd_ise1 !isevars term1 in
  let term2 = whd_ise1 !isevars term2 in
(*
 if eq_constr term1 term2 then 
    true
  else if (not(has_undefined_isevars isevars term1)) &
    not(has_undefined_isevars isevars term2) 
  then 
    is_fconv pbty env !isevars term1 term2
  else
*)
  (is_fconv pbty env !isevars term1 term2) or
  if ise_undefined isevars term1 then
    solve_simple_eqn evar_conv_x env isevars (pbty,destEvar term1,term2)
  else if ise_undefined isevars term2 then
    solve_simple_eqn evar_conv_x env isevars (pbty,destEvar term2,term1)
  else 
    let (t1,l1) = evar_apprec env isevars [] term1 in
    let (t2,l2) = evar_apprec env isevars [] term2 in
    if (head_is_embedded_evar isevars t1 & not(is_eliminator t2))
      or (head_is_embedded_evar isevars t2 & not(is_eliminator t1))
    then 
      (add_conv_pb (pbty,applist(t1,l1),applist(t2,l2)); true)
    else 
      evar_eqappr_x env isevars pbty (t1,l1) (t2,l2)

and evar_eqappr_x env isevars pbty (term1,l1 as appr1) (term2,l2 as appr2) =
  (* Evar must be undefined since we have whd_ised *)
  match (flex_kind_of_term term1, flex_kind_of_term term2) with
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
	  solve_simple_eqn evar_conv_x env isevars
	    (pbty,ev1,applist(term2,deb2))
          & list_for_all2eq (evar_conv_x env isevars CONV) l1 rest2
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
	  solve_simple_eqn evar_conv_x env isevars
	    (pbty,ev2,applist(term1,deb1))
          & list_for_all2eq (evar_conv_x env isevars CONV) rest1 l2
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
	  & (list_for_all2eq (evar_conv_x env isevars CONV) l1 l2)
	and f3 () =
	  (try conv_record env isevars 
             (try check_conv_record appr1 appr2
	      with Not_found -> check_conv_record appr2 appr1)
           with _ -> false)
	and f4 () =
	  match eval_flexible_term env flex2 with
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
	solve_simple_eqn evar_conv_x env isevars
	  (pbty,ev1,applist(term2,deb2))
        & list_for_all2eq (evar_conv_x env isevars CONV) l1 rest2

    | Rigid _, Flexible ev2 ->
       	(List.length l2 <= List.length l1) &
       	let (deb1,rest1) = list_chop (List.length l1-List.length l2) l1 in
	solve_simple_eqn evar_conv_x env isevars
	  (pbty,ev2,applist(term1,deb1))
        & list_for_all2eq (evar_conv_x env isevars CONV) rest1 l2

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
	  
	| IsCast (c1,_), _ -> evar_eqappr_x env isevars pbty (c1,l1) appr2

	| _, IsCast (c2,_) -> evar_eqappr_x env isevars pbty appr1 (c2,l2)

	| IsSort s1, IsSort s2 when l1=[] & l2=[] -> base_sort_cmp pbty s1 s2

	| IsLambda (_,c1,c'1), IsLambda (_,c2,c'2) when l1=[] & l2=[] -> 
	    evar_conv_x env isevars CONV c1 c2
	    & evar_conv_x env isevars CONV c'1 c'2

	| IsLetIn (_,b1,_,c'1), IsLetIn (_,b2,_,c'2) ->
	    let f1 () =
	      evar_conv_x env isevars CONV b1 b2
	      & evar_conv_x env isevars pbty c'1 c'2
	      & (List.length l1 = List.length l2)
	      & (List.for_all2 (evar_conv_x env isevars CONV) l1 l2)
	    and f2 () =
	      evar_eqappr_x env isevars pbty (subst1 b1 c'1,l1)
		(subst1 b2 c'2,l2)
	    in 
	    ise_try isevars [f1; f2]

	| IsLetIn (_,b1,_,c'1), _ ->(* On fait commuter les args avec le Let *)
	    evar_eqappr_x env isevars pbty (subst1 b1 c'1,l1) appr2

	| _, IsLetIn (_,b2,_,c'2) ->
	    evar_eqappr_x env isevars pbty appr1 (subst1 b2 c'2,l2)

	| IsProd (n,c1,c'1), IsProd (_,c2,c'2) when l1=[] & l2=[] -> 
            evar_conv_x env isevars CONV c1 c2
            & 
	    (let d = nf_ise1 !isevars c1 in
	     evar_conv_x (push_rel_assum (n,d) env) isevars pbty c'1 c'2)

	| IsMutInd (sp1,cl1), IsMutInd (sp2,cl2) ->
	    sp1=sp2
	    & array_for_all2 (evar_conv_x env isevars CONV) cl1 cl2
            & list_for_all2eq (evar_conv_x env isevars CONV) l1 l2
             
	| IsMutConstruct (sp1,cl1), IsMutConstruct (sp2,cl2) ->
	    sp1=sp2
            & array_for_all2 (evar_conv_x env isevars CONV) cl1 cl2
            & list_for_all2eq (evar_conv_x env isevars CONV) l1 l2

	| IsMutCase (_,p1,c1,cl1), IsMutCase (_,p2,c2,cl2) ->
	    evar_conv_x env isevars CONV p1 p2
	    & evar_conv_x env isevars CONV c1 c2
	    & (array_for_all2 (evar_conv_x env isevars CONV) cl1 cl2)
	    & (list_for_all2eq (evar_conv_x env isevars CONV) l1 l2)

	| IsFix (li1,(tys1,_,bds1)), IsFix (li2,(tys2,_,bds2)) ->
	    li1=li2
	    & (array_for_all2 (evar_conv_x env isevars CONV) tys1 tys2)
	    & (array_for_all2 (evar_conv_x env isevars CONV) bds1 bds2)
	    & (list_for_all2eq (evar_conv_x env isevars CONV) l1 l2)
	     
	| IsCoFix (i1,(tys1,_,bds1)), IsCoFix (i2,(tys2,_,bds2)) ->
	    i1=i2 
	    & (array_for_all2 (evar_conv_x env isevars CONV) tys1 tys2)
	    & (array_for_all2 (evar_conv_x env isevars CONV) bds1 bds2)
	    & (list_for_all2eq (evar_conv_x env isevars CONV) l1 l2)

	| (IsMeta _ | IsXtra _ | IsLambda _), _ -> false
	| _, (IsMeta _ | IsXtra _ | IsLambda _) -> false

	| (IsMutInd _ | IsMutConstruct _ | IsSort _ | IsProd _), _ -> false
	| _, (IsMutInd _ | IsMutConstruct _ | IsSort _ | IsProd _) -> false

	| (IsApp _ | IsMutCase _ | IsFix _ | IsCoFix _), 
	  (IsApp _ | IsMutCase _ | IsFix _ | IsCoFix _) -> false

	| (IsRel _ | IsVar _ | IsConst _ | IsEvar _), _ -> assert false
	| _, (IsRel _ | IsVar _ | IsConst _ | IsEvar _) -> assert false


and conv_record env isevars (c,bs,(xs,xs1),(us,us1),(ts,ts1),t) = 
  let ks =
    List.fold_left
      (fun ks b ->
	 (new_isevar isevars env (substl ks b) CCI)::ks)
      [] bs
  in
  if (list_for_all2eq 
	(fun u1 u -> evar_conv_x env isevars CONV u1 (substl ks u))
	us1 us)
    &
    (list_for_all2eq 
       (fun x1 x -> evar_conv_x env isevars CONV x1 (substl ks x))
       xs1 xs)
    & (list_for_all2eq (evar_conv_x env isevars CONV) ts ts1)
    & (evar_conv_x env isevars CONV t 
	 (if ks=[] then c else applist (c,(List.rev ks))))
  then
    (*TR*) (if !compter then (nbstruc:=!nbstruc+1;
                              nbimplstruc:=!nbimplstruc+(List.length ks);true)
            else true)
  else false

and check_conv_record (t1,l1) (t2,l2) = 
  try
    let {o_DEF=c;o_TABS=bs;o_TPARAMS=xs;o_TCOMPS=us} = 
      objdef_info (cte_of_constr t1,cte_of_constr t2) in
    let xs1,t,ts = 
      match list_chop (List.length xs) l1 with 
	| xs1,t::ts -> xs1,t,ts
	| _ -> assert false 
    in
    let us1,ts1 = list_chop (List.length us) l2 in
    c,bs,(xs,xs1),(us,us1),(ts,ts1),t
  with _ -> 
    raise Not_found

let the_conv_x     env isevars t1 t2 = evar_conv_x env isevars CONV     t1 t2
let the_conv_x_leq env isevars t1 t2 = evar_conv_x env isevars CONV_LEQ t1 t2
 
