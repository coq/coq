
(* $Id$ *)

open Util
open Names
(* open Generic *)
open Term
open Reduction
open Instantiate
open Environ
open Typing
open Classops
open Recordops 
open Evarutil

(* Pb: Mach cannot type evar in the general case (all Const must be applied
 * to Vars). But evars may be applied to Rels or other terms! This is the
 * difference between type_of_const and type_of_const2.
 *)

(* This code (i.e. try_solve_pb, solve_pb, etc.) takes a unification
 * problem, and tries to solve it. If it solves it, then it removes
 * all the conversion problems, and re-runs conversion on each one, in
 * the hopes that the new solution will aid in solving them.
 *
 * The kinds of problems it knows how to solve are those in which
 * the usable arguments of an existential var are all themselves
 * universal variables.
 * The solution to this problem is to do renaming for the Var's,
 * to make them match up with the Var's which are found in the
 * hyps of the existential, to do a "pop" for each Rel which is
 * not an argument of the existential, and a subst1 for each which
 * is, again, with the corresponding variable. This is done by
 * Tradevar.evar_define
 *
 * Thus, we take the arguments of the existential which we are about
 * to assign, and zip them with the identifiers in the hypotheses.
 * Then, we process all the Var's in the arguments, and sort the
 * Rel's into ascending order.  Then, we just march up, doing
 * subst1's and pop's.
 *
 * NOTE: We can do this more efficiently for the relative arguments,
 * by building a long substituend by hand, but this is a pain in the
 * ass.
 *)

let evar_apprec env isevars stack c =
  let rec aux s =
    let (t,stack as s') = Reduction.apprec env !isevars s in
    match kind_of_term t with
      | IsEvar (n,_ as ev) when Evd.is_defined !isevars n ->
	  aux (existential_value !isevars ev, stack)
      | _ -> (t, list_of_stack stack)
  in aux (c, append_stack (Array.of_list stack) empty_stack)


let conversion_problems = ref ([] : (conv_pb * constr * constr) list)

let reset_problems () = conversion_problems := []

let add_conv_pb pb = (conversion_problems := pb::!conversion_problems)

let get_changed_pb lev =
  let (pbs,pbs1) = 
    List.fold_left
      (fun (pbs,pbs1) pb ->
    	 if status_changed lev pb then 
	   (pb::pbs,pbs1)
         else 
	   (pbs,pb::pbs1))
      ([],[])
      !conversion_problems 
  in
  conversion_problems := pbs1;
  pbs

(* Precondition: one of the terms of the pb is an uninstanciated evar,
 * possibly applied to arguments. *)

let rec solve_pb env isevars pb =
  match solve_simple_eqn (evar_conv_x env isevars CONV) isevars pb with
    | Some lsp ->
	let pbs = get_changed_pb lsp in
	List.for_all
 	  (fun (pbty,t1,t2) -> evar_conv_x env isevars pbty t1 t2)
 	  pbs
    | None -> (add_conv_pb pb; true)

and evar_conv_x env isevars pbty term1 term2 =
  let term1 = whd_ise1 !isevars term1 in
  let term2 = whd_ise1 !isevars term2 in
  if eq_constr term1 term2 then 
    true
  else if (not(has_undefined_isevars isevars term1)) &
    not(has_undefined_isevars isevars term2) 
  then 
    is_fconv pbty env !isevars term1 term2
  else if ise_undefined isevars term1 or ise_undefined isevars term2
  then 
    solve_pb env isevars (pbty,term1,term2)
  else 
    let (t1,l1) = evar_apprec env isevars [] term1 in
    let (t2,l2) = evar_apprec env isevars [] term2 in
    if (head_is_embedded_exist isevars t1 & not(is_eliminator t2))
      or (head_is_embedded_exist isevars t2 & not(is_eliminator t1))
    then 
      (add_conv_pb (pbty,applist(t1,l1),applist(t2,l2)); true)
    else 
      evar_eqappr_x env isevars pbty (t1,l1) (t2,l2)

and evar_eqappr_x env isevars pbty (term1,l1 as appr1) (term2,l2 as appr2) =
  (* Evar must be undefined since we have whd_ised *)
  match (kind_of_term term1, kind_of_term term2) with
    | IsEvar (sp1,al1), IsEvar (sp2,al2) ->
	let f1 () =
	  if List.length l1 > List.length l2 then 
            let (deb1,rest1) = list_chop (List.length l1-List.length l2) l1 in
            solve_pb env isevars(pbty,applist(term1,deb1),term2)
            & list_for_all2eq (evar_conv_x env isevars CONV) rest1 l2
	  else
	    let (deb2,rest2) = list_chop (List.length l2-List.length l1) l2 in
	    solve_pb env isevars(pbty,term1,applist(term2,deb2))
            & list_for_all2eq (evar_conv_x env isevars CONV) l1 rest2
	and f2 () =
          (sp1 = sp2)
	  & (array_for_all2 (evar_conv_x env isevars CONV) al1 al2)  
	  & (list_for_all2eq (evar_conv_x env isevars CONV) l1 l2)
	in 
	ise_try isevars [f1; f2]

    | IsEvar (sp1,al1), IsConst cst2 ->
	let f1 () =
	  (List.length l1 <= List.length l2) &
	  let (deb2,rest2) = list_chop (List.length l2-List.length l1) l2 in
	  solve_pb env isevars(pbty,term1,applist(term2,deb2))
          & list_for_all2eq (evar_conv_x env isevars CONV) l1 rest2
	and f4 () =
	  match constant_opt_value env cst2 with
	    | Some v2 ->
		evar_eqappr_x env isevars pbty
		  appr1 (evar_apprec env isevars l2 v2)
	    | None -> false
	in 
	ise_try isevars [f1; f4]

    | IsConst cst1, IsEvar (sp2,al2) ->
	let f1 () =
       	  (List.length l2 <= List.length l1) &
       	  let (deb1,rest1) = list_chop (List.length l1-List.length l2) l1 in
	  solve_pb env isevars(pbty,applist(term1,deb1),term2)
          & list_for_all2eq (evar_conv_x env isevars CONV) rest1 l2
	and f4 () =
	  match constant_opt_value env cst1 with
	    | Some v1 ->
		evar_eqappr_x env isevars pbty
		  (evar_apprec env isevars l1 v1) appr2
	    | None -> false
	in 
	ise_try isevars [f1; f4]

    | IsConst (sp1,al1 as cst1), IsConst (sp2,al2 as cst2) ->
	let f2 () =
          (sp1 = sp2)
	  & (array_for_all2 (evar_conv_x env isevars CONV) al1 al2)  
	  & (list_for_all2eq (evar_conv_x env isevars CONV) l1 l2)
	and f3 () =
	  (try conv_record env isevars 
             (try check_conv_record appr1 appr2
	      with Not_found -> check_conv_record appr2 appr1)
           with _ -> false)
	and f4 () =
	  match constant_opt_value env cst2 with
	    | Some v2 ->
		evar_eqappr_x env isevars pbty
		  appr1 (evar_apprec env isevars l2 v2)
	    | None ->
		match constant_opt_value env cst1 with
		  | Some v1 ->
		      evar_eqappr_x env isevars pbty
			(evar_apprec env isevars l1 v1) appr2
		  | None -> false
	in 
	ise_try isevars [f2; f3; f4]

    | IsEvar (_,_), _ ->
       	(List.length l1 <= List.length l2) &
       	let (deb2,rest2) = list_chop (List.length l2-List.length l1) l2 in
	solve_pb env isevars(pbty,term1,applist(term2,deb2))
        & list_for_all2eq (evar_conv_x env isevars CONV) l1 rest2

    | _, IsEvar (_,_) ->
       	(List.length l2 <= List.length l1) &
       	let (deb1,rest1) = list_chop (List.length l1-List.length l2) l1 in
	solve_pb env isevars(pbty,applist(term1,deb1),term2)
        & list_for_all2eq (evar_conv_x env isevars CONV) rest1 l2

    | IsConst cst1, _ ->
	let f3 () =
	  (try conv_record env isevars (check_conv_record appr1 appr2)
           with _ -> false)
	and f4 () =
	  match constant_opt_value env cst1 with
	    | Some v1 ->
 		evar_eqappr_x env isevars pbty
		  (evar_apprec env isevars l1 v1) appr2
	    | None -> false
	in 
	ise_try isevars [f3; f4]
	     
    | _ , IsConst cst2 -> 
	let f3 () = 
	  (try (conv_record env isevars (check_conv_record appr2 appr1))
           with _ -> false)
	and f4 () =
	  match constant_opt_value env cst2 with
	    | Some v2 ->
 		evar_eqappr_x env isevars pbty
		  appr1 (evar_apprec env isevars l2 v2)
	    | None -> false
	in 
	ise_try isevars [f3; f4]

    | IsRel n, IsRel m ->
	n=m
	  & (List.length(l1) = List.length(l2))
	  & (List.for_all2 (evar_conv_x env isevars CONV) l1 l2)

    | IsCast (c1,_), _ -> evar_eqappr_x env isevars pbty (c1,l1) appr2

    | _, IsCast (c2,_) -> evar_eqappr_x env isevars pbty appr1 (c2,l2)

    | IsVar id1, IsVar id2 ->
	(id1=id2 & (List.length l1 = List.length l2)
	     & (List.for_all2 (evar_conv_x env isevars CONV) l1 l2))

    | IsMeta n, IsMeta m ->
	(n=m & (List.length(l1) = List.length(l2))
	   & (List.for_all2 (evar_conv_x env isevars CONV) l1 l2))

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
	  evar_eqappr_x env isevars pbty (subst1 b1 c'1,l1) (subst1 b2 c'2,l2)
	in 
	ise_try isevars [f1; f2]

    | IsLetIn (_,b1,_,c'1), _ ->  (* On fait commuter les args avec le Let *)
	evar_eqappr_x env isevars pbty (subst1 b1 c'1,l1) appr2

    | _, IsLetIn (_,b2,_,c'2) ->
	evar_eqappr_x env isevars pbty appr1 (subst1 b2 c'2,l2)

    | IsProd (n,c1,c'1), IsProd (_,c2,c'2) when l1=[] & l2=[] -> 
        evar_conv_x env isevars CONV c1 c2
        & 
	(let d = Retyping.get_assumption_of env !isevars (nf_ise1 !isevars c1)
	 in evar_conv_x (push_rel_assum (n,d) env) isevars pbty c'1 c'2)

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

    | (IsRel _ | IsVar _ | IsMeta _ | IsXtra _ | IsLambda _), _ -> false
    | _, (IsRel _ | IsVar _ | IsMeta _ | IsXtra _ | IsLambda _) -> false

    | (IsMutInd _ | IsMutConstruct _ | IsSort _ | IsProd _), _ -> false
    | _, (IsMutInd _ | IsMutConstruct _ | IsSort _ | IsProd _) -> false

    | (IsApp _ | IsMutCase _ | IsFix _ | IsCoFix _), 
      (IsApp _ | IsMutCase _ | IsFix _ | IsCoFix _) -> false



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

let the_conv_x env isevars t1 t2 =
  is_conv env !isevars t1 t2 or evar_conv_x env isevars CONV t1 t2

(* Si conv_x_leq repond true, pourquoi diable est-ce qu'on repasse une couche
 * avec evar_conv_x! Si quelqu'un comprend pourquoi, qu'il remplace ce
 * commentaire. Sinon, il va y avoir un bon coup de balai. B.B.
 *)
let the_conv_x_leq env isevars t1 t2 =
  is_conv_leq env !isevars t1 t2
  or evar_conv_x env isevars CONV_LEQ t1 t2     
 
