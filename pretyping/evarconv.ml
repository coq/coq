
(* $Id$ *)

open Util
open Names
open Generic
open Term
open Reduction
open Classops
open Recordops 
open Evarutil

(* Pb: Mach cannot type evar in the general case (all Const must be applied
 * to VARs). But evars may be applied to Rels or other terms! This is the
 * difference between type_of_const and type_of_const2.
 *)
(* Fonctions temporaires pour relier la forme castée de la forme jugement *)
let tjudge_of_cast_safe sigma env var =
  match under_casts (nf_ise1 sigma) var with
   DOP2 (Cast, b, t) ->
     (match whd_betadeltaiota sigma t with
	  DOP0 (Sort s) -> {body=b; typ=s}
	| _ -> anomaly "Not a type (tjudge_of_cast)")
  | c -> Mach.execute_rec_type sigma env c
(* FIN TMP ***** *)


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

let rec evar_apprec isevars stack c =
  let (t,stack) = Reduction.apprec !isevars c stack in 
  if ise_defined isevars t
  then evar_apprec isevars stack (const_value !isevars t)
  else (t,stack)


let conversion_problems = ref ([] : (conv_pb * constr * constr) list)

let reset_problems () = conversion_problems := []

let add_conv_pb pb = (conversion_problems := pb::!conversion_problems)

let get_changed_pb lsp =
  let (pbs,pbs1) = List.fold_left
      (fun (pbs,pbs1) pb ->
    	if status_changed lsp pb then (pb::pbs,pbs1)
        else (pbs,pb::pbs1))
      ([],[])
      !conversion_problems in
  conversion_problems := pbs1;
  pbs



(* Precondition: one of the terms of the pb is an uninstanciated evar,
 * possibly applied to arguments.
 *)
let rec solve_pb isevars pb =
  match solve_simple_eqn (evar_conv_x isevars None CONV_X) isevars pb with
    Some lsp ->
      let pbs = get_changed_pb lsp in
      List.for_all
 	(fun (pbty,t1,t2) -> evar_conv_x isevars None pbty t1 t2)
 	pbs
  | None -> (add_conv_pb pb; true)

and evar_conv_x isevars b pbty term1 term2 =
  let term1 = whd_ise1 !isevars term1
  and term2 = whd_ise1 !isevars term2 in
   if eq_constr term1 term2 then true
   else if (not(has_undefined_isevars isevars term1)) &
            not(has_undefined_isevars isevars term2)
   then fconv pbty !isevars term1 term2
   else if ise_undefined isevars term1 or ise_undefined isevars term2
   then solve_pb isevars (pbty,term1,term2)
   else 
     let (t1,l1) = evar_apprec isevars [] term1
     and (t2,l2) = evar_apprec isevars [] term2 in
     if (head_is_embedded_exist isevars t1 & not(is_eliminator t2))
         or (head_is_embedded_exist isevars t2 & not(is_eliminator t1))
     then (add_conv_pb (pbty,applist(t1,l1),applist(t2,l2)); true)
     else evar_eqappr_x isevars b pbty (t1,l1) (t2,l2)

and evar_eqappr_x isevars b pbty appr1 appr2 =
  match (appr1,appr2) with
    ((DOPN(Const sp1,al1) as term1,l1), (DOPN(Const sp2,al2) as term2,l2)) ->
      let f1 () = 
      	(ise_undefined isevars term1 or ise_undefined isevars term2) &
	if List.length l1 > List.length l2 then 
          let (deb1,rest1) = chop_list (List.length l1-List.length l2) l1
          in solve_pb isevars(pbty,applist(term1,deb1),term2)
            & for_all2eq (evar_conv_x isevars b CONV_X) rest1 l2
	else
	  let (deb2,rest2) = chop_list (List.length l2-List.length l1) l2
          in solve_pb isevars(pbty,term1,applist(term2,deb2))
            & for_all2eq (evar_conv_x isevars b CONV_X) l1 rest2
      and f2 () =
         (sp1 = sp2)
       & (for_all2eq_vect (evar_conv_x isevars b CONV_X) al1 al2)  
       & (for_all2eq (evar_conv_x isevars b CONV_X) l1 l2)
      and f3 () =
	 b<>None
       & (try conv_record isevars b 
           (try check_conv_record appr1 appr2
           with Not_found -> check_conv_record appr2 appr1)
          with _ -> false)
      and f4 () =
        if evaluable_const !isevars term2 then
          evar_eqappr_x isevars b pbty
            appr1 (evar_apprec isevars l2 (const_value !isevars term2))
        else if evaluable_const !isevars term1 then
          evar_eqappr_x isevars b pbty
            (evar_apprec isevars l1 (const_value !isevars term1)) appr2
        else false
      in ise_try isevars [f1; f2; f3; f4]

  | ((DOPN(Const _,_) as term1,l1),(t2,l2)) ->  
      let f1 () =
       	ise_undefined isevars term1 &
       	(List.length l1 <= List.length l2) &
       	let (deb2,rest2) = chop_list (List.length l2-List.length l1) l2
        in solve_pb isevars(pbty,term1,applist(t2,deb2))
          & for_all2eq (evar_conv_x isevars b CONV_X) l1 rest2
      and f2 () =
	b<>None &
 	(try conv_record isevars b (check_conv_record appr1 appr2)
        with _ -> false)
      and f3 () = 
	evaluable_const !isevars term1 &
 	evar_eqappr_x isevars b pbty
          (evar_apprec isevars l1 (const_value !isevars term1)) appr2
      in ise_try isevars [f1; f2; f3]

  | ((t1,l1),(DOPN(Const _,_) as t2,l2))  -> 
      let f1 () =
       	ise_undefined isevars t2 &
       	(List.length l2 <= List.length l1) &
       	let (deb1,rest1) = chop_list (List.length l1-List.length l2) l1
        in solve_pb isevars(pbty,applist(t1,deb1),t2)
          & for_all2eq (evar_conv_x isevars b CONV_X) rest1 l2
      and f2 () = 
	b<>None &
 	(try (conv_record isevars b (check_conv_record appr2 appr1))
        with _ -> false)
      and f3 () =
        evaluable_const !isevars t2 &
 	evar_eqappr_x isevars b pbty
          appr1 (evar_apprec isevars l2 (const_value !isevars t2))
      in ise_try isevars [f1; f2; f3]

  | ((DOPN(Abst _,_) as term1,l1),(DOPN(Abst _,_) as term2,l2)) ->
      let f1 () =
        (term1=term2) &
 	(List.length(l1) = List.length(l2)) &
 	(for_all2 (evar_conv_x isevars b CONV_X) l1 l2)
      and f2 () =
        if (evaluable_abst term2)
	then evar_eqappr_x isevars b pbty
               appr1 (evar_apprec isevars l2 (abst_value term2))
	else evaluable_abst term1
            & evar_eqappr_x isevars b pbty
                (evar_apprec isevars l1 (abst_value term1)) appr2
      in ise_try isevars [f1; f2]

  | ((DOPN(Abst _,_) as term1,l1),_) ->  
        (evaluable_abst term1)
      & evar_eqappr_x isevars b pbty
          (evar_apprec isevars l1 (abst_value term1)) appr2

  | (_,(DOPN(Abst _,_) as term2,l2))  -> 
        (evaluable_abst term2)
      & evar_eqappr_x isevars b pbty
 	  appr1 (evar_apprec isevars l2 (abst_value term2))

  | ((Rel(n),l1),(Rel(m),l2)) ->
	 n=m
       & (List.length(l1) = List.length(l2))
       & (for_all2 (evar_conv_x isevars b CONV_X) l1 l2)
  | ((DOP2(Cast,c,_),l),_) -> evar_eqappr_x isevars b pbty (c,l) appr2
  | (_,(DOP2(Cast,c,_),l)) -> evar_eqappr_x isevars b pbty appr1 (c,l)
  | ((VAR id1,l1),(VAR id2,l2)) ->
	 (id1=id2 & (List.length l1 = List.length l2)
	    & (for_all2 (evar_conv_x isevars b CONV_X) l1 l2))
  | ((DOP0(Meta(n)),l1),(DOP0(Meta(m)),l2)) ->
	 (n=m & (List.length(l1) = List.length(l2))
	    & (for_all2 (evar_conv_x isevars b CONV_X) l1 l2))
  | ((DOP0(Sort s1),[]),(DOP0(Sort s2),[])) -> sort_cmp pbty s1 s2
  | ((DOP2(Lambda,c1,DLAM(_,c2)),[]), (DOP2(Lambda,c'1,DLAM(_,c'2)),[])) -> 
	  evar_conv_x isevars b CONV_X c1 c'1
	    & evar_conv_x isevars b CONV_X c2 c'2
  | ((DOP2(Prod,c1,DLAM(n,c2)),[]), (DOP2(Prod,c'1,DLAM(_,c'2)),[])) -> 
         evar_conv_x isevars b CONV_X c1 c'1 
         & evar_conv_x isevars
	    (option_app
	       (add_rel (n,tjudge_of_cast_safe !isevars (outSOME b) c1)) b)
	    pbty c2 c'2
  | ((DOPN(MutInd _ as o1,cl1) as ind1,l'1),
     (DOPN(MutInd _ as o2,cl2) as ind2,l'2)) ->
	  o1=o2
	& for_all2eq_vect (evar_conv_x isevars b CONV_X) cl1 cl2
        & for_all2eq (evar_conv_x isevars b CONV_X) l'1 l'2
         
  | ((DOPN(MutConstruct _ as o1,cl1) as constr1,l1),
     (DOPN(MutConstruct _ as o2,cl2) as constr2,l2)) ->
	  o1=o2
        & for_all2eq_vect (evar_conv_x isevars b CONV_X) cl1 cl2
        & for_all2eq (evar_conv_x isevars b CONV_X) l1 l2

  | ((DOPN(MutCase _,_) as constr1,l'1),
     (DOPN(MutCase _,_) as constr2,l'2)) ->
	  let (_,p1,c1,cl1) = destCase constr1 in
	  let (_,p2,c2,cl2) = destCase constr2 in
	    evar_conv_x isevars b CONV_X p1 p2
	  & evar_conv_x isevars b CONV_X c1 c2
	  & (for_all2eq_vect (evar_conv_x isevars b CONV_X) cl1 cl2)
	  & (for_all2eq (evar_conv_x isevars b CONV_X) l'1 l'2)

  | ((DOPN(Fix _ as o1,cl1),l1),(DOPN(Fix _ as o2,cl2),l2))   ->
	 o1=o2 & 
	 (for_all2eq_vect (evar_conv_x isevars b CONV_X) cl1 cl2) &
	 (for_all2eq (evar_conv_x isevars b CONV_X) l1 l2)

  | ((DOPN(CoFix(i1),cl1),l1),(DOPN(CoFix(i2),cl2),l2))   ->
	 i1=i2 & 
	 (for_all2eq_vect (evar_conv_x isevars b CONV_X) cl1 cl2) &
	 (for_all2eq (evar_conv_x isevars b CONV_X) l1 l2)

  | (DOP0(Implicit),[]),(DOP0(Implicit),[]) -> true
(* added to compare easily the specification of fixed points
 * But b (optional env) is not updated!
 *)
  | (DLAM(_,c1),[]),(DLAM(_,c2),[]) -> evar_conv_x isevars b pbty c1 c2
  | (DLAMV(_,vc1),[]),(DLAMV(_,vc2),[]) ->
	 for_all2eq_vect (evar_conv_x isevars b pbty) vc1 vc2
  | _ -> false


and conv_record isevars ((Some env) as b) (c,bs,(xs,xs1),(us,us1),(ts,ts1),t) = 
   let ks =
     List.fold_left
       (fun ks b ->
	 let (k,_) = new_isevar isevars env (substl ks b) CCI in (k::ks))
       [] bs
   in
     if (for_all2eq 
	   (fun u1 u -> evar_conv_x isevars b CONV_X u1 (substl ks u))
	   us1 us)
        &
        (for_all2eq 
	   (fun x1 x -> evar_conv_x isevars b CONV_X x1 (substl ks x))
	   xs1 xs)
        & (for_all2eq (evar_conv_x isevars b CONV_X) ts ts1)
	& (evar_conv_x isevars b CONV_X t 
	     (if ks=[] then c 
	      else  (DOPN(AppL,Array.of_list(c::(List.rev ks))))))
     then
 (*TR*) (if !compter then (nbstruc:=!nbstruc+1;
                          nbimplstruc:=!nbimplstruc+(List.length ks);true)
                     else true)
     else false


and check_conv_record (t1,l1) (t2,l2) = 
  try
    let {o_DEF=c;o_TABS=bs;o_TPARAMS=xs;o_TCOMPS=us} = 
      objdef_info (cte_of_constr t1,cte_of_constr t2) in
    let xs1,t::ts = chop_list (List.length xs) l1 in
    let us1,ts1= chop_list (List.length us) l2 in
    c,bs,(xs,xs1),(us,us1),(ts,ts1),t
  with _ -> raise Not_found  (* try ... with _ -> ... *)



let the_conv_x isevars env t1 t2 =
  conv_x !isevars t1 t2 or evar_conv_x isevars (Some env) CONV_X t1 t2

(* Si conv_x_leq repond true, pourquoi diable est-ce qu'on repasse une couche
 * avec evar_conv_x! Si quelqu'un comprend pourquoi, qu'il remplace ce
 * commentaire. Sinon, il va y avoir un bon coup de balai. B.B.
 *)
let the_conv_x_leq isevars env t1 t2 =
  conv_x_leq !isevars t1 t2
  or evar_conv_x isevars (Some env) CONV_X_LEQ t1 t2     
 
