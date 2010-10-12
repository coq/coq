(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util
open Names
open Term
open Univ
open Closure
open Esubst
open Environ

let rec is_empty_stack = function
    [] -> true
  | Zupdate _::s -> is_empty_stack s
  | Zshift _::s -> is_empty_stack s
  | _ -> false

(* Compute the lift to be performed on a term placed in a given stack *)
let el_stack el stk =
  let n =
    List.fold_left
      (fun i z ->
        match z with
            Zshift n -> i+n
          | _ -> i)
      0
      stk in
  el_shft n el

let compare_stack_shape stk1 stk2 =
  let rec compare_rec bal stk1 stk2 =
  match (stk1,stk2) with
      ([],[]) -> bal=0
    | ((Zupdate _|Zshift _)::s1, _) -> compare_rec bal s1 stk2
    | (_, (Zupdate _|Zshift _)::s2) -> compare_rec bal stk1 s2
    | (Zapp l1::s1, _) -> compare_rec (bal+Array.length l1) s1 stk2
    | (_, Zapp l2::s2) -> compare_rec (bal-Array.length l2) stk1 s2
    | (Zcase(c1,_,_)::s1, Zcase(c2,_,_)::s2) ->
        bal=0 (* && c1.ci_ind  = c2.ci_ind *) && compare_rec 0 s1 s2
    | (Zfix(_,a1)::s1, Zfix(_,a2)::s2) ->
        bal=0 && compare_rec 0 a1 a2 && compare_rec 0 s1 s2
    | (_,_) -> false in
  compare_rec 0 stk1 stk2

type lft_constr_stack_elt =
    Zlapp of (lift * fconstr) array
  | Zlfix of (lift * fconstr) * lft_constr_stack
  | Zlcase of case_info * lift * fconstr * fconstr array
and lft_constr_stack = lft_constr_stack_elt list

let rec zlapp v = function
    Zlapp v2 :: s -> zlapp (Array.append v v2) s
  | s -> Zlapp v :: s

let pure_stack lfts stk =
  let rec pure_rec lfts stk =
    match stk with
        [] -> (lfts,[])
      | zi::s ->
          (match (zi,pure_rec lfts s) with
              (Zupdate _,lpstk)  -> lpstk
            | (Zshift n,(l,pstk)) -> (el_shft n l, pstk)
            | (Zapp a, (l,pstk)) ->
                (l,zlapp (Array.map (fun t -> (l,t)) a) pstk)
            | (Zfix(fx,a),(l,pstk)) ->
                let (lfx,pa) = pure_rec l a in
                (l, Zlfix((lfx,fx),pa)::pstk)
            | (Zcase(ci,p,br),(l,pstk)) ->
                (l,Zlcase(ci,l,p,br)::pstk)) in
  snd (pure_rec lfts stk)

(****************************************************************************)
(*                   Reduction Functions                                    *)
(****************************************************************************)

let whd_betaiotazeta x =
  match x with
    | (Sort _|Var _|Meta _|Evar _|Const _|Ind _|Construct _|
       Prod _|Lambda _|Fix _|CoFix _) -> x
    | _ -> whd_val (create_clos_infos betaiotazeta empty_env) (inject x)

let whd_betadeltaiota env t =
  match t with
    | (Sort _|Meta _|Evar _|Ind _|Construct _|
       Prod _|Lambda _|Fix _|CoFix _) -> t
    | _ -> whd_val (create_clos_infos betadeltaiota env) (inject t)

let whd_betadeltaiota_nolet env t =
  match t with
    | (Sort _|Meta _|Evar _|Ind _|Construct _|
       Prod _|Lambda _|Fix _|CoFix _|LetIn _) -> t
    | _ -> whd_val (create_clos_infos betadeltaiotanolet env) (inject t)

(* Beta *)

let beta_appvect c v =
  let rec stacklam env t stack =
    match t, stack with
        Lambda(_,_,c), arg::stacktl -> stacklam (arg::env) c stacktl
      | _ -> applist (substl env t, stack) in
  stacklam [] c (Array.to_list v)

(********************************************************************)
(*                         Conversion                               *)
(********************************************************************)

(* Conversion utility functions *)
type 'a conversion_function = env -> 'a -> 'a -> unit

exception NotConvertible
exception NotConvertibleVect of int

let compare_stacks f fmind lft1 stk1 lft2 stk2 =
  let rec cmp_rec pstk1 pstk2 =
    match (pstk1,pstk2) with
      | (z1::s1, z2::s2) ->
          cmp_rec s1 s2;
          (match (z1,z2) with
            | (Zlapp a1,Zlapp a2) -> array_iter2 f a1 a2
            | (Zlfix(fx1,a1),Zlfix(fx2,a2)) ->
                f fx1 fx2; cmp_rec a1 a2
            | (Zlcase(ci1,l1,p1,br1),Zlcase(ci2,l2,p2,br2)) ->
                if not (fmind ci1.ci_ind ci2.ci_ind) then
		  raise NotConvertible;
		f (l1,p1) (l2,p2);
                array_iter2 (fun c1 c2 -> f (l1,c1) (l2,c2)) br1 br2
            | _ -> assert false)
      | _ -> () in
  if compare_stack_shape stk1 stk2 then
    cmp_rec (pure_stack lft1 stk1) (pure_stack lft2 stk2)
  else raise NotConvertible

(* Convertibility of sorts *)

type conv_pb =
  | CONV
  | CUMUL

let sort_cmp univ pb s0 s1 =
  match (s0,s1) with
    | (Prop c1, Prop c2) when pb = CUMUL -> if c1 = Pos & c2 = Null then raise NotConvertible
    | (Prop c1, Prop c2) -> if c1 <> c2 then raise NotConvertible
    | (Prop c1, Type u)  ->
        (match pb with
            CUMUL -> ()
          | _ -> raise NotConvertible)
    | (Type u1, Type u2) ->
        if not
	  (match pb with
            | CONV -> check_eq univ u1 u2
	    | CUMUL -> check_geq univ u2 u1)
        then raise NotConvertible
    | (_, _) -> raise NotConvertible

let rec no_arg_available = function
  | [] -> true
  | Zupdate _ :: stk -> no_arg_available stk
  | Zshift _ :: stk -> no_arg_available stk
  | Zapp v :: stk -> Array.length v = 0 && no_arg_available stk
  | Zcase _ :: _ -> true
  | Zfix _ :: _ -> true

let rec no_nth_arg_available n = function
  | [] -> true
  | Zupdate _ :: stk -> no_nth_arg_available n stk
  | Zshift _ :: stk -> no_nth_arg_available n stk
  | Zapp v :: stk ->
      let k = Array.length v in
      if n >= k then no_nth_arg_available (n-k) stk
      else false
  | Zcase _ :: _ -> true
  | Zfix _ :: _ -> true

let rec no_case_available = function
  | [] -> true
  | Zupdate _ :: stk -> no_case_available stk
  | Zshift _ :: stk -> no_case_available stk
  | Zapp _ :: stk -> no_case_available stk
  | Zcase _ :: _ -> false
  | Zfix _ :: _ -> true

let in_whnf (t,stk) =
  match fterm_of t with
    | (FLetIn _ | FCases _ | FApp _ | FCLOS _ | FLIFT _ | FCast _) -> false
    | FLambda _ -> no_arg_available stk
    | FConstruct _ -> no_case_available stk
    | FCoFix _ -> no_case_available stk
    | FFix(((ri,n),(_,_,_)),_) -> no_nth_arg_available ri.(n) stk
    | (FFlex _ | FProd _ | FEvar _ | FInd _ | FAtom _ | FRel _) -> true
    | FLOCKED -> assert false

let oracle_order fl1 fl2 =
  match fl1,fl2 with
      ConstKey c1, ConstKey c2 -> (*height c1 > height c2*)false
    | _, ConstKey _ -> true
    | _ -> false

(* Conversion between  [lft1]term1 and [lft2]term2 *)
let rec ccnv univ cv_pb infos lft1 lft2 term1 term2 =
  eqappr univ cv_pb infos (lft1, (term1,[])) (lft2, (term2,[]))

(* Conversion between [lft1](hd1 v1) and [lft2](hd2 v2) *)
and eqappr univ cv_pb infos (lft1,st1) (lft2,st2) =
  Util.check_for_interrupt ();
  (* First head reduce both terms *)
  let rec  whd_both (t1,stk1) (t2,stk2) =
    let st1' = whd_stack infos t1 stk1 in
    let st2' = whd_stack infos t2 stk2 in
    (* Now, whd_stack on term2 might have modified st1 (due to sharing),
       and st1 might not be in whnf anymore. If so, we iterate ccnv. *)
    if in_whnf st1' then (st1',st2') else whd_both st1' st2' in
  let ((hd1,v1),(hd2,v2)) = whd_both st1 st2 in
  let appr1 = (lft1,(hd1,v1)) and appr2 = (lft2,(hd2,v2)) in
  (* compute the lifts that apply to the head of the term (hd1 and hd2) *)
  let el1 = el_stack lft1 v1 in
  let el2 = el_stack lft2 v2 in
  match (fterm_of hd1, fterm_of hd2) with
    (* case of leaves *)
    | (FAtom a1, FAtom a2) ->
	(match a1, a2 with
	   | (Sort s1, Sort s2) ->
	       assert (is_empty_stack v1 && is_empty_stack v2);
	       sort_cmp univ cv_pb s1 s2
	   | (Meta n, Meta m) ->
               if n=m
	       then convert_stacks univ infos lft1 lft2 v1 v2
               else raise NotConvertible
	   | _ -> raise NotConvertible)
    | (FEvar (ev1,args1), FEvar (ev2,args2)) ->
        if ev1=ev2 then
          (convert_stacks univ infos lft1 lft2 v1 v2;
           convert_vect univ infos el1 el2 args1 args2)
        else raise NotConvertible

    (* 2 index known to be bound to no constant *)
    | (FRel n, FRel m) ->
        if reloc_rel n el1 = reloc_rel m el2
        then convert_stacks univ infos lft1 lft2 v1 v2
        else raise NotConvertible

    (* 2 constants, 2 local defined vars or 2 defined rels *)
    | (FFlex fl1, FFlex fl2) ->
	(try (* try first intensional equality *)
	  if  eq_table_key fl1 fl2
          then convert_stacks univ infos lft1 lft2 v1 v2
          else raise NotConvertible
        with NotConvertible ->
          (* else the oracle tells which constant is to be expanded *)
          let (app1,app2) =
            if oracle_order fl1 fl2 then
              match unfold_reference infos fl1 with
                | Some def1 -> ((lft1, whd_stack infos def1 v1), appr2)
                | None ->
                    (match unfold_reference infos fl2 with
                      | Some def2 -> (appr1, (lft2, whd_stack infos def2 v2))
                     | None -> raise NotConvertible)
            else
	      match unfold_reference infos fl2 with
                | Some def2 -> (appr1, (lft2, whd_stack infos def2 v2))
                | None ->
                    (match unfold_reference infos fl1 with
                    | Some def1 -> ((lft1, whd_stack infos def1 v1), appr2)
		    | None -> raise NotConvertible) in
          eqappr univ cv_pb infos app1 app2)

    (* only one constant, defined var or defined rel *)
    | (FFlex fl1, _)      ->
        (match unfold_reference infos fl1 with
           | Some def1 ->
	       eqappr univ cv_pb infos (lft1, whd_stack infos def1 v1) appr2
           | None -> raise NotConvertible)
    | (_, FFlex fl2)      ->
        (match unfold_reference infos fl2 with
           | Some def2 ->
	       eqappr univ cv_pb infos appr1 (lft2, whd_stack infos def2 v2)
           | None -> raise NotConvertible)

    (* other constructors *)
    | (FLambda _, FLambda _) ->
        assert (is_empty_stack v1 && is_empty_stack v2);
        let (_,ty1,bd1) = destFLambda mk_clos hd1 in
        let (_,ty2,bd2) = destFLambda mk_clos hd2 in
        ccnv univ CONV infos el1 el2 ty1 ty2;
        ccnv univ CONV infos (el_lift el1) (el_lift el2) bd1 bd2

    | (FProd (_,c1,c2), FProd (_,c'1,c'2)) ->
        assert (is_empty_stack v1 && is_empty_stack v2);
	(* Luo's system *)
        ccnv univ CONV infos el1 el2 c1 c'1;
        ccnv univ cv_pb infos (el_lift el1) (el_lift el2) c2 c'2

    (* Inductive types:  MutInd MutConstruct Fix Cofix *)

     | (FInd ind1, FInd ind2) ->
         if mind_equiv_infos infos ind1 ind2
	 then
           convert_stacks univ infos lft1 lft2 v1 v2
         else raise NotConvertible

     | (FConstruct (ind1,j1), FConstruct (ind2,j2)) ->
	 if j1 = j2 && mind_equiv_infos infos ind1 ind2
	 then
           convert_stacks univ infos lft1 lft2 v1 v2
         else raise NotConvertible

     | (FFix ((op1,(_,tys1,cl1)),e1), FFix((op2,(_,tys2,cl2)),e2)) ->
	 if op1 = op2
	 then
	   let n = Array.length cl1 in
           let fty1 = Array.map (mk_clos e1) tys1 in
           let fty2 = Array.map (mk_clos e2) tys2 in
           let fcl1 = Array.map (mk_clos (subs_liftn n e1)) cl1 in
           let fcl2 = Array.map (mk_clos (subs_liftn n e2)) cl2 in
           convert_vect univ infos el1 el2 fty1 fty2;
           convert_vect univ infos
	     (el_liftn n el1) (el_liftn n el2) fcl1 fcl2;
           convert_stacks univ infos lft1 lft2 v1 v2
         else raise NotConvertible

     | (FCoFix ((op1,(_,tys1,cl1)),e1), FCoFix((op2,(_,tys2,cl2)),e2)) ->
         if op1 = op2
         then
	   let n = Array.length cl1 in
           let fty1 = Array.map (mk_clos e1) tys1 in
           let fty2 = Array.map (mk_clos e2) tys2 in
           let fcl1 = Array.map (mk_clos (subs_liftn n e1)) cl1 in
           let fcl2 = Array.map (mk_clos (subs_liftn n e2)) cl2 in
           convert_vect univ infos el1 el2 fty1 fty2;
	   convert_vect univ infos
	     (el_liftn n el1) (el_liftn n el2) fcl1 fcl2;
           convert_stacks univ infos lft1 lft2 v1 v2
         else raise NotConvertible

     (* Should not happen because both (hd1,v1) and (hd2,v2) are in whnf *)
     | ( (FLetIn _, _) | (FCases _,_) | (FApp _,_) | (FCLOS _,_) | (FLIFT _,_)
       | (_, FLetIn _) | (_,FCases _) | (_,FApp _) | (_,FCLOS _) | (_,FLIFT _)
       | (FLOCKED,_) | (_,FLOCKED) ) -> assert false

     (* In all other cases, terms are not convertible *)
     | _ -> raise NotConvertible

and convert_stacks univ infos lft1 lft2 stk1 stk2 =
  compare_stacks
    (fun (l1,t1) (l2,t2) -> ccnv univ CONV infos l1 l2 t1 t2)
    (mind_equiv_infos infos)
    lft1 stk1 lft2 stk2

and convert_vect univ infos lft1 lft2 v1 v2 =
  array_iter2 (fun t1 t2 -> ccnv univ CONV infos lft1 lft2 t1 t2) v1 v2

let clos_fconv cv_pb env t1 t2 =
  let infos = create_clos_infos betaiotazeta env in
  let univ = universes env in
  ccnv univ cv_pb infos ELID ELID (inject t1) (inject t2)

let fconv cv_pb env t1 t2 =
  if eq_constr t1 t2 then ()
  else clos_fconv cv_pb env t1 t2

let conv = fconv CONV
let conv_leq = fconv CUMUL

(* option for conversion : no compilation for the checker *)

let vm_conv = fconv

(********************************************************************)
(*             Special-Purpose Reduction                            *)
(********************************************************************)

(* pseudo-reduction rule:
 * [hnf_prod_app env s (Prod(_,B)) N --> B[N]
 * with an HNF on the first argument to produce a product.
 * if this does not work, then we use the string S as part of our
 * error message. *)

let hnf_prod_app env t n =
  match whd_betadeltaiota env t with
    | Prod (_,_,b) -> subst1 n b
    | _ -> anomaly "hnf_prod_app: Need a product"

let hnf_prod_applist env t nl =
  List.fold_left (hnf_prod_app env) t nl

(* Dealing with arities *)

let dest_prod env =
  let rec decrec env m c =
    let t = whd_betadeltaiota env c in
    match t with
      | Prod (n,a,c0) ->
          let d = (n,None,a) in
	  decrec (push_rel d env) (d::m) c0
      | _ -> m,t
  in
  decrec env empty_rel_context

(* The same but preserving lets *)
let dest_prod_assum env =
  let rec prodec_rec env l ty =
    let rty = whd_betadeltaiota_nolet env ty in
    match rty with
    | Prod (x,t,c)  ->
        let d = (x,None,t) in
	prodec_rec (push_rel d env) (d::l) c
    | LetIn (x,b,t,c) ->
        let d = (x,Some b,t) in
	prodec_rec (push_rel d env) (d::l) c
    | Cast (c,_,_)    -> prodec_rec env l c
    | _               -> l,rty
  in
  prodec_rec env empty_rel_context

let dest_arity env c =
  let l, c = dest_prod_assum env c in
  match c with
    | Sort s -> l,s
    | _ -> error "not an arity"

