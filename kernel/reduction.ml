(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Util
open Names
open Term
open Univ
open Declarations
open Environ
open Closure
open Esubst

(****************************************************************************)
(*                   Reduction Functions                                    *)
(****************************************************************************)

let nf_betaiota t =
  norm_val (create_clos_infos betaiota empty_env) (inject t)

let hnf_stack env x =
  decompose_app
    (norm_val (create_clos_infos hnf_flags env) (inject x))

let whd_betadeltaiota env t = 
  whd_val (create_clos_infos betadeltaiota env) (inject t)

let whd_betadeltaiota_nolet env t = 
  whd_val (create_clos_infos betadeltaiotanolet env) (inject t)

(* Beta *)

let beta_appvect c v =
  let rec stacklam env t stack =
    match (decomp_stack stack,kind_of_term t) with
      | Some (h,stacktl), Lambda (_,_,c) -> stacklam (h::env) c stacktl
      | _ -> app_stack (substl env t, stack) in
  stacklam [] c (append_stack v empty_stack)

(* pseudo-reduction rule:
 * [hnf_prod_app env s (Prod(_,B)) N --> B[N]
 * with an HNF on the first argument to produce a product.
 * if this does not work, then we use the string S as part of our
 * error message. *)

let hnf_prod_app env t n =
  match kind_of_term (whd_betadeltaiota env t) with
    | Prod (_,_,b) -> subst1 n b
    | _ -> anomaly "hnf_prod_app: Need a product"

let hnf_prod_applist env t nl = 
  List.fold_left (hnf_prod_app env) t nl

(********************************************************************)
(*                         Conversion                               *)
(********************************************************************)

(* Conversion utility functions *)
type 'a conversion_function = env -> 'a -> 'a -> constraints

exception NotConvertible
exception NotConvertibleVect of int

(* Convertibility of sorts *)

type conv_pb = 
  | CONV 
  | CUMUL

let sort_cmp pb s0 s1 cuniv =
  match (s0,s1) with
    | (Prop c1, Prop c2) -> if c1 = c2 then cuniv else raise NotConvertible
    | (Prop c1, Type u)  ->
        (match pb with
            CUMUL -> cuniv
          | _ -> raise NotConvertible)
    | (Type u1, Type u2) ->
	(match pb with
           | CONV -> enforce_eq u1 u2 cuniv
	   | CUMUL -> enforce_geq u2 u1 cuniv)
    | (_, _) -> raise NotConvertible

(* Conversion between  [lft1]term1 and [lft2]term2 *)
let rec ccnv cv_pb infos lft1 lft2 term1 term2 cuniv = 
  eqappr cv_pb infos (lft1, fhnf infos term1) (lft2, fhnf infos term2) cuniv

(* Conversion between [lft1]([^n1]hd1 v1) and [lft2]([^n2]hd2 v2) *)
and eqappr cv_pb infos appr1 appr2 cuniv =
  let (lft1,(n1,hd1,v1)) = appr1
  and (lft2,(n2,hd2,v2)) = appr2 in
  let el1 = el_shft n1 lft1
  and el2 = el_shft n2 lft2 in
  match (fterm_of hd1, fterm_of hd2) with
    (* case of leaves *)
    | (FAtom a1, FAtom a2) ->
	(match kind_of_term a1, kind_of_term a2 with
	   | (Sort s1, Sort s2) -> 
	       if stack_args_size v1 = 0 && stack_args_size v2 = 0
	       then sort_cmp cv_pb s1 s2 cuniv
               else raise NotConvertible
	   | (Meta n, Meta m) ->
               if n=m
	       then convert_stacks infos lft1 lft2 v1 v2 cuniv
               else raise NotConvertible
	   | _ -> raise NotConvertible)
    | (FEvar (ev1,args1), FEvar (ev2,args2)) ->
        if ev1=ev2 then
          let u1 = convert_vect infos el1 el2 args1 args2 cuniv in
	  convert_stacks infos lft1 lft2 v1 v2 u1
        else raise NotConvertible

    (* 2 index known to be bound to no constant *)
    | (FRel n, FRel m) ->
        if reloc_rel n el1 = reloc_rel m el2
        then convert_stacks infos lft1 lft2 v1 v2 cuniv
        else raise NotConvertible

    (* 2 constants, 2 existentials or 2 local defined vars or 2 defined rels *)
    | (FFlex fl1, FFlex fl2) ->
	(try (* try first intensional equality *)
	  if fl1 = fl2
          then
	    convert_stacks infos lft1 lft2 v1 v2 cuniv
          else raise NotConvertible
        with NotConvertible ->
          (* else expand the second occurrence (arbitrary heuristic) *)
	  match unfold_reference infos fl2 with
            | Some def2 -> 
		eqappr cv_pb infos appr1
                  (lft2, fhnf_apply infos n2 def2 v2) cuniv
             | None ->
                 (match unfold_reference infos fl1 with
                   | Some def1 ->
                       eqappr cv_pb infos
			 (lft1, fhnf_apply infos n1 def1 v1) appr2 cuniv
		   | None -> raise NotConvertible))

    (* only one constant, existential, defined var or defined rel *)
    | (FFlex fl1, _)      ->
        (match unfold_reference infos fl1 with
           | Some def1 -> 
	       eqappr cv_pb infos (lft1, fhnf_apply infos n1 def1 v1)
                 appr2 cuniv
           | None -> raise NotConvertible)
    | (_, FFlex fl2)      ->
        (match unfold_reference infos fl2 with
           | Some def2 -> 
	       eqappr cv_pb infos appr1
                 (lft2, fhnf_apply infos n2 def2 v2)
                 cuniv
           | None -> raise NotConvertible)
	
    (* other constructors *)
    | (FLambda (_,c1,c2,_,_), FLambda (_,c'1,c'2,_,_)) ->
        if stack_args_size v1 = 0 && stack_args_size v2 = 0
        then
          let u1 = ccnv CONV infos el1 el2 c1 c'1 cuniv in
          ccnv CONV infos
            (el_lift el1) (el_lift el2) c2 c'2 u1
        else raise NotConvertible

    | (FLetIn _, _) | (_, FLetIn _) ->
        anomaly "LetIn normally removed by fhnf"

    | (FProd (_,c1,c2,_,_), FProd (_,c'1,c'2,_,_)) ->
	if stack_args_size v1 = 0 && stack_args_size v2 = 0
	then (* Luo's system *)
          let u1 = ccnv CONV infos el1 el2 c1 c'1 cuniv in
          ccnv cv_pb infos (el_lift el1) (el_lift el2) c2 c'2 u1
        else raise NotConvertible

    (* Inductive types:  MutInd MutConstruct MutCase Fix Cofix *)

      (* Les annotations du MutCase ne servent qu'à l'affichage *)

    | (FCases (_,p1,c1,cl1), FCases (_,p2,c2,cl2)) ->
        let u1 = ccnv CONV infos el1 el2 p1 p2 cuniv in
        let u2 = ccnv CONV infos el1 el2 c1 c2 u1 in
        let u3 = convert_vect infos el1 el2 cl1 cl2 u2 in
	convert_stacks infos lft1 lft2 v1 v2 u3

     | (FInd op1, FInd op2) ->
         if op1 = op2 then
           convert_stacks infos lft1 lft2 v1 v2 cuniv
         else raise NotConvertible

     | (FConstruct op1, FConstruct op2) ->
         if op1 = op2
         then
           convert_stacks infos lft1 lft2 v1 v2 cuniv
         else raise NotConvertible

     | (FFix (op1,(_,tys1,cl1),_,_), FFix(op2,(_,tys2,cl2),_,_)) ->
	 if op1 = op2
	 then
	   let u1 = convert_vect infos el1 el2 tys1 tys2 cuniv in
           let n = Array.length cl1 in
           let u2 =
             convert_vect infos 
		 (el_liftn n el1) (el_liftn n el2) cl1 cl2 u1 in
           convert_stacks infos lft1 lft2 v1 v2 u2
         else raise NotConvertible

     | (FCoFix (op1,(_,tys1,cl1),_,_), FCoFix(op2,(_,tys2,cl2),_,_)) ->
         if op1 = op2
         then
           let u1 = convert_vect infos el1 el2 tys1 tys2 cuniv in
	   let n = Array.length cl1 in
           let u2 =
	     convert_vect infos
		 (el_liftn n el1) (el_liftn n el2) cl1 cl2 u1 in
           convert_stacks infos lft1 lft2 v1 v2 u2
         else raise NotConvertible

     | _ -> raise NotConvertible

and convert_stacks infos lft1 lft2 stk1 stk2 cuniv =
  match (decomp_stack stk1, decomp_stack stk2) with
      (Some(a1,s1), Some(a2,s2)) ->
        let u1 = ccnv CONV infos lft1 lft2 a1 a2 cuniv in
        convert_stacks infos lft1 lft2 s1 s2 u1
    | (None, None) -> cuniv
    | _ -> raise NotConvertible

and convert_vect infos lft1 lft2 v1 v2 cuniv =
  let lv1 = Array.length v1 in
  let lv2 = Array.length v2 in
  if lv1 = lv2
  then 
    let rec fold n univ = 
      if n >= lv1 then univ
      else
        let u1 = ccnv CONV infos lft1 lft2 v1.(n) v2.(n) univ in
        fold (n+1) u1 in
    fold 0 cuniv
  else raise NotConvertible



let fconv cv_pb env t1 t2 =
  if eq_constr t1 t2 then 
    Constraint.empty
  else
    let infos = create_clos_infos hnf_flags env in
    ccnv cv_pb infos ELID ELID (inject t1) (inject t2)
      Constraint.empty

let conv env = fconv CONV env
let conv_leq env = fconv CUMUL env

let conv_leq_vecti env v1 v2 =
  array_fold_left2_i 
    (fun i c t1 t2 ->
      let c' =
        try conv_leq env t1 t2 
        with NotConvertible -> raise (NotConvertibleVect i) in
      Constraint.union c c')
    Constraint.empty
    v1
    v2

(*
let convleqkey = Profile.declare_profile "Kernel_reduction.conv_leq";;
let conv_leq env t1 t2 =
  Profile.profile4 convleqkey conv_leq env t1 t2;;

let convkey = Profile.declare_profile "Kernel_reduction.conv";;
let conv env t1 t2 =
  Profile.profile4 convleqkey conv env t1 t2;;
*)

(********************************************************************)
(*             Special-Purpose Reduction                            *)
(********************************************************************)

(* Dealing with arities *)

let dest_prod env = 
  let rec decrec env m c =
    let t = whd_betadeltaiota env c in
    match kind_of_term t with
      | Prod (n,a,c0) ->
          let d = (n,None,a) in
	  decrec (push_rel d env) (Sign.add_rel_decl d m) c0
      | _ -> m,t
  in 
  decrec env []

(* The same but preserving lets *)
let dest_prod_assum env = 
  let rec prodec_rec env l ty =
    let rty = whd_betadeltaiota_nolet env ty in
    match kind_of_term rty with
    | Prod (x,t,c)  ->
        let d = (x,None,t) in
	prodec_rec (push_rel d env) (Sign.add_rel_decl d l) c
    | LetIn (x,b,t,c) ->
        let d = (x,Some b,t) in
	prodec_rec (push_rel d env) (Sign.add_rel_decl d l) c
    | Cast (c,_)    -> prodec_rec env l c
    | _               -> l,rty
  in
  prodec_rec env Sign.empty_rel_context

let dest_arity env c =
  let l, c = dest_prod env c in
  match kind_of_term c with
    | Sort s -> l,s
    | _ -> error "not an arity"

let is_arity env c =
  try
    let _ = dest_arity env c in
    true
  with UserError _ -> false

