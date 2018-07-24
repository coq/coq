(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Created under Benjamin Werner account by Bruno Barras to implement
   a call-by-value conversion algorithm and a lazy reduction machine
   with sharing, Nov 1996 *)
(* Addition of zeta-reduction (let-in contraction) by Hugo Herbelin, Oct 2000 *)
(* Irreversibility of opacity by Bruno Barras *)
(* Cleaning and lightening of the kernel by Bruno Barras, Nov 2001 *)
(* Equal inductive types by Jacek Chrzaszcz as part of the module
   system, Aug 2002 *)

open CErrors
open Util
open Names
open Constr
open Vars
open Environ
open CClosure
open Esubst
open Context.Rel.Declaration

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
      ([],[]) -> Int.equal bal 0
    | ((Zupdate _|Zshift _)::s1, _) -> compare_rec bal s1 stk2
    | (_, (Zupdate _|Zshift _)::s2) -> compare_rec bal stk1 s2
    | (Zapp l1::s1, _) -> compare_rec (bal+Array.length l1) s1 stk2
    | (_, Zapp l2::s2) -> compare_rec (bal-Array.length l2) stk1 s2
    | (Zproj p1::s1, Zproj p2::s2) ->
        Int.equal bal 0 && compare_rec 0 s1 s2
    | (ZcaseT(c1,_,_,_)::s1, ZcaseT(c2,_,_,_)::s2) ->
        Int.equal bal 0 (* && c1.ci_ind  = c2.ci_ind *) && compare_rec 0 s1 s2
    | (Zfix(_,a1)::s1, Zfix(_,a2)::s2) ->
        Int.equal bal 0 && compare_rec 0 a1 a2 && compare_rec 0 s1 s2
    | [], _ :: _
    | (Zproj _ | ZcaseT _ | Zfix _) :: _, _ -> false
  in
  compare_rec 0 stk1 stk2

type lft_constr_stack_elt =
    Zlapp of (lift * fconstr) array
  | Zlproj of Projection.Repr.t * lift
  | Zlfix of (lift * fconstr) * lft_constr_stack
  | Zlcase of case_info * lift * fconstr * fconstr array
and lft_constr_stack = lft_constr_stack_elt list

let rec zlapp v = function
    Zlapp v2 :: s -> zlapp (Array.append v v2) s
  | s -> Zlapp v :: s

(** Hand-unrolling of the map function to bypass the call to the generic array
    allocation. Type annotation is required to tell OCaml that the array does
    not contain floats. *)
let map_lift (l : lift) (v : fconstr array) = match v with
| [||] -> assert false
| [|c0|] -> [|(l, c0)|]
| [|c0; c1|] -> [|(l, c0); (l, c1)|]
| [|c0; c1; c2|] -> [|(l, c0); (l, c1); (l, c2)|]
| [|c0; c1; c2; c3|] -> [|(l, c0); (l, c1); (l, c2); (l, c3)|]
| v -> Array.Fun1.map (fun l t -> (l, t)) l v

let pure_stack lfts stk =
  let rec pure_rec lfts stk =
    match stk with
        [] -> (lfts,[])
      | zi::s ->
          (match (zi,pure_rec lfts s) with
              (Zupdate _,lpstk)  -> lpstk
            | (Zshift n,(l,pstk)) -> (el_shft n l, pstk)
            | (Zapp a, (l,pstk)) ->
                (l,zlapp (map_lift l a) pstk)
            | (Zproj p, (l,pstk)) ->
                (l, Zlproj (p,l)::pstk)
            | (Zfix(fx,a),(l,pstk)) ->
                let (lfx,pa) = pure_rec l a in
                (l, Zlfix((lfx,fx),pa)::pstk)
            | (ZcaseT(ci,p,br,e),(l,pstk)) ->
                (l,Zlcase(ci,l,mk_clos e p,Array.map (mk_clos e) br)::pstk))
  in
  snd (pure_rec lfts stk)

(****************************************************************************)
(*                   Reduction Functions                                    *)
(****************************************************************************)

let whd_betaiota env t =
  match kind t with
    | (Sort _|Var _|Meta _|Evar _|Const _|Ind _|Construct _|
       Prod _|Lambda _|Fix _|CoFix _) -> t
    | App (c, _) ->
      begin match kind c with
      | Ind _ | Construct _ | Evar _ | Meta _ | Const _ | LetIn _ -> t
      | _ -> whd_val (create_clos_infos betaiota env) (create_tab ()) (inject t)
      end
    | _ -> whd_val (create_clos_infos betaiota env) (create_tab ()) (inject t)

let nf_betaiota env t =
  norm_val (create_clos_infos betaiota env) (create_tab ()) (inject t)

let whd_betaiotazeta env x =
  match kind x with
  | (Sort _|Var _|Meta _|Evar _|Const _|Ind _|Construct _|
       Prod _|Lambda _|Fix _|CoFix _) -> x
    | App (c, _) ->
      begin match kind c with
      | Ind _ | Construct _ | Evar _ | Meta _ | Const _ -> x
      | Sort _ | Rel _ | Var _ | Cast _ | Prod _ | Lambda _ | LetIn _ | App _
        | Case _ | Fix _ | CoFix _ | Proj _ ->
         whd_val (create_clos_infos betaiotazeta env) (create_tab ()) (inject x)
      end
    | Rel _ | Cast _ | LetIn _ | Case _ | Proj _ ->
        whd_val (create_clos_infos betaiotazeta env) (create_tab ()) (inject x)

let whd_all env t =
  match kind t with
    | (Sort _|Meta _|Evar _|Ind _|Construct _|
       Prod _|Lambda _|Fix _|CoFix _) -> t
    | App (c, _) ->
      begin match kind c with
      | Ind _ | Construct _ | Evar _ | Meta _ -> t
      | Sort _ | Rel _ | Var _ | Cast _ | Prod _ | Lambda _ | LetIn _ | App _
        | Const _ |Case _ | Fix _ | CoFix _ | Proj _ ->
         whd_val (create_clos_infos all env) (create_tab ()) (inject t)
      end
    | Rel _ | Cast _ | LetIn _ | Case _ | Proj _ | Const _ | Var _ ->
        whd_val (create_clos_infos all env) (create_tab ()) (inject t)

let whd_allnolet env t =
  match kind t with
    | (Sort _|Meta _|Evar _|Ind _|Construct _|
       Prod _|Lambda _|Fix _|CoFix _|LetIn _) -> t
    | App (c, _) ->
      begin match kind c with
      | Ind _ | Construct _ | Evar _ | Meta _ | LetIn _ -> t
      | Sort _ | Rel _ | Var _ | Cast _ | Prod _ | Lambda _ | App _
        | Const _ | Case _ | Fix _ | CoFix _ | Proj _ ->
         whd_val (create_clos_infos allnolet env) (create_tab ()) (inject t)
      end
    | Rel _ | Cast _ | Case _ | Proj _ | Const _ | Var _ ->
        whd_val (create_clos_infos allnolet env) (create_tab ()) (inject t)

(********************************************************************)
(*                         Conversion                               *)
(********************************************************************)

(* Conversion utility functions *)

(* functions of this type are called from the kernel *)
type 'a kernel_conversion_function = env -> 'a -> 'a -> unit

(* functions of this type can be called from outside the kernel *)
type 'a extended_conversion_function =
  ?l2r:bool -> ?reds:Names.transparent_state -> env ->
  ?evars:((existential->constr option) * UGraph.t) ->
  'a -> 'a -> unit

exception NotConvertible
exception NotConvertibleVect of int


(* Convertibility of sorts *)

(* The sort cumulativity is

    Prop <= Set <= Type 1 <= ... <= Type i <= ...

    and this holds whatever Set is predicative or impredicative
*)

type conv_pb =
  | CONV
  | CUMUL

let is_cumul = function CUMUL -> true | CONV -> false

type 'a universe_compare = 
  { (* Might raise NotConvertible *)
    compare_sorts : env -> conv_pb -> Sorts.t -> Sorts.t -> 'a -> 'a;
    compare_instances: flex:bool -> Univ.Instance.t -> Univ.Instance.t -> 'a -> 'a;
    compare_cumul_instances : conv_pb -> Univ.Variance.t array ->
      Univ.Instance.t -> Univ.Instance.t -> 'a -> 'a }

type 'a universe_state = 'a * 'a universe_compare

type ('a,'b) generic_conversion_function = env -> 'b universe_state -> 'a -> 'a -> 'b

type 'a infer_conversion_function = env -> UGraph.t -> 'a -> 'a -> Univ.Constraint.t

let sort_cmp_universes env pb s0 s1 (u, check) =
  (check.compare_sorts env pb s0 s1 u, check)

(* [flex] should be true for constants, false for inductive types and
   constructors. *)
let convert_instances ~flex u u' (s, check) =
  (check.compare_instances ~flex u u' s, check)

let get_cumulativity_constraints cv_pb variance u u' =
  match cv_pb with
  | CONV ->
    Univ.enforce_eq_variance_instances variance u u' Univ.Constraint.empty
  | CUMUL ->
    Univ.enforce_leq_variance_instances variance u u' Univ.Constraint.empty

let inductive_cumulativity_arguments (mind,ind) =
  mind.Declarations.mind_nparams +
  mind.Declarations.mind_packets.(ind).Declarations.mind_nrealargs

let convert_inductives_gen cmp_instances cmp_cumul cv_pb (mind,ind) nargs u1 u2 s =
  match mind.Declarations.mind_universes with
  | Declarations.Monomorphic_ind _ ->
    assert (Univ.Instance.length u1 = 0 && Univ.Instance.length u2 = 0);
    s
  | Declarations.Polymorphic_ind _ ->
    cmp_instances u1 u2 s
  | Declarations.Cumulative_ind cumi ->
    let num_param_arity = inductive_cumulativity_arguments (mind,ind) in
    if not (Int.equal num_param_arity nargs) then
      cmp_instances u1 u2 s
    else
      cmp_cumul cv_pb (Univ.ACumulativityInfo.variance cumi) u1 u2 s

let convert_inductives cv_pb ind nargs u1 u2 (s, check) =
  convert_inductives_gen (check.compare_instances ~flex:false) check.compare_cumul_instances
    cv_pb ind nargs u1 u2 s, check

let constructor_cumulativity_arguments (mind, ind, ctor) =
  mind.Declarations.mind_nparams +
  mind.Declarations.mind_packets.(ind).Declarations.mind_consnrealargs.(ctor - 1)

let convert_constructors_gen cmp_instances cmp_cumul (mind, ind, cns) nargs u1 u2 s =
  match mind.Declarations.mind_universes with
  | Declarations.Monomorphic_ind _ ->
    assert (Univ.Instance.length u1 = 0 && Univ.Instance.length u2 = 0);
    s
  | Declarations.Polymorphic_ind _ ->
    cmp_instances u1 u2 s
  | Declarations.Cumulative_ind cumi ->
    let num_cnstr_args = constructor_cumulativity_arguments (mind,ind,cns) in
    if not (Int.equal num_cnstr_args nargs) then
      cmp_instances u1 u2 s
    else
      (** By invariant, both constructors have a common supertype,
          so they are convertible _at that type_. *)
      let variance = Array.make (Univ.Instance.length u1) Univ.Variance.Irrelevant in
      cmp_cumul CONV variance u1 u2 s

let convert_constructors ctor nargs u1 u2 (s, check) =
  convert_constructors_gen (check.compare_instances ~flex:false) check.compare_cumul_instances
    ctor nargs u1 u2 s, check

let conv_table_key infos k1 k2 cuniv =
  if k1 == k2 then cuniv else
  match k1, k2 with
  | ConstKey (cst, u), ConstKey (cst', u') when Constant.equal cst cst' ->
    if Univ.Instance.equal u u' then cuniv
    else 
      let flex = evaluable_constant cst (info_env infos) 
	&& RedFlags.red_set (info_flags infos) (RedFlags.fCONST cst)
      in convert_instances ~flex u u' cuniv
  | VarKey id, VarKey id' when Id.equal id id' -> cuniv
  | RelKey n, RelKey n' when Int.equal n n' -> cuniv
  | _ -> raise NotConvertible

let compare_stacks f fmind lft1 stk1 lft2 stk2 cuniv =
  let rec cmp_rec pstk1 pstk2 cuniv =
    match (pstk1,pstk2) with
      | (z1::s1, z2::s2) ->
          let cu1 = cmp_rec s1 s2 cuniv in
          (match (z1,z2) with
            | (Zlapp a1,Zlapp a2) -> 
	       Array.fold_right2 f a1 a2 cu1
	    | (Zlproj (c1,l1),Zlproj (c2,l2)) -> 
              if not (Projection.Repr.equal c1 c2) then
		raise NotConvertible
	      else cu1
            | (Zlfix(fx1,a1),Zlfix(fx2,a2)) ->
                let cu2 = f fx1 fx2 cu1 in
                cmp_rec a1 a2 cu2
            | (Zlcase(ci1,l1,p1,br1),Zlcase(ci2,l2,p2,br2)) ->
                if not (fmind ci1.ci_ind ci2.ci_ind) then
		  raise NotConvertible;
		let cu2 = f (l1,p1) (l2,p2) cu1 in
                Array.fold_right2 (fun c1 c2 -> f (l1,c1) (l2,c2)) br1 br2 cu2
            | _ -> assert false)
      | _ -> cuniv in
  if compare_stack_shape stk1 stk2 then
    cmp_rec (pure_stack lft1 stk1) (pure_stack lft2 stk2) cuniv
  else raise NotConvertible

type conv_tab = {
  cnv_inf : clos_infos;
  lft_tab : fconstr infos_tab;
  rgt_tab : fconstr infos_tab;
}
(** Invariant: for any tl ∈ lft_tab and tr ∈ rgt_tab, there is no mutable memory
    location contained both in tl and in tr. *)

(** The same heap separation invariant must hold for the fconstr arguments
    passed to each respective side of the conversion function below. *)

(* Conversion between  [lft1]term1 and [lft2]term2 *)
let rec ccnv cv_pb l2r infos lft1 lft2 term1 term2 cuniv =
  eqappr cv_pb l2r infos (lft1, (term1,[])) (lft2, (term2,[])) cuniv

(* Conversion between [lft1](hd1 v1) and [lft2](hd2 v2) *)
and eqappr cv_pb l2r infos (lft1,st1) (lft2,st2) cuniv =
  Control.check_for_interrupt ();
  (* First head reduce both terms *)
  let ninfos = infos_with_reds infos.cnv_inf betaiotazeta in
  let (hd1, v1 as appr1) = whd_stack ninfos infos.lft_tab (fst st1) (snd st1) in
  let (hd2, v2 as appr2) = whd_stack ninfos infos.rgt_tab (fst st2) (snd st2) in
  let appr1 = (lft1, appr1) and appr2 = (lft2, appr2) in
  (** We delay the computation of the lifts that apply to the head of the term
      with [el_stack] inside the branches where they are actually used. *)
  match (fterm_of hd1, fterm_of hd2) with
    (* case of leaves *)
    | (FAtom a1, FAtom a2) ->
	(match kind a1, kind a2 with
	   | (Sort s1, Sort s2) ->
	       if not (is_empty_stack v1 && is_empty_stack v2) then
		 anomaly (Pp.str "conversion was given ill-typed terms (Sort).");
              sort_cmp_universes (env_of_infos infos.cnv_inf) cv_pb s1 s2 cuniv
	   | (Meta n, Meta m) ->
               if Int.equal n m
               then convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
               else raise NotConvertible
	   | _ -> raise NotConvertible)
    | (FEvar ((ev1,args1),env1), FEvar ((ev2,args2),env2)) ->
        if Evar.equal ev1 ev2 then
          let el1 = el_stack lft1 v1 in
          let el2 = el_stack lft2 v2 in
          let cuniv = convert_stacks l2r infos lft1 lft2 v1 v2 cuniv in
          convert_vect l2r infos el1 el2
            (Array.map (mk_clos env1) args1)
            (Array.map (mk_clos env2) args2) cuniv
        else raise NotConvertible

    (* 2 index known to be bound to no constant *)
    | (FRel n, FRel m) ->
        let el1 = el_stack lft1 v1 in
        let el2 = el_stack lft2 v2 in
        if Int.equal (reloc_rel n el1) (reloc_rel m el2)
        then convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
        else raise NotConvertible

    (* 2 constants, 2 local defined vars or 2 defined rels *)
    | (FFlex fl1, FFlex fl2) ->
      (try
          let cuniv = conv_table_key infos.cnv_inf fl1 fl2 cuniv in
           convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
       with NotConvertible | Univ.UniverseInconsistency _ ->
           (* else the oracle tells which constant is to be expanded *)
         let oracle = CClosure.oracle_of_infos infos.cnv_inf in
         let (app1,app2) =
           if Conv_oracle.oracle_order Univ.out_punivs oracle l2r fl1 fl2 then
             match unfold_reference infos.cnv_inf infos.lft_tab fl1 with
             | Some def1 -> ((lft1, (def1, v1)), appr2)
             | None ->
               (match unfold_reference infos.cnv_inf infos.rgt_tab fl2 with
               | Some def2 -> (appr1, (lft2, (def2, v2)))
	       | None -> raise NotConvertible)
           else
             match unfold_reference infos.cnv_inf infos.rgt_tab fl2 with
             | Some def2 -> (appr1, (lft2, (def2, v2)))
             | None ->
               (match unfold_reference infos.cnv_inf infos.lft_tab fl1 with
               | Some def1 -> ((lft1, (def1, v1)), appr2)
	       | None -> raise NotConvertible) 
	 in
           eqappr cv_pb l2r infos app1 app2 cuniv)

    | (FProj (p1,c1), FProj (p2, c2)) ->
      (* Projections: prefer unfolding to first-order unification,
	 which will happen naturally if the terms c1, c2 are not in constructor
	 form *)
      (match unfold_projection infos.cnv_inf p1 with
      | Some s1 ->
        eqappr cv_pb l2r infos (lft1, (c1, (s1 :: v1))) appr2 cuniv
      | None ->
        match unfold_projection infos.cnv_inf p2 with
        | Some s2 ->
          eqappr cv_pb l2r infos appr1 (lft2, (c2, (s2 :: v2))) cuniv
	| None -> 
          if Projection.Repr.equal (Projection.repr p1) (Projection.repr p2)
	     && compare_stack_shape v1 v2 then
            let el1 = el_stack lft1 v1 in
            let el2 = el_stack lft2 v2 in
            let u1 = ccnv CONV l2r infos el1 el2 c1 c2 cuniv in
              convert_stacks l2r infos lft1 lft2 v1 v2 u1
	  else (* Two projections in WHNF: unfold *)
	    raise NotConvertible)

    | (FProj (p1,c1), t2) ->
      (match unfold_projection infos.cnv_inf p1 with
      | Some s1 ->
         eqappr cv_pb l2r infos (lft1, (c1, (s1 :: v1))) appr2 cuniv
      | None -> 
	 (match t2 with 
	  | FFlex fl2 ->
            (match unfold_reference infos.cnv_inf infos.rgt_tab fl2 with
              | Some def2 ->
                 eqappr cv_pb l2r infos appr1 (lft2, (def2, v2)) cuniv
              | None -> raise NotConvertible)
	  | _ -> raise NotConvertible))
      
    | (t1, FProj (p2,c2)) ->
      (match unfold_projection infos.cnv_inf p2 with
      | Some s2 ->
         eqappr cv_pb l2r infos appr1 (lft2, (c2, (s2 :: v2))) cuniv
      | None -> 
	 (match t1 with 
	  | FFlex fl1 ->
            (match unfold_reference infos.cnv_inf infos.lft_tab fl1 with
              | Some def1 ->
                 eqappr cv_pb l2r infos (lft1, (def1, v1)) appr2 cuniv
              | None -> raise NotConvertible)
	  | _ -> raise NotConvertible))
      
    (* other constructors *)
    | (FLambda _, FLambda _) ->
        (* Inconsistency: we tolerate that v1, v2 contain shift and update but
           we throw them away *)
        if not (is_empty_stack v1 && is_empty_stack v2) then
	  anomaly (Pp.str "conversion was given ill-typed terms (FLambda).");
        let (_,ty1,bd1) = destFLambda mk_clos hd1 in
        let (_,ty2,bd2) = destFLambda mk_clos hd2 in
        let el1 = el_stack lft1 v1 in
        let el2 = el_stack lft2 v2 in
        let cuniv = ccnv CONV l2r infos el1 el2 ty1 ty2 cuniv in
        ccnv CONV l2r infos (el_lift el1) (el_lift el2) bd1 bd2 cuniv

    | (FProd (_,c1,c2), FProd (_,c'1,c'2)) ->
        if not (is_empty_stack v1 && is_empty_stack v2) then
	  anomaly (Pp.str "conversion was given ill-typed terms (FProd).");
	(* Luo's system *)
        let el1 = el_stack lft1 v1 in
        let el2 = el_stack lft2 v2 in
        let cuniv = ccnv CONV l2r infos el1 el2 c1 c'1 cuniv in
        ccnv cv_pb l2r infos (el_lift el1) (el_lift el2) c2 c'2 cuniv

    (* Eta-expansion on the fly *)
    | (FLambda _, _) ->
        let () = match v1 with
        | [] -> ()
        | _ ->
          anomaly (Pp.str "conversion was given unreduced term (FLambda).")
        in
        let (_,_ty1,bd1) = destFLambda mk_clos hd1 in
        eqappr CONV l2r infos
	  (el_lift lft1, (bd1, [])) (el_lift lft2, (hd2, eta_expand_stack v2)) cuniv
    | (_, FLambda _) ->
        let () = match v2 with
        | [] -> ()
        | _ ->
	  anomaly (Pp.str "conversion was given unreduced term (FLambda).")
	in
        let (_,_ty2,bd2) = destFLambda mk_clos hd2 in
        eqappr CONV l2r infos
	  (el_lift lft1, (hd1, eta_expand_stack v1)) (el_lift lft2, (bd2, [])) cuniv
	
    (* only one constant, defined var or defined rel *)
    | (FFlex fl1, c2)      ->
       (match unfold_reference infos.cnv_inf infos.lft_tab fl1 with
	| Some def1 ->
          (** By virtue of the previous case analyses, we know [c2] is rigid.
              Conversion check to rigid terms eventually implies full weak-head
              reduction, so instead of repeatedly performing small-step
              unfoldings, we perform reduction with all flags on. *)
            let all = RedFlags.red_add_transparent all (RedFlags.red_transparent (info_flags infos.cnv_inf)) in
            let r1 = whd_stack (infos_with_reds infos.cnv_inf all) infos.lft_tab def1 v1 in
            eqappr cv_pb l2r infos (lft1, r1) appr2 cuniv
	| None -> 
	   match c2 with
	   | FConstruct ((ind2,j2),u2) ->
	      (try
	      let v2, v1 =
                eta_expand_ind_stack (info_env infos.cnv_inf) ind2 hd2 v2 (snd appr1)
              in convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
	      with Not_found -> raise NotConvertible)
	   | _ -> raise NotConvertible)
       
    | (c1, FFlex fl2)      ->
       (match unfold_reference infos.cnv_inf infos.rgt_tab fl2 with
        | Some def2 ->
          (** Symmetrical case of above. *)
          let all = RedFlags.red_add_transparent all (RedFlags.red_transparent (info_flags infos.cnv_inf)) in
          let r2 = whd_stack (infos_with_reds infos.cnv_inf all) infos.rgt_tab def2 v2 in
          eqappr cv_pb l2r infos appr1 (lft2, r2) cuniv
        | None -> 
	   match c1 with
	   | FConstruct ((ind1,j1),u1) ->
 	      (try let v1, v2 =
                    eta_expand_ind_stack (info_env infos.cnv_inf) ind1 hd1 v1 (snd appr2)
                   in convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
	       with Not_found -> raise NotConvertible)
	   | _ -> raise NotConvertible)
       
    (* Inductive types:  MutInd MutConstruct Fix Cofix *)
    | (FInd (ind1,u1), FInd (ind2,u2)) ->
      if eq_ind ind1 ind2 then
        if Univ.Instance.length u1 = 0 || Univ.Instance.length u2 = 0 then
          let cuniv = convert_instances ~flex:false u1 u2 cuniv in
          convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
        else
          let mind = Environ.lookup_mind (fst ind1) (info_env infos.cnv_inf) in
          let nargs = CClosure.stack_args_size v1 in
          if not (Int.equal nargs (CClosure.stack_args_size v2))
          then raise NotConvertible
          else
            let cuniv = convert_inductives cv_pb (mind, snd ind1) nargs u1 u2 cuniv in
            convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
      else raise NotConvertible

    | (FConstruct ((ind1,j1),u1), FConstruct ((ind2,j2),u2)) ->
      if Int.equal j1 j2 && eq_ind ind1 ind2 then
        if Univ.Instance.length u1 = 0 || Univ.Instance.length u2 = 0 then
          let cuniv = convert_instances ~flex:false u1 u2 cuniv in
          convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
        else
          let mind = Environ.lookup_mind (fst ind1) (info_env infos.cnv_inf) in
          let nargs = CClosure.stack_args_size v1 in
          if not (Int.equal nargs (CClosure.stack_args_size v2))
          then raise NotConvertible
          else
            let cuniv = convert_constructors (mind, snd ind1, j1) nargs u1 u2 cuniv in
            convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
      else raise NotConvertible
	  
    (* Eta expansion of records *)
    | (FConstruct ((ind1,j1),u1), _) ->
      (try
    	 let v1, v2 =
            eta_expand_ind_stack (info_env infos.cnv_inf) ind1 hd1 v1 (snd appr2)
         in convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
       with Not_found -> raise NotConvertible)

    | (_, FConstruct ((ind2,j2),u2)) ->
      (try
    	 let v2, v1 =
            eta_expand_ind_stack (info_env infos.cnv_inf) ind2 hd2 v2 (snd appr1)
         in convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
       with Not_found -> raise NotConvertible)

    | (FFix (((op1, i1),(_,tys1,cl1)),e1), FFix(((op2, i2),(_,tys2,cl2)),e2)) ->
	if Int.equal i1 i2 && Array.equal Int.equal op1 op2
	then
	  let n = Array.length cl1 in
          let fty1 = Array.map (mk_clos e1) tys1 in
          let fty2 = Array.map (mk_clos e2) tys2 in
          let fcl1 = Array.map (mk_clos (subs_liftn n e1)) cl1 in
          let fcl2 = Array.map (mk_clos (subs_liftn n e2)) cl2 in
          let el1 = el_stack lft1 v1 in
          let el2 = el_stack lft2 v2 in
          let cuniv = convert_vect l2r infos el1 el2 fty1 fty2 cuniv in
          let cuniv =
            convert_vect l2r infos
	      (el_liftn n el1) (el_liftn n el2) fcl1 fcl2 cuniv in
          convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
        else raise NotConvertible

    | (FCoFix ((op1,(_,tys1,cl1)),e1), FCoFix((op2,(_,tys2,cl2)),e2)) ->
        if Int.equal op1 op2
        then
	  let n = Array.length cl1 in
          let fty1 = Array.map (mk_clos e1) tys1 in
          let fty2 = Array.map (mk_clos e2) tys2 in
          let fcl1 = Array.map (mk_clos (subs_liftn n e1)) cl1 in
          let fcl2 = Array.map (mk_clos (subs_liftn n e2)) cl2 in
          let el1 = el_stack lft1 v1 in
          let el2 = el_stack lft2 v2 in
          let cuniv = convert_vect l2r infos el1 el2 fty1 fty2 cuniv in
          let cuniv =
            convert_vect l2r infos
	      (el_liftn n el1) (el_liftn n el2) fcl1 fcl2 cuniv in
          convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
        else raise NotConvertible

     (* Should not happen because both (hd1,v1) and (hd2,v2) are in whnf *)
     | ( (FLetIn _, _) | (FCaseT _,_) | (FApp _,_) | (FCLOS _,_) | (FLIFT _,_)
       | (_, FLetIn _) | (_,FCaseT _) | (_,FApp _) | (_,FCLOS _) | (_,FLIFT _)
       | (FLOCKED,_) | (_,FLOCKED) ) | (FCast _, _) | (_, FCast _) -> assert false

     | (FRel _ | FAtom _ | FInd _ | FFix _ | FCoFix _
        | FProd _ | FEvar _), _ -> raise NotConvertible

and convert_stacks l2r infos lft1 lft2 stk1 stk2 cuniv =
  compare_stacks
    (fun (l1,t1) (l2,t2) cuniv -> ccnv CONV l2r infos l1 l2 t1 t2 cuniv)
    (eq_ind)
    lft1 stk1 lft2 stk2 cuniv

and convert_vect l2r infos lft1 lft2 v1 v2 cuniv =
  let lv1 = Array.length v1 in
  let lv2 = Array.length v2 in
  if Int.equal lv1 lv2
  then
    let rec fold n cuniv =
      if n >= lv1 then cuniv
      else
        let cuniv = ccnv CONV l2r infos lft1 lft2 v1.(n) v2.(n) cuniv in
        fold (n+1) cuniv in
    fold 0 cuniv
  else raise NotConvertible

let clos_gen_conv trans cv_pb l2r evars env univs t1 t2 =
  let reds = CClosure.RedFlags.red_add_transparent betaiotazeta trans in
  let infos = create_clos_infos ~evars reds env in
  let infos = {
    cnv_inf = infos;
    lft_tab = create_tab ();
    rgt_tab = create_tab ();
  } in
  ccnv cv_pb l2r infos el_id el_id (inject t1) (inject t2) univs


let check_eq univs u u' = 
  if not (UGraph.check_eq univs u u') then raise NotConvertible

let check_leq univs u u' = 
  if not (UGraph.check_leq univs u u') then raise NotConvertible

let check_sort_cmp_universes env pb s0 s1 univs =
  let open Sorts in
  if not (type_in_type env) then
    let check_pb u0 u1 =
      match pb with
      | CUMUL -> check_leq univs u0 u1
      | CONV -> check_eq univs u0 u1
    in
    match (s0,s1) with
    | Prop, Prop | Set, Set -> ()
    | Prop, (Set | Type _) -> if not (is_cumul pb) then raise NotConvertible
    | Set, Prop -> raise NotConvertible
    | Set, Type u -> check_pb Univ.type0_univ u
    | Type u, Prop -> raise NotConvertible
    | Type u, Set -> check_pb u Univ.type0_univ
    | Type u0, Type u1 -> check_pb u0 u1

let checked_sort_cmp_universes env pb s0 s1 univs =
  check_sort_cmp_universes env pb s0 s1 univs; univs

let check_convert_instances ~flex u u' univs =
  if UGraph.check_eq_instances univs u u' then univs
  else raise NotConvertible

(* general conversion and inference functions *)
let check_inductive_instances cv_pb variance u1 u2 univs =
  let csts = get_cumulativity_constraints cv_pb variance u1 u2 in
  if (UGraph.check_constraints csts univs) then univs
  else raise NotConvertible

let checked_universes =
  { compare_sorts = checked_sort_cmp_universes;
    compare_instances = check_convert_instances;
    compare_cumul_instances = check_inductive_instances; }

let infer_eq (univs, cstrs as cuniv) u u' =
  if UGraph.check_eq univs u u' then cuniv
  else
    univs, (Univ.enforce_eq u u' cstrs)

let infer_leq (univs, cstrs as cuniv) u u' =
  if UGraph.check_leq univs u u' then cuniv
  else
    let cstrs', _ = UGraph.enforce_leq_alg u u' univs in
      univs, Univ.Constraint.union cstrs cstrs'

let infer_cmp_universes env pb s0 s1 univs =
  if type_in_type env
  then univs
  else
    let open Sorts in
    let infer_pb u0 u1 =
      match pb with
      | CUMUL -> infer_leq univs u0 u1
      | CONV -> infer_eq univs u0 u1
    in
    match (s0,s1) with
    | Prop, Prop | Set, Set -> univs
    | Prop, (Set | Type _) -> if not (is_cumul pb) then raise NotConvertible else univs
    | Set, Prop -> raise NotConvertible
    | Set, Type u -> infer_pb Univ.type0_univ u
    | Type u, Prop -> raise NotConvertible
    | Type u, Set -> infer_pb u Univ.type0_univ
    | Type u0, Type u1 -> infer_pb u0 u1

let infer_convert_instances ~flex u u' (univs,cstrs) =
  let cstrs' =
    if flex then 
      if UGraph.check_eq_instances univs u u' then cstrs
      else raise NotConvertible
    else Univ.enforce_eq_instances u u' cstrs
  in (univs, cstrs')

let infer_inductive_instances cv_pb variance u1 u2 (univs,csts') =
  let csts = get_cumulativity_constraints cv_pb variance u1 u2 in
  (univs, Univ.Constraint.union csts csts')

let inferred_universes : (UGraph.t * Univ.Constraint.t) universe_compare =
  { compare_sorts = infer_cmp_universes;
    compare_instances = infer_convert_instances;
    compare_cumul_instances = infer_inductive_instances; }

let gen_conv cv_pb l2r reds env evars univs t1 t2 =
  let b = 
    if cv_pb = CUMUL then leq_constr_univs univs t1 t2 
    else eq_constr_univs univs t1 t2
  in
    if b then ()
    else 
      let _ = clos_gen_conv reds cv_pb l2r evars env (univs, checked_universes) t1 t2 in
	()

(* Profiling *)
let gen_conv cv_pb ?(l2r=false) ?(reds=full_transparent_state) env ?(evars=(fun _->None), universes env) =
  let evars, univs = evars in
  if Flags.profile then
    let fconv_universes_key = CProfile.declare_profile "trans_fconv_universes" in
      CProfile.profile8 fconv_universes_key gen_conv cv_pb l2r reds env evars univs
  else gen_conv cv_pb l2r reds env evars univs

let conv = gen_conv CONV

let conv_leq = gen_conv CUMUL

let generic_conv cv_pb ~l2r evars reds env univs t1 t2 =
  let (s, _) = 
    clos_gen_conv reds cv_pb l2r evars env univs t1 t2 
  in s

let infer_conv_universes cv_pb l2r evars reds env univs t1 t2 =
  let b, cstrs =
    if cv_pb == CUMUL then Constr.leq_constr_univs_infer univs t1 t2
    else Constr.eq_constr_univs_infer univs t1 t2
  in
    if b then cstrs
    else
      let univs = ((univs, Univ.Constraint.empty), inferred_universes) in
      let ((_,cstrs), _) = clos_gen_conv reds cv_pb l2r evars env univs t1 t2 in
	cstrs

(* Profiling *)
let infer_conv_universes = 
  if Flags.profile then 
    let infer_conv_universes_key = CProfile.declare_profile "infer_conv_universes" in
      CProfile.profile8 infer_conv_universes_key infer_conv_universes
  else infer_conv_universes

let infer_conv ?(l2r=false) ?(evars=fun _ -> None) ?(ts=full_transparent_state)
    env univs t1 t2 = 
  infer_conv_universes CONV l2r evars ts env univs t1 t2

let infer_conv_leq ?(l2r=false) ?(evars=fun _ -> None) ?(ts=full_transparent_state) 
    env univs t1 t2 = 
  infer_conv_universes CUMUL l2r evars ts env univs t1 t2

let default_conv cv_pb ?(l2r=false) env t1 t2 =
    gen_conv cv_pb env t1 t2

let default_conv_leq = default_conv CUMUL
(*
let convleqkey = CProfile.declare_profile "Kernel_reduction.conv_leq";;
let conv_leq env t1 t2 =
  CProfile.profile4 convleqkey conv_leq env t1 t2;;

let convkey = CProfile.declare_profile "Kernel_reduction.conv";;
let conv env t1 t2 =
  CProfile.profile4 convleqkey conv env t1 t2;;
*)

(* Application with on-the-fly reduction *)

let beta_applist c l =
  let rec app subst c l =
    match kind c, l with
    | Lambda(_,_,c), arg::l -> app (arg::subst) c l
    | _ -> Term.applist (substl subst c, l) in
  app [] c l

let beta_appvect c v = beta_applist c (Array.to_list v)

let beta_app c a = beta_applist c [a]

(* Compatibility *)
let betazeta_appvect = Term.lambda_appvect_assum

(********************************************************************)
(*             Special-Purpose Reduction                            *)
(********************************************************************)

(* pseudo-reduction rule:
 * [hnf_prod_app env (Prod(_,B)) N --> B[N]
 * with an HNF on the first argument to produce a product.
 * if this does not work, then we use the string S as part of our
 * error message. *)

let hnf_prod_app env t n =
  match kind (whd_all env t) with
    | Prod (_,_,b) -> subst1 n b
    | _ -> anomaly ~label:"hnf_prod_app" (Pp.str "Need a product.")

let hnf_prod_applist env t nl =
  List.fold_left (hnf_prod_app env) t nl

let hnf_prod_applist_assum env n c l =
  let rec app n subst t l =
    if Int.equal n 0 then
      if l == [] then substl subst t
      else anomaly (Pp.str "Too many arguments.")
    else match kind (whd_allnolet env t), l with
    | Prod(_,_,c), arg::l -> app (n-1) (arg::subst) c l
    | LetIn(_,b,_,c), _ -> app (n-1) (substl subst b::subst) c l
    | _, [] -> anomaly (Pp.str "Not enough arguments.")
    | _ -> anomaly (Pp.str "Not enough prod/let's.") in
  app n [] c l

(* Dealing with arities *)

let dest_prod env =
  let rec decrec env m c =
    let t = whd_all env c in
    match kind t with
      | Prod (n,a,c0) ->
	  let d = LocalAssum (n,a) in
	  decrec (push_rel d env) (Context.Rel.add d m) c0
      | _ -> m,t
  in
  decrec env Context.Rel.empty

let dest_lam env =
  let rec decrec env m c =
    let t = whd_all env c in
    match kind t with
      | Lambda (n,a,c0) ->
          let d = LocalAssum (n,a) in
          decrec (push_rel d env) (Context.Rel.add d m) c0
      | _ -> m,t
  in
  decrec env Context.Rel.empty

(* The same but preserving lets in the context, not internal ones. *)
let dest_prod_assum env =
  let rec prodec_rec env l ty =
    let rty = whd_allnolet env ty in
    match kind rty with
    | Prod (x,t,c)  ->
        let d = LocalAssum (x,t) in
	prodec_rec (push_rel d env) (Context.Rel.add d l) c
    | LetIn (x,b,t,c) ->
        let d = LocalDef (x,b,t) in
	prodec_rec (push_rel d env) (Context.Rel.add d l) c
    | _               ->
      let rty' = whd_all env rty in
	if Constr.equal rty' rty then l, rty
	else prodec_rec env l rty'
  in
  prodec_rec env Context.Rel.empty

let dest_lam_assum env =
  let rec lamec_rec env l ty =
    let rty = whd_allnolet env ty in
    match kind rty with
    | Lambda (x,t,c)  ->
        let d = LocalAssum (x,t) in
	lamec_rec (push_rel d env) (Context.Rel.add d l) c
    | LetIn (x,b,t,c) ->
        let d = LocalDef (x,b,t) in
	lamec_rec (push_rel d env) (Context.Rel.add d l) c
    | _               -> l,rty
  in
  lamec_rec env Context.Rel.empty

exception NotArity

let dest_arity env c =
  let l, c = dest_prod_assum env c in
  match kind c with
    | Sort s -> l,s
    | _ -> raise NotArity

let is_arity env c =
  try
    let _ = dest_arity env c in
    true
  with NotArity -> false

let eta_expand env t ty =
  let ctxt, codom = dest_prod env ty in
  let ctxt',t = dest_lam env t in
  let d = Context.Rel.nhyps ctxt - Context.Rel.nhyps ctxt' in
  let eta_args = List.rev_map mkRel (List.interval 1 d) in
  let t = Term.applistc (Vars.lift d t) eta_args in
  let t = Term.it_mkLambda_or_LetIn t (List.firstn d ctxt) in
  Term.it_mkLambda_or_LetIn t ctxt'
