(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
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
    | (Zproj (n1,m1,p1)::s1, Zproj (n2,m2,p2)::s2) ->
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
  | Zlproj of Constant.t * lift
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
| v -> CArray.Fun1.map (fun l t -> (l, t)) l v

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
	    | (Zproj (n,m,c), (l,pstk)) ->
		(l, Zlproj (c,l)::pstk)
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
      | _ -> whd_val (create_clos_infos betaiota env) (inject t)
      end
    | _ -> whd_val (create_clos_infos betaiota env) (inject t)

let nf_betaiota env t =
  norm_val (create_clos_infos betaiota env) (inject t)

let whd_betaiotazeta env x =
  match kind x with
  | (Sort _|Var _|Meta _|Evar _|Const _|Ind _|Construct _|
       Prod _|Lambda _|Fix _|CoFix _) -> x
    | App (c, _) ->
      begin match kind c with
      | Ind _ | Construct _ | Evar _ | Meta _ | Const _ -> x
      | Sort _ | Rel _ | Var _ | Cast _ | Prod _ | Lambda _ | LetIn _ | App _
        | Case _ | Fix _ | CoFix _ | Proj _ ->
         whd_val (create_clos_infos betaiotazeta env) (inject x)
      end
    | Rel _ | Cast _ | LetIn _ | Case _ | Proj _ ->
        whd_val (create_clos_infos betaiotazeta env) (inject x)

let whd_all env t =
  match kind t with
    | (Sort _|Meta _|Evar _|Ind _|Construct _|
       Prod _|Lambda _|Fix _|CoFix _) -> t
    | App (c, _) ->
      begin match kind c with
      | Ind _ | Construct _ | Evar _ | Meta _ -> t
      | Sort _ | Rel _ | Var _ | Cast _ | Prod _ | Lambda _ | LetIn _ | App _
        | Const _ |Case _ | Fix _ | CoFix _ | Proj _ ->
         whd_val (create_clos_infos all env) (inject t)
      end
    | Rel _ | Cast _ | LetIn _ | Case _ | Proj _ | Const _ | Var _ ->
        whd_val (create_clos_infos all env) (inject t)

let whd_allnolet env t =
  match kind t with
    | (Sort _|Meta _|Evar _|Ind _|Construct _|
       Prod _|Lambda _|Fix _|CoFix _|LetIn _) -> t
    | App (c, _) ->
      begin match kind c with
      | Ind _ | Construct _ | Evar _ | Meta _ | LetIn _ -> t
      | Sort _ | Rel _ | Var _ | Cast _ | Prod _ | Lambda _ | App _
        | Const _ | Case _ | Fix _ | CoFix _ | Proj _ ->
         whd_val (create_clos_infos allnolet env) (inject t)
      end
    | Rel _ | Cast _ | Case _ | Proj _ | Const _ | Var _ ->
        whd_val (create_clos_infos allnolet env) (inject t)

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
    compare : env -> conv_pb -> Sorts.t -> Sorts.t -> 'a -> 'a;
    compare_instances: flex:bool -> Univ.Instance.t -> Univ.Instance.t -> 'a -> 'a;
    conv_inductives : conv_pb -> (Declarations.mutual_inductive_body * int) -> Univ.Instance.t -> int ->
      Univ.Instance.t -> int -> 'a -> 'a;
    conv_constructors : (Declarations.mutual_inductive_body * int * int) ->
      Univ.Instance.t -> int -> Univ.Instance.t -> int -> 'a -> 'a;
  } 

type 'a universe_state = 'a * 'a universe_compare

type ('a,'b) generic_conversion_function = env -> 'b universe_state -> 'a -> 'a -> 'b

type 'a infer_conversion_function = env -> UGraph.t -> 'a -> 'a -> Univ.Constraint.t

let sort_cmp_universes env pb s0 s1 (u, check) =
  (check.compare env pb s0 s1 u, check)

(* [flex] should be true for constants, false for inductive types and
   constructors. *)
let convert_instances ~flex u u' (s, check) =
  (check.compare_instances ~flex u u' s, check)
  
let convert_inductives cv_pb ind u1 sv1 u2 sv2 (s, check) =
  (check.conv_inductives cv_pb ind u1 sv1 u2 sv2 s, check)

let convert_constructors cons u1 sv1 u2 sv2 (s, check) =
  (check.conv_constructors cons u1 sv1 u2 sv2 s, check)

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
	      if not (Constant.equal c1 c2) then 
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

let rec no_arg_available = function
  | [] -> true
  | Zupdate _ :: stk -> no_arg_available stk
  | Zshift _ :: stk -> no_arg_available stk
  | Zapp v :: stk -> Int.equal (Array.length v) 0 && no_arg_available stk
  | Zproj _ :: _ -> true
  | ZcaseT _ :: _ -> true
  | Zfix _ :: _ -> true

let rec no_nth_arg_available n = function
  | [] -> true
  | Zupdate _ :: stk -> no_nth_arg_available n stk
  | Zshift _ :: stk -> no_nth_arg_available n stk
  | Zapp v :: stk ->
      let k = Array.length v in
      if n >= k then no_nth_arg_available (n-k) stk
      else false
  | Zproj _ :: _ -> true
  | ZcaseT _ :: _ -> true
  | Zfix _ :: _ -> true

let rec no_case_available = function
  | [] -> true
  | Zupdate _ :: stk -> no_case_available stk
  | Zshift _ :: stk -> no_case_available stk
  | Zapp _ :: stk -> no_case_available stk
  | Zproj (_,_,p) :: _ -> false
  | ZcaseT _ :: _ -> false
  | Zfix _ :: _ -> true

let in_whnf (t,stk) =
  match fterm_of t with
    | (FLetIn _ | FCaseT _ | FApp _ 
	  | FCLOS _ | FLIFT _ | FCast _) -> false
    | FLambda _ -> no_arg_available stk
    | FConstruct _ -> no_case_available stk
    | FCoFix _ -> no_case_available stk
    | FFix(((ri,n),(_,_,_)),_) -> no_nth_arg_available ri.(n) stk
    | (FFlex _ | FProd _ | FEvar _ | FInd _ | FAtom _ | FRel _ | FProj _) -> true
    | FLOCKED -> assert false

let unfold_projection infos p c =
  let unf = Projection.unfolded p in
    if unf || RedFlags.red_set infos.i_flags (RedFlags.fCONST (Projection.constant p)) then
      (match try Some (lookup_projection p (info_env infos)) with Not_found -> None with
      | Some pb -> 
	let s = Zproj (pb.Declarations.proj_npars, pb.Declarations.proj_arg, 
		       Projection.constant p) in
	  Some (c, s)
      | None -> None)
  else None

(* Conversion between  [lft1]term1 and [lft2]term2 *)
let rec ccnv cv_pb l2r infos lft1 lft2 term1 term2 cuniv =
  eqappr cv_pb l2r infos (lft1, (term1,[])) (lft2, (term2,[])) cuniv

(* Conversion between [lft1](hd1 v1) and [lft2](hd2 v2) *)
and eqappr cv_pb l2r infos (lft1,st1) (lft2,st2) cuniv =
  Control.check_for_interrupt ();
  (* First head reduce both terms *)
  let whd = whd_stack (infos_with_reds infos betaiotazeta) in
  let rec whd_both (t1,stk1) (t2,stk2) =
    let st1' = whd t1 stk1 in
    let st2' = whd t2 stk2 in
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
	(match kind a1, kind a2 with
	   | (Sort s1, Sort s2) ->
	       if not (is_empty_stack v1 && is_empty_stack v2) then
		 anomaly (Pp.str "conversion was given ill-typed terms (Sort).");
	       sort_cmp_universes (env_of_infos infos) cv_pb s1 s2 cuniv
	   | (Meta n, Meta m) ->
               if Int.equal n m
               then convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
               else raise NotConvertible
	   | _ -> raise NotConvertible)
    | (FEvar ((ev1,args1),env1), FEvar ((ev2,args2),env2)) ->
        if Evar.equal ev1 ev2 then
          let cuniv = convert_stacks l2r infos lft1 lft2 v1 v2 cuniv in
          convert_vect l2r infos el1 el2
            (Array.map (mk_clos env1) args1)
            (Array.map (mk_clos env2) args2) cuniv
        else raise NotConvertible

    (* 2 index known to be bound to no constant *)
    | (FRel n, FRel m) ->
        if Int.equal (reloc_rel n el1) (reloc_rel m el2)
        then convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
        else raise NotConvertible

    (* 2 constants, 2 local defined vars or 2 defined rels *)
    | (FFlex fl1, FFlex fl2) ->
      (try
	 let cuniv = conv_table_key infos fl1 fl2 cuniv in
           convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
       with NotConvertible | Univ.UniverseInconsistency _ ->
           (* else the oracle tells which constant is to be expanded *)
	 let oracle = CClosure.oracle_of_infos infos in
         let (app1,app2) =
           if Conv_oracle.oracle_order Univ.out_punivs oracle l2r fl1 fl2 then
	     match unfold_reference infos fl1 with
             | Some def1 -> ((lft1, (def1, v1)), appr2)
             | None ->
               (match unfold_reference infos fl2 with
               | Some def2 -> (appr1, (lft2, (def2, v2)))
	       | None -> raise NotConvertible)
           else
	     match unfold_reference infos fl2 with
             | Some def2 -> (appr1, (lft2, (def2, v2)))
             | None ->
               (match unfold_reference infos fl1 with
               | Some def1 -> ((lft1, (def1, v1)), appr2)
	       | None -> raise NotConvertible) 
	 in
           eqappr cv_pb l2r infos app1 app2 cuniv)

    | (FProj (p1,c1), FProj (p2, c2)) ->
      (* Projections: prefer unfolding to first-order unification,
	 which will happen naturally if the terms c1, c2 are not in constructor
	 form *)
      (match unfold_projection infos p1 c1 with
      | Some (def1,s1) -> 
        eqappr cv_pb l2r infos (lft1, (def1, (s1 :: v1))) appr2 cuniv
      | None ->
	match unfold_projection infos p2 c2 with
	| Some (def2,s2) ->
          eqappr cv_pb l2r infos appr1 (lft2, (def2, (s2 :: v2))) cuniv
	| None -> 
          if Constant.equal (Projection.constant p1) (Projection.constant p2)
	     && compare_stack_shape v1 v2 then
            let u1 = ccnv CONV l2r infos el1 el2 c1 c2 cuniv in
              convert_stacks l2r infos lft1 lft2 v1 v2 u1
	  else (* Two projections in WHNF: unfold *)
	    raise NotConvertible)

    | (FProj (p1,c1), t2) ->
      (match unfold_projection infos p1 c1 with
      | Some (def1,s1) ->
         eqappr cv_pb l2r infos (lft1, (def1, (s1 :: v1))) appr2 cuniv
      | None -> 
	 (match t2 with 
	  | FFlex fl2 ->
	     (match unfold_reference infos fl2 with
              | Some def2 ->
                 eqappr cv_pb l2r infos appr1 (lft2, (def2, v2)) cuniv
              | None -> raise NotConvertible)
	  | _ -> raise NotConvertible))
      
    | (t1, FProj (p2,c2)) ->
      (match unfold_projection infos p2 c2 with
      | Some (def2,s2) -> 
         eqappr cv_pb l2r infos appr1 (lft2, (def2, (s2 :: v2))) cuniv
      | None -> 
	 (match t1 with 
	  | FFlex fl1 ->
	     (match unfold_reference infos fl1 with
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
        let cuniv = ccnv CONV l2r infos el1 el2 ty1 ty2 cuniv in
        ccnv CONV l2r infos (el_lift el1) (el_lift el2) bd1 bd2 cuniv

    | (FProd (_,c1,c2), FProd (_,c'1,c'2)) ->
        if not (is_empty_stack v1 && is_empty_stack v2) then
	  anomaly (Pp.str "conversion was given ill-typed terms (FProd).");
	(* Luo's system *)
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
       (match unfold_reference infos fl1 with
	| Some def1 ->
           eqappr cv_pb l2r infos (lft1, (def1, v1)) appr2 cuniv
	| None -> 
	   match c2 with
	   | FConstruct ((ind2,j2),u2) ->
	      (try
	      let v2, v1 =
		eta_expand_ind_stack (info_env infos) ind2 hd2 v2 (snd appr1)
              in convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
	      with Not_found -> raise NotConvertible)
	   | _ -> raise NotConvertible)
       
    | (c1, FFlex fl2)      ->
       (match unfold_reference infos fl2 with
        | Some def2 ->
           eqappr cv_pb l2r infos appr1 (lft2, (def2, v2)) cuniv
        | None -> 
	   match c1 with
	   | FConstruct ((ind1,j1),u1) ->
 	      (try let v1, v2 =
	     	     eta_expand_ind_stack (info_env infos) ind1 hd1 v1 (snd appr2)
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
          let mind = Environ.lookup_mind (fst ind1) (info_env infos) in
          let cuniv =
            match mind.Declarations.mind_universes with
            | Declarations.Monomorphic_ind _ | Declarations.Polymorphic_ind _ ->
              convert_instances ~flex:false u1 u2 cuniv
            | Declarations.Cumulative_ind cumi ->
              convert_inductives cv_pb (mind, snd ind1) u1 (CClosure.stack_args_size v1)
                u2 (CClosure.stack_args_size v2) cuniv
          in
          convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
      else raise NotConvertible

    | (FConstruct ((ind1,j1),u1), FConstruct ((ind2,j2),u2)) ->
      if Int.equal j1 j2 && eq_ind ind1 ind2 then
        if Univ.Instance.length u1 = 0 || Univ.Instance.length u2 = 0 then
          let cuniv = convert_instances ~flex:false u1 u2 cuniv in
          convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
        else
          let mind = Environ.lookup_mind (fst ind1) (info_env infos) in
          let cuniv =
            match mind.Declarations.mind_universes with
            | Declarations.Monomorphic_ind _ | Declarations.Polymorphic_ind _ ->
              convert_instances ~flex:false u1 u2 cuniv
            | Declarations.Cumulative_ind _ ->
              convert_constructors
                (mind, snd ind1, j1) u1 (CClosure.stack_args_size v1)
                u2 (CClosure.stack_args_size v2) cuniv
          in
          convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
      else raise NotConvertible
	  
    (* Eta expansion of records *)
    | (FConstruct ((ind1,j1),u1), _) ->
      (try
    	 let v1, v2 =
    	   eta_expand_ind_stack (info_env infos) ind1 hd1 v1 (snd appr2)
         in convert_stacks l2r infos lft1 lft2 v1 v2 cuniv
       with Not_found -> raise NotConvertible)

    | (_, FConstruct ((ind2,j2),u2)) ->
      (try
    	 let v2, v1 =
    	   eta_expand_ind_stack (info_env infos) ind2 hd2 v2 (snd appr1)
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
  ccnv cv_pb l2r infos el_id el_id (inject t1) (inject t2) univs


let check_eq univs u u' = 
  if not (UGraph.check_eq univs u u') then raise NotConvertible

let check_leq univs u u' = 
  if not (UGraph.check_leq univs u u') then raise NotConvertible

let check_sort_cmp_universes env pb s0 s1 univs =
  let open Sorts in
  match (s0,s1) with
    | (Prop c1, Prop c2) when is_cumul pb ->
      begin match c1, c2 with
      | Null, _ | _, Pos -> () (* Prop <= Set *)
      | _ -> raise NotConvertible
      end
    | (Prop c1, Prop c2) -> if c1 != c2 then raise NotConvertible
    | (Prop c1, Type u) ->
	if not (type_in_type env) then
	let u0 = univ_of_sort s0 in
	(match pb with
	| CUMUL -> check_leq univs u0 u
	| CONV -> check_eq univs u0 u)
    | (Type u, Prop c) -> raise NotConvertible
    | (Type u1, Type u2) ->
        if not (type_in_type env) then
	(match pb with
	| CUMUL -> check_leq univs u1 u2
	| CONV -> check_eq univs u1 u2)

let checked_sort_cmp_universes env pb s0 s1 univs =
  check_sort_cmp_universes env pb s0 s1 univs; univs

let check_convert_instances ~flex u u' univs =
  if UGraph.check_eq_instances univs u u' then univs
  else raise NotConvertible

(* general conversion and inference functions *)
let infer_check_conv_inductives
    infer_check_convert_instances
    infer_check_inductive_instances
    cv_pb (mind, ind) u1 sv1 u2 sv2 univs =
  match mind.Declarations.mind_universes with
  | Declarations.Monomorphic_ind _ | Declarations.Polymorphic_ind _ ->
    infer_check_convert_instances ~flex:false u1 u2 univs
  | Declarations.Cumulative_ind cumi ->
    let num_param_arity =
      mind.Declarations.mind_nparams + mind.Declarations.mind_packets.(ind).Declarations.mind_nrealargs
    in
    if not (num_param_arity = sv1 && num_param_arity = sv2) then
      infer_check_convert_instances ~flex:false u1 u2 univs
    else
      infer_check_inductive_instances cv_pb cumi u1 u2 univs

let infer_check_conv_constructors
    infer_check_convert_instances
    infer_check_inductive_instances
    (mind, ind, cns) u1 sv1 u2 sv2 univs =
  match mind.Declarations.mind_universes with
  | Declarations.Monomorphic_ind _ | Declarations.Polymorphic_ind _ ->
    infer_check_convert_instances ~flex:false u1 u2 univs
  | Declarations.Cumulative_ind cumi ->
    let num_cnstr_args =
      let nparamsctxt =
        mind.Declarations.mind_nparams + mind.Declarations.mind_packets.(ind).Declarations.mind_nrealargs
        (* Context.Rel.length mind.Declarations.mind_params_ctxt *) in
      nparamsctxt + mind.Declarations.mind_packets.(ind).Declarations.mind_consnrealargs.(cns - 1)
    in
    if not (num_cnstr_args = sv1 && num_cnstr_args = sv2) then
      infer_check_convert_instances ~flex:false u1 u2 univs
    else
      infer_check_inductive_instances CONV cumi u1 u2 univs

let check_inductive_instances cv_pb cumi u u' univs =
  let length_ind_instance = 
    Univ.AUContext.size (Univ.ACumulativityInfo.univ_context cumi)
  in
  let ind_subtypctx = Univ.ACumulativityInfo.subtyp_context cumi in
  if not ((length_ind_instance = Univ.Instance.length u) &&
          (length_ind_instance = Univ.Instance.length u')) then
     anomaly (Pp.str "Invalid inductive subtyping encountered!")
  else
    let comp_cst =
      let comp_subst = (Univ.Instance.append u u') in
      Univ.AUContext.instantiate comp_subst ind_subtypctx
    in
    let comp_cst =
      match cv_pb with
        CONV -> 
        let comp_cst' = 
          let comp_subst = (Univ.Instance.append u' u) in
          Univ.AUContext.instantiate comp_subst ind_subtypctx
        in
        Univ.Constraint.union comp_cst comp_cst'
      | CUMUL -> comp_cst
    in
    if (UGraph.check_constraints comp_cst univs) then univs
    else raise NotConvertible

let check_conv_inductives cv_pb ind u1 sv1 u2 sv2 univs =
  infer_check_conv_inductives
    check_convert_instances
    check_inductive_instances
    cv_pb ind u1 sv1 u2 sv2 univs

let check_conv_constructors cns u1 sv1 u2 sv2 univs =
  infer_check_conv_constructors
    check_convert_instances
    check_inductive_instances
    cns u1 sv1 u2 sv2 univs

let checked_universes =
  { compare = checked_sort_cmp_universes;
    compare_instances = check_convert_instances;
    conv_inductives = check_conv_inductives;
    conv_constructors = check_conv_constructors}

let infer_eq (univs, cstrs as cuniv) u u' =
  if UGraph.check_eq univs u u' then cuniv
  else
    univs, (Univ.enforce_eq u u' cstrs)

let infer_leq (univs, cstrs as cuniv) u u' =
  if UGraph.check_leq univs u u' then cuniv
  else
    let cstrs' = Univ.enforce_leq u u' cstrs in
      univs, cstrs'

let infer_cmp_universes env pb s0 s1 univs =
  let open Sorts in
  match (s0,s1) with
    | (Prop c1, Prop c2) when is_cumul pb ->
      begin match c1, c2 with
      | Null, _ | _, Pos -> univs (* Prop <= Set *)
      | _ -> raise NotConvertible
      end
    | (Prop c1, Prop c2) -> if c1 == c2 then univs else raise NotConvertible
    | (Prop c1, Type u) ->
      let u0 = univ_of_sort s0 in
	(match pb with
	| CUMUL -> infer_leq univs u0 u
	| CONV -> infer_eq univs u0 u)
    | (Type u, Prop c) -> raise NotConvertible
    | (Type u1, Type u2) ->
        if not (type_in_type env) then
	(match pb with
	| CUMUL -> infer_leq univs u1 u2
	| CONV -> infer_eq univs u1 u2)
        else univs

let infer_convert_instances ~flex u u' (univs,cstrs) =
  let cstrs' =
    if flex then 
      if UGraph.check_eq_instances univs u u' then cstrs
      else raise NotConvertible
    else Univ.enforce_eq_instances u u' cstrs
  in (univs, cstrs')

let infer_inductive_instances cv_pb cumi u u' (univs, cstrs) =
  let length_ind_instance = 
    Univ.AUContext.size (Univ.ACumulativityInfo.univ_context cumi)
  in
  let ind_subtypctx =  Univ.ACumulativityInfo.subtyp_context cumi in
  if not ((length_ind_instance = Univ.Instance.length u) &&
          (length_ind_instance = Univ.Instance.length u')) then
    anomaly (Pp.str "Invalid inductive subtyping encountered!")
  else
    let comp_cst =
      let comp_subst = (Univ.Instance.append u u') in
      Univ.AUContext.instantiate comp_subst ind_subtypctx
    in
    let comp_cst =
      match cv_pb with
        CONV -> 
        let comp_cst' = 
          let comp_subst = (Univ.Instance.append u' u) in
          Univ.AUContext.instantiate comp_subst ind_subtypctx
        in
        Univ.Constraint.union comp_cst comp_cst'
      | CUMUL -> comp_cst
    in
    (univs, Univ.Constraint.union cstrs comp_cst)


let infer_conv_inductives cv_pb ind u1 sv1 u2 sv2 univs =
  infer_check_conv_inductives
    infer_convert_instances
    infer_inductive_instances
    cv_pb ind u1 sv1 u2 sv2 univs

let infer_conv_constructors cns u1 sv1 u2 sv2 univs =
  infer_check_conv_constructors
    infer_convert_instances
    infer_inductive_instances
    cns u1 sv1 u2 sv2 univs
    
let inferred_universes : (UGraph.t * Univ.Constraint.t) universe_compare = 
  { compare = infer_cmp_universes;
    compare_instances = infer_convert_instances;
    conv_inductives = infer_conv_inductives;
    conv_constructors = infer_conv_constructors}

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
    let fconv_universes_key = Profile.declare_profile "trans_fconv_universes" in
      Profile.profile8 fconv_universes_key gen_conv cv_pb l2r reds env evars univs
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
    let infer_conv_universes_key = Profile.declare_profile "infer_conv_universes" in
      Profile.profile8 infer_conv_universes_key infer_conv_universes
  else infer_conv_universes

let infer_conv ?(l2r=false) ?(evars=fun _ -> None) ?(ts=full_transparent_state)
    env univs t1 t2 = 
  infer_conv_universes CONV l2r evars ts env univs t1 t2

let infer_conv_leq ?(l2r=false) ?(evars=fun _ -> None) ?(ts=full_transparent_state) 
    env univs t1 t2 = 
  infer_conv_universes CUMUL l2r evars ts env univs t1 t2

(* This reference avoids always having to link C code with the kernel *)
let vm_conv = ref (fun cv_pb env ->
		   gen_conv cv_pb env ~evars:((fun _->None), universes env))

let warn_bytecode_compiler_failed =
  let open Pp in
  CWarnings.create ~name:"bytecode-compiler-failed" ~category:"bytecode-compiler"
         (fun () -> strbrk "Bytecode compiler failed, " ++
                      strbrk "falling back to standard conversion")

let set_vm_conv (f:conv_pb -> types kernel_conversion_function) = vm_conv := f
let vm_conv cv_pb env t1 t2 =
  try
    !vm_conv cv_pb env t1 t2
  with Not_found | Invalid_argument _ ->
    warn_bytecode_compiler_failed ();
    gen_conv cv_pb env t1 t2

let default_conv cv_pb ?(l2r=false) env t1 t2 =
    gen_conv cv_pb env t1 t2

let default_conv_leq = default_conv CUMUL
(*
let convleqkey = Profile.declare_profile "Kernel_reduction.conv_leq";;
let conv_leq env t1 t2 =
  Profile.profile4 convleqkey conv_leq env t1 t2;;

let convkey = Profile.declare_profile "Kernel_reduction.conv";;
let conv env t1 t2 =
  Profile.profile4 convleqkey conv env t1 t2;;
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
    | Cast (c,_,_)    -> prodec_rec env l c
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
    | Cast (c,_,_)    -> lamec_rec env l c
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
