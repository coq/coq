(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
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

open Util
open Names
open Native
open Term
open Univ
open Declarations
open Environ
open Closure
open Esubst

let pr_table_key k =
  match k with
  | ConstKey k -> Printf.printf "%s" (Names.string_of_label (con_label k))
  | VarKey k -> Printf.printf "%s" (Names.string_of_id k)
  | RelKey k -> Printf.printf "R_%i" k

let rec pr_fterm t = 
  match t with
  | FRel i -> Printf.printf "#%i" i
  | FAtom _ -> Printf.printf "Atom"
  | FCast _ -> Printf.printf "Cast"
  | FFlex k -> pr_table_key k
  | FInd (mind,i) -> 
      Printf.printf "%s_%i" (Names.string_of_label (mind_label mind)) i
  | FConstruct ((mind,i),j) ->
      Printf.printf "%s_%i_%i" (Names.string_of_label (mind_label mind)) i j
  | FApp(f,args) ->
      Printf.printf "(";
      pr_fconstr f;
      Array.iter (fun a -> Printf.printf " ";pr_fconstr a) args;
      Printf.printf ")";
  | FFix _ -> Printf.printf "FIX"
  | FCoFix _ -> Printf.printf "COFIX"
  | FCases _ -> Printf.printf "CASES"
  | FLambda _ -> Printf.printf "LAMBDA"
  | FProd (Anonymous,dom,codom) -> 
      pr_fconstr dom;
      Printf.printf " -> ";
      pr_fconstr codom
  | FProd (Name id,dom,codom) -> 
      Printf.printf "forall %s:" (string_of_id id);
      pr_fconstr dom;
      Printf.printf ", ";
      pr_fconstr codom
  | FLetIn _ -> Printf.printf "LETIN"
  | FEvar _ -> Printf.printf "EVAR"
  | FNativeInt _ -> Printf.printf "INT"
  | FNativeArr _ -> Printf.printf "ARRAY"
  | FLIFT (i,a) -> Printf.printf "LIFT_%i(" i; pr_fconstr a;Printf.printf ")"
  | FCLOS (c,s) -> 
      Printf.printf "CLOS(";
      Pp.msg (Clambda.pr_constr c);
      Printf.printf ", %s)"
	(if is_subs_id s then "ID" else "subst")
  | FLOCKED -> Printf.printf "LOCKED"
and pr_fconstr a = pr_fterm (fterm_of a)

let pr_stk_mem m = 
  match m with
  | Zapp args -> 
      Printf.printf "Zapp";
      Array.iter (fun a -> Printf.printf " ";pr_fconstr a) args;
  | Zcase _ -> Printf.printf "Zcase"
  | Zfix _ -> Printf.printf "Zfix"
  | Znative _ -> Printf.printf "Znative"
  | Zshift _ -> Printf.printf "Zshift"
  | Zupdate _ -> Printf.printf "Zupdate"

let pr_stk = 
  List.iter (fun e -> Printf.printf " ";pr_stk_mem e) 

let pr_state (f,stk) = 
  Printf.printf "[";
  pr_fconstr f;
  Printf.printf "|";
  pr_stk stk;
  Printf.printf "]"

let unfold_reference ((ids, csts), infos) k =
  match k with
    | VarKey id when not (Idpred.mem id ids) -> Opaque None
    | ConstKey cst when not (Cpred.mem cst csts) ->Opaque None
    | _ -> unfold_reference infos k

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
    | Znative(op1,_,rargs1, kargs1)::s1, Znative(op2,_,rargs2, kargs2)::s2 ->
	bal=0 && op1=op2 && List.length rargs1=List.length rargs1 &&
	compare_rec 0 s1 s2
    | (_,_) -> false in
  compare_rec 0 stk1 stk2

type lft_fconstr = lift * fconstr

type lft_constr_stack_elt =
    Zlapp of lft_fconstr array
  | Zlfix of lft_fconstr * lft_constr_stack
  | Zlcase of case_info * lift * fconstr * fconstr array
  | Zlnative of 
     Native.op * constant * lft_fconstr list * lft_fconstr next_native_args 

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
                (l,Zlcase(ci,l,p,br)::pstk)
	    | (Znative(op,kn,rargs,kargs),(l,pstk)) ->
		(l,Zlnative(op,kn,List.map (fun t -> (l,t)) rargs,
			    List.map (fun (k,t) -> (k,(l,t))) kargs)::pstk))
  in snd (pure_rec lfts stk)

(****************************************************************************)
(*                   Reduction Functions                                    *)
(****************************************************************************)

let whd_betaiota t =
  whd_val (create_clos_infos betaiota empty_env) (inject t)

let nf_betaiota t =
  norm_val (create_clos_infos betaiota empty_env) (inject t)

let whd_betaiotazeta x =
  match kind_of_term x with
    | (Sort _|Var _|Meta _|Evar _|Const _|Ind _|Construct _|
       Prod _|Lambda _|Fix _|CoFix _|NativeInt _|NativeArr _) -> x
    | _ -> whd_val (create_clos_infos betaiotazeta empty_env) (inject x)

let whd_betadeltaiota env t =
  match kind_of_term t with
    | (Sort _|Meta _|Evar _|Ind _|Construct _|NativeInt _|NativeArr _|
       Prod _|Lambda _|Fix _|CoFix _) -> t
    | _ -> whd_val (create_clos_infos betadeltaiota env) (inject t)

let whd_betadeltaiota_nolet env t =
  match kind_of_term t with
    | (Sort _|Meta _|Evar _|Ind _|Construct _|NativeInt _|NativeArr _|
       Prod _|Lambda _|Fix _|CoFix _|LetIn _) -> t
    | _ -> whd_val (create_clos_infos betadeltaiotanolet env) (inject t)

(* Beta *)

let beta_appvect c v =
  let rec stacklam env t stack =
    match kind_of_term t, stack with
        Lambda(_,_,c), arg::stacktl -> stacklam (arg::env) c stacktl
      | _ -> applist (substl env t, stack) in
  stacklam [] c (Array.to_list v)

let betazeta_appvect n c v =
  let rec stacklam n env t stack =
    if n = 0 then applist (substl env t, stack) else
    match kind_of_term t, stack with
        Lambda(_,_,c), arg::stacktl -> stacklam (n-1) (arg::env) c stacktl
      | LetIn(_,b,_,c), _ -> stacklam (n-1) (b::env) c stack
      | _ -> anomaly "Not enough lambda/let's" in
  stacklam n [] c (Array.to_list v)

(********************************************************************)
(*                         Conversion                               *)
(********************************************************************)

(* Conversion utility functions *)
type 'a conversion_function = env -> 'a -> 'a -> Univ.constraints
type 'a trans_conversion_function = transparent_state -> env -> 'a -> 'a -> Univ.constraints

exception NotConvertible
exception NotConvertibleVect of int

let compare_stacks f fmind lft1 stk1 lft2 stk2 cuniv =
  let rec cmp_rec pstk1 pstk2 cuniv =
    match (pstk1,pstk2) with
      | (z1::s1, z2::s2) ->
          let cu1 = cmp_rec s1 s2 cuniv in
          (match (z1,z2) with
            | (Zlapp a1,Zlapp a2) -> array_fold_right2 f a1 a2 cu1
            | (Zlfix(fx1,a1),Zlfix(fx2,a2)) ->
                let cu2 = f fx1 fx2 cu1 in
                cmp_rec a1 a2 cu2
            | (Zlcase(ci1,l1,p1,br1),Zlcase(ci2,l2,p2,br2)) ->
                if not (fmind ci1.ci_ind ci2.ci_ind) then
		  raise NotConvertible;
		let cu2 = f (l1,p1) (l2,p2) cu1 in
                array_fold_right2 (fun c1 c2 -> f (l1,c1) (l2,c2)) br1 br2 cu2
	    | (Zlnative(op1,_,rargs1,kargs1),Zlnative(op2,_,rargs2,kargs2)) ->
		let cu2 = List.fold_right2 f rargs1 rargs2 cu1 in
		let fk (_,a1) (_,a2) cu = f a1 a2 cu in
		List.fold_right2 fk kargs1 kargs2 cu2
            | _ -> assert false)
      | _ -> cuniv in
  if compare_stack_shape stk1 stk2 then
    cmp_rec (pure_stack lft1 stk1) (pure_stack lft2 stk2) cuniv
  else raise NotConvertible

(* Convertibility of sorts *)

(* The sort cumulativity is

    Prop <= Set <= Type 1 <= ... <= Type i <= ...

    and this holds whatever Set is predicative or impredicative
*)

type conv_pb =
  | CONV
  | CUMUL

let sort_cmp pb s0 s1 cuniv =
  match (s0,s1) with
    | (Prop c1, Prop c2) ->
        if c1 = Null or c2 = Pos then cuniv   (* Prop <= Set *)
        else raise NotConvertible
    | (Prop c1, Type u) when pb = CUMUL -> assert (is_univ_variable u); cuniv
    | (Type u1, Type u2) ->
	assert (is_univ_variable u2);
	(match pb with
           | CONV -> enforce_eq u1 u2 cuniv
	   | CUMUL -> enforce_geq u2 u1 cuniv)
    | (_, _) -> raise NotConvertible


let conv_sort env s0 s1 = sort_cmp CONV s0 s1 Constraint.empty

let conv_sort_leq env s0 s1 = sort_cmp CUMUL s0 s1 Constraint.empty

let rec no_arg_available = function
  | [] -> true
  | Zupdate _ :: stk -> no_arg_available stk
  | Zshift _ :: stk -> no_arg_available stk
  | Zapp v :: stk -> Array.length v = 0 && no_arg_available stk
  | Zcase _ :: _ -> true
  | Zfix _ :: _ -> true
  | Znative _ :: _ -> true

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
  | Znative _ :: _ -> true

let rec no_case_available = function
  | [] -> true
  | Zupdate _ :: stk -> no_case_available stk
  | Zshift _ :: stk -> no_case_available stk
  | Zapp _ :: stk -> no_case_available stk
  | Zcase _ :: _ -> false
  | Zfix _ :: _ -> true
  | Znative _ :: _ -> true

let rec no_native_available = function
  | [] -> true
  | Zupdate _ :: stk -> no_native_available stk
  | Zshift _ :: stk -> no_native_available stk
  | Zapp _ :: stk -> no_native_available stk
  | Zcase _ :: _ -> true
  | Zfix _ :: _ -> true
  | Znative _ :: _ -> false

let in_whnf (t,stk) =
  match fterm_of t with
    | (FLetIn _ | FCases _ | FApp _ | FCLOS _ | FLIFT _ | FCast _) -> false
    | FLambda _ -> no_arg_available stk
    | FConstruct _ -> no_case_available stk
    | FNativeInt _ | FNativeArr _ -> no_native_available stk
    | FCoFix _ -> no_case_available stk
    | FFix(((ri,n),(_,_,_)),_) -> no_nth_arg_available ri.(n) stk
    | (FFlex _ | FProd _ | FEvar _ | FInd _ | FAtom _ | FRel _) -> true
    | FLOCKED -> assert false


let rec pr_lift lft =
  match lft with
  | ELID -> Printf.printf "ID"
  | ELSHFT (lft,n) -> Printf.printf "SHFT(";pr_lift lft;Printf.printf ",%i)" n
  | ELLFT (n,lft) ->  Printf.printf "LFT(%i," n;pr_lift lft;Printf.printf ")"


      
(* Conversion between  [lft1]term1 and [lft2]term2 *)
let rec ccnv cv_pb infos lft1 lft2 term1 term2 cuniv =
  eqappr cv_pb infos (lft1, (term1,[])) (lft2, (term2,[])) cuniv

(* Conversion between [lft1](hd1 v1) and [lft2](hd2 v2) *)
and eqappr cv_pb infos (lft1,st1) (lft2,st2) cuniv =
 (* Printf.printf "eqappr: \n";
  Printf.printf "lft1 = ";pr_lift lft1;
  Printf.printf "\nlft2 = ";pr_lift lft2;Printf.printf "\n";
  pr_state st1;  Printf.printf "\n\n";
  pr_state st2;  Printf.printf "\n\n";*)
  Util.check_for_interrupt ();
  (* First head reduce both terms *)
  let rec  whd_both (t1,stk1) (t2,stk2) =
    let st1' = whd_stack (snd infos) t1 stk1 in
    let st2' = whd_stack (snd infos) t2 stk2 in
    (* Now, whd_stack on term2 might have modified st1 (due to sharing),
       and st1 might not be in whnf anymore. If so, we iterate ccnv. *)
    if in_whnf st1' then (st1',st2') else whd_both st1' st2' in
  let ((hd1,v1),(hd2,v2)) = whd_both st1 st2 in
  let appr1 = (lft1,(hd1,v1)) and appr2 = (lft2,(hd2,v2)) in
  (* compute the lifts that apply to the head of the term (hd1 and hd2) *)
  let el1 = el_stack lft1 v1 in
  let el2 = el_stack lft2 v2 in
(*  pr_state (hd1,v1);  Printf.printf "\n\n";
  pr_state (hd2,v2);  Printf.printf "\n\n\n"; *)
  match (fterm_of hd1, fterm_of hd2) with
  (* case of leaves *)
  | (FAtom a1, FAtom a2) ->
      (match kind_of_term a1, kind_of_term a2 with
      | (Sort s1, Sort s2) ->
	  assert (is_empty_stack v1 && is_empty_stack v2);
	  sort_cmp cv_pb s1 s2 cuniv
      | (Meta n, Meta m) ->
          if n=m
	  then convert_stacks infos lft1 lft2 v1 v2 cuniv
          else raise NotConvertible
      | _ -> raise NotConvertible)
  | (FEvar ((ev1,args1),env1), FEvar ((ev2,args2),env2)) ->
      if ev1=ev2 then
        let u1 = convert_stacks infos lft1 lft2 v1 v2 cuniv in
        convert_vect infos el1 el2
          (Array.map (mk_clos env1) args1)
          (Array.map (mk_clos env2) args2) u1
      else raise NotConvertible

    (* 2 index known to be bound to no constant *)
  | (FRel n, FRel m) ->
      if reloc_rel n el1 = reloc_rel m el2
      then convert_stacks infos lft1 lft2 v1 v2 cuniv
      else raise NotConvertible

    (* 2 constants, 2 local defined vars or 2 defined rels *)
  | (FFlex fl1, FFlex fl2) ->
(*       Printf.printf "Flex, Flex\n"; *)
       begin try (* try first intensional equality *)
	if eq_table_key fl1 fl2
        then convert_stacks infos lft1 lft2 v1 v2 cuniv
        else raise NotConvertible
      with NotConvertible ->
(*	Printf.printf "Oracle "; *)
         (* else the oracle tells which constant is to be expanded *)
        let (app1,app2) =
	  let aux appr1 lft1 fl1 v1 appr2 lft2 fl2 v2 =
	    begin match unfold_reference infos fl1 with
	    | Def def1 ->
(*		Printf.printf "Unfold 1\n"; *)
		((lft1, whd_stack (snd infos) def1 v1), appr2)
	    | Primitive op when check_native_args op v1 ->
		let kn = 
		  match fl1 with ConstKey kn -> kn | _ -> assert false in
		let rargs, a, nargs, v1 = get_native_args1 op kn v1 in
		((lft1, 
		  whd_stack (snd infos) a 
		    (Znative(op,kn,rargs,nargs)::v1)), appr2)
	    | _ ->
		begin match unfold_reference infos fl2 with
		| Def def2 ->
(*		    Printf.printf "Unfold 2\n"; *)
		    (appr1, (lft2, whd_stack (snd infos) def2 v2))
		| Primitive op when check_native_args op v2 -> 
		    let kn = 
		      match fl2 with ConstKey kn -> kn | _ -> assert false in
		    let rargs, a, nargs, v2 = get_native_args1 op kn v2 in
		    (appr1, (lft2, 
			     whd_stack (snd infos) a 
			       (Znative(op,kn,rargs,nargs)::v2)))
		| _ -> raise NotConvertible
		end
	    end in
          if Conv_oracle.oracle_order fl1 fl2 then
            ( (*Printf.printf "1 2\n"; *)
	    aux appr1 lft1 fl1 v1 appr2 lft2 fl2 v2 )
	  else 
	    let (app2,app1) = 
	      (*Printf.printf "2 1\n"; *)
	      aux appr2 lft2 fl2 v2 appr1 lft1 fl1 v1 in
	    (app1,app2) in
	eqappr cv_pb infos app1 app2 cuniv 
      end	
      (* only one constant, defined var or defined rel *)  
  | (FFlex fl1, _)      ->
      begin match unfold_reference infos fl1 with
      | Def def1 -> 
	  eqappr cv_pb infos 
	    (lft1, whd_stack (snd infos) def1 v1) appr2 cuniv 
      | Primitive op when check_native_args op v1 ->
	  let kn = 
	    match fl1 with ConstKey kn -> kn | _ -> assert false in
	  let rargs, a, nargs, v1 = get_native_args1 op kn v1 in
	  eqappr cv_pb infos 
	    (lft1, whd_stack (snd infos) a (Znative(op,kn,rargs,nargs)::v1))
	    appr2 cuniv
      | _ -> raise NotConvertible
      end
  | (_, FFlex fl2)      ->
(*      Printf.printf "Flex2\n"; *)
      begin match unfold_reference infos fl2 with
      | Def def2 ->
	  eqappr cv_pb infos appr1 
	    (lft2, whd_stack (snd infos) def2 v2) cuniv 
      | Primitive op when check_native_args op v2 ->
	  let kn = 
	    match fl2 with ConstKey kn -> kn | _ -> assert false in
	  let rargs, a, nargs, v2 = get_native_args1 op kn v2 in
	  eqappr cv_pb infos 
	    appr1
	    (lft2, whd_stack (snd infos) a (Znative(op,kn,rargs,nargs)::v2))
	    cuniv
      | _ -> raise NotConvertible
      end

  (* other constructors *)
  | (FLambda _, FLambda _) ->
      assert (is_empty_stack v1 && is_empty_stack v2);
      let (_,ty1,bd1) = destFLambda mk_clos hd1 in
      let (_,ty2,bd2) = destFLambda mk_clos hd2 in
      let u1 = ccnv CONV infos el1 el2 ty1 ty2 cuniv in
      ccnv CONV infos (el_lift el1) (el_lift el2) bd1 bd2 u1
	
  | (FProd (_,c1,c2), FProd (_,c'1,c'2)) ->
      assert (is_empty_stack v1 && is_empty_stack v2);
      (* Luo's system *)
      let u1 = ccnv CONV infos el1 el2 c1 c'1 cuniv in
      ccnv cv_pb infos (el_lift el1) (el_lift el2) c2 c'2 u1
	
  (* Inductive types:  MutInd MutConstruct Fix Cofix *)
	  
  | (FInd ind1, FInd ind2) ->
      if eq_ind ind1 ind2 then convert_stacks infos lft1 lft2 v1 v2 cuniv
      else raise NotConvertible
	    
  | (FConstruct (ind1,j1), FConstruct (ind2,j2)) ->
      if j1 = j2 && eq_ind ind1 ind2 then
        convert_stacks infos lft1 lft2 v1 v2 cuniv
      else raise NotConvertible
	    
  | (FFix ((op1,(_,tys1,cl1)),e1), FFix((op2,(_,tys2,cl2)),e2)) ->
      if op1 = op2 then
	let n = Array.length cl1 in
        let fty1 = Array.map (mk_clos e1) tys1 in
        let fty2 = Array.map (mk_clos e2) tys2 in
        let fcl1 = Array.map (mk_clos (subs_liftn n e1)) cl1 in
        let fcl2 = Array.map (mk_clos (subs_liftn n e2)) cl2 in
	let u1 = convert_vect infos el1 el2 fty1 fty2 cuniv in
        let u2 =
          convert_vect infos
	    (el_liftn n el1) (el_liftn n el2) fcl1 fcl2 u1 in
        convert_stacks infos lft1 lft2 v1 v2 u2
      else raise NotConvertible
	    
  | (FCoFix ((op1,(_,tys1,cl1)),e1), FCoFix((op2,(_,tys2,cl2)),e2)) ->
      if op1 = op2 then
	let n = Array.length cl1 in
        let fty1 = Array.map (mk_clos e1) tys1 in
        let fty2 = Array.map (mk_clos e2) tys2 in
        let fcl1 = Array.map (mk_clos (subs_liftn n e1)) cl1 in
        let fcl2 = Array.map (mk_clos (subs_liftn n e2)) cl2 in
        let u1 = convert_vect infos el1 el2 fty1 fty2 cuniv in
        let u2 =
	  convert_vect infos
	      (el_liftn n el1) (el_liftn n el2) fcl1 fcl2 u1 in
        convert_stacks infos lft1 lft2 v1 v2 u2
      else raise NotConvertible
	
  (* Native constructors *)    
  | FNativeInt i1, FNativeInt i2 ->
      if i1 = i2 then convert_stacks infos lft1 lft2 v1 v2 cuniv
      else raise NotConvertible
  | FNativeArr(t1, p1), FNativeArr(t2,p2) ->
      let len = Uint31.to_int (Parray.length p1) in
      if len = Uint31.to_int (Parray.length p2) then
	let u = ref (ccnv CONV infos el1 el2 t1 t2 cuniv) in
	for i = 0 to len (* default value *) do
	  let i = Uint31.of_int i in
	  u := ccnv CONV infos el1 el2 (Parray.get p1 i) (Parray.get p2 i) !u
	done;
	convert_stacks infos lft1 lft2 v1 v2 !u
      else raise NotConvertible

  (* Should not happen because both (hd1,v1) and (hd2,v2) are in whnf *)
  | ( (FLetIn _, _) | (FCases _,_) | (FApp _,_) | (FCLOS _,_) | (FLIFT _,_)
  | (_, FLetIn _) | (_,FCases _) | (_,FApp _) | (_,FCLOS _) | (_,FLIFT _)
  | (FLOCKED,_) | (_,FLOCKED) ) -> assert false

  (* In all other cases, terms are not convertible *)
  | _ -> raise NotConvertible
	  
and convert_stacks infos lft1 lft2 stk1 stk2 cuniv =
  compare_stacks
    (fun (l1,t1) (l2,t2) c -> ccnv CONV infos l1 l2 t1 t2 c)
    (eq_ind)
    lft1 stk1 lft2 stk2 cuniv

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

let clos_fconv trans cv_pb evars env t1 t2 =
  let infos = trans, create_clos_infos ~evars betaiotazeta env in
  ccnv cv_pb infos ELID ELID (inject t1) (inject t2) Constraint.empty

let trans_fconv reds cv_pb evars env t1 t2 =
  if eq_constr t1 t2 then Constraint.empty
  else 
    ((*print_string "Start conversion\n"; *)
     clos_fconv reds cv_pb evars env t1 t2)

let trans_conv_cmp conv reds = trans_fconv reds conv (fun _->None)
let trans_conv ?(evars=fun _->None) reds = trans_fconv reds CONV evars
let trans_conv_leq ?(evars=fun _->None) reds = trans_fconv reds CUMUL evars

let fconv =  trans_fconv (Idpred.full, Cpred.full)

let conv_cmp cv_pb = fconv cv_pb (fun _->None)
let conv ?(evars=fun _->None) = fconv CONV evars
let conv_leq ?(evars=fun _->None) = fconv CUMUL evars

let conv_leq_vecti ?(evars=fun _->None) env v1 v2 =
  array_fold_left2_i
    (fun i c t1 t2 ->
      let c' =
        try conv_leq ~evars env t1 t2
        with NotConvertible -> raise (NotConvertibleVect i) in
      Constraint.union c c')
    Constraint.empty
    v1
    v2

(* option for conversion *)

let vm_conv = ref (fun cv_pb -> fconv cv_pb (fun _->None))
let set_vm_conv f = vm_conv := f
let vm_conv cv_pb env t1 t2 =
  try
    !vm_conv cv_pb env t1 t2
  with Not_found | Invalid_argument _ ->
      (* If compilation fails, fall-back to closure conversion *)
      fconv cv_pb (fun _->None) env t1 t2


let default_conv = ref (fun cv_pb -> fconv cv_pb (fun _->None))

let set_default_conv f = default_conv := f

let default_conv cv_pb env t1 t2 =
  try
    !default_conv cv_pb env t1 t2
  with Not_found | Invalid_argument _ ->
      (* If compilation fails, fall-back to closure conversion *)
      fconv cv_pb (fun _->None) env t1 t2

let default_conv_leq = default_conv CUMUL
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

(* Dealing with arities *)

let dest_prod env =
  let rec decrec env m c =
    let t = whd_betadeltaiota env c in
    match kind_of_term t with
      | Prod (n,a,c0) ->
          let d = (n,None,a) in
	  decrec (push_rel d env) (add_rel_decl d m) c0
      | _ -> m,t
  in
  decrec env empty_rel_context

(* The same but preserving lets *)
let dest_prod_assum env =
  let rec prodec_rec env l ty =
    let rty = whd_betadeltaiota_nolet env ty in
    match kind_of_term rty with
    | Prod (x,t,c)  ->
        let d = (x,None,t) in
	prodec_rec (push_rel d env) (add_rel_decl d l) c
    | LetIn (x,b,t,c) ->
        let d = (x,Some b,t) in
	prodec_rec (push_rel d env) (add_rel_decl d l) c
    | Cast (c,_,_)    -> prodec_rec env l c
    | _               -> l,rty
  in
  prodec_rec env empty_rel_context

let dest_arity env c =
  let l, c = dest_prod_assum env c in
  match kind_of_term c with
    | Sort s -> l,s
    | _ -> error "not an arity"

let is_arity env c =
  try
    let _ = dest_arity env c in
    true
  with UserError _ -> false

