(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Pp
open Util
open Names
open Term
open Univ
open Evd
open Declarations
open Environ
open Instantiate
open Closure
open Esubst

exception Elimconst

(* The type of (machine) states (= lambda-bar-calculus' cuts) *) 
type state = constr * constr stack

type 'a contextual_reduction_function = env -> 'a evar_map -> constr -> constr
type 'a reduction_function = 'a contextual_reduction_function
type local_reduction_function = constr -> constr

type 'a contextual_stack_reduction_function = 
    env -> 'a evar_map -> constr -> constr * constr list
type 'a stack_reduction_function = 'a contextual_stack_reduction_function
type local_stack_reduction_function = constr -> constr * constr list

type 'a contextual_state_reduction_function = 
    env -> 'a evar_map -> state -> state
type 'a state_reduction_function = 'a contextual_state_reduction_function
type local_state_reduction_function = state -> state

(*************************************)
(*** Reduction Functions Operators ***)
(*************************************)

let rec whd_state (x, stack as s) =
  match kind_of_term x with
    | IsApp (f,cl) -> whd_state (f, append_stack cl stack)
    | IsCast (c,_)  -> whd_state (c, stack)
    | _             -> s

let appterm_of_stack (f,s) = (f,list_of_stack s)

let whd_stack x = appterm_of_stack (whd_state (x, empty_stack))
let whd_castapp_stack = whd_stack

let stack_reduction_of_reduction red_fun env sigma s =
  let t = red_fun env sigma (app_stack s) in
  whd_stack t

let strong whdfun env sigma t = 
  let rec strongrec env t =
    map_constr_with_full_binders push_rel strongrec env (whdfun env sigma t) in
  strongrec env t

let local_strong whdfun = 
  let rec strongrec t = map_constr strongrec (whdfun t) in
  strongrec

let rec strong_prodspine redfun c = 
  let x = redfun c in
  match kind_of_term x with
    | IsProd (na,a,b) -> mkProd (na,a,strong_prodspine redfun b)
    | _ -> x

(****************************************************************************)
(*                   Reduction Functions                                    *)
(****************************************************************************)

(* lazy reduction functions. The infos must be created for each term *)
let clos_norm_flags flgs env sigma t =
  norm_val (create_clos_infos flgs env sigma) (inject t)

let nf_beta = clos_norm_flags beta empty_env Evd.empty
let nf_betaiota = clos_norm_flags betaiota empty_env Evd.empty
let nf_betadeltaiota env sigma =  clos_norm_flags betadeltaiota env sigma

(* lazy weak head reduction functions *)
let whd_flags flgs env sigma t =
  whd_val (create_clos_infos flgs env sigma) (inject t)

(*************************************)
(*** Reduction using substitutions ***)
(*************************************)

(* This signature is very similar to Closure.RedFlagsSig except there
   is eta but no per-constant unfolding *)

module type RedFlagsSig = sig
  type flags
  type flag
  val fbeta : flag
  val fevar : flag
  val fdelta : flag
  val feta : flag
  val fiota : flag
  val fzeta : flag
  val mkflags : flag list -> flags
  val red_beta : flags -> bool
  val red_delta : flags -> bool
  val red_evar : flags -> bool
  val red_eta : flags -> bool
  val red_iota : flags -> bool
  val red_zeta : flags -> bool
end

(* Naive Implementation 
module RedFlags = (struct
  type flag = BETA | DELTA | EVAR | IOTA | ZETA | ETA
  type flags = flag list
  let fbeta = BETA 
  let fdelta = DELTA
  let fevar = EVAR
  let fiota = IOTA
  let fzeta = ZETA
  let feta = ETA
  let mkflags l = l
  let red_beta = List.mem BETA
  let red_delta = List.mem DELTA
  let red_evar = List.mem EVAR
  let red_eta = List.mem ETA
  let red_iota = List.mem IOTA
  let red_zeta = List.mem ZETA
end : RedFlagsSig)
*)

(* Compact Implementation *)
module RedFlags = (struct
  type flag = int
  type flags = int
  let fbeta = 1
  let fdelta = 2
  let fevar = 4
  let feta = 8 
  let fiota = 16
  let fzeta = 32
  let mkflags = List.fold_left (lor) 0
  let red_beta f = f land fbeta <> 0
  let red_delta f = f land fdelta <> 0
  let red_evar f = f land fevar <> 0
  let red_eta f = f land feta <> 0
  let red_iota f = f land fiota <> 0
  let red_zeta f = f land fzeta <> 0
end : RedFlagsSig)

open RedFlags

(* Local *)
let beta = mkflags [fbeta]
let betaevar = mkflags [fevar; fbeta]
let betaiota = mkflags [fiota; fbeta]
let betaiotazeta = mkflags [fiota; fbeta;fzeta]

(* Contextual *)
let delta = mkflags [fdelta;fevar]
let betadelta = mkflags [fbeta;fdelta;fzeta;fevar]
let betadeltaeta = mkflags [fbeta;fdelta;fzeta;fevar;feta]
let betadeltaiota = mkflags [fbeta;fdelta;fzeta;fevar;fiota]
let betadeltaiota_nolet = mkflags [fbeta;fdelta;fevar;fiota]
let betadeltaiotaeta = mkflags [fbeta;fdelta;fzeta;fevar;fiota;feta]
let betaiotaevar = mkflags [fbeta;fiota;fevar]
let betaetalet = mkflags [fbeta;feta;fzeta]

(* Beta Reduction tools *)

let rec stacklam recfun env t stack =
  match (decomp_stack stack,kind_of_term t) with
    | Some (h,stacktl), IsLambda (_,_,c) -> stacklam recfun (h::env) c stacktl
    | _ -> recfun (substl env t, stack)

let beta_applist (c,l) =
  stacklam app_stack [] c (append_stack (Array.of_list l) empty_stack)

(* Iota reduction tools *)

type 'a miota_args = {
  mP      : constr;     (* the result type *)
  mconstr : constr;     (* the constructor *)
  mci     : case_info;  (* special info to re-build pattern *)
  mcargs  : 'a list;    (* the constructor's arguments *)
  mlf     : 'a array }  (* the branch code vector *)
		       
let reducible_mind_case c = match kind_of_term c with
  | IsMutConstruct _ | IsCoFix _ -> true
  | _  -> false

let contract_cofix (bodynum,(types,names,bodies as typedbodies)) =
  let nbodies = Array.length bodies in
  let make_Fi j = mkCoFix (nbodies-j-1,typedbodies) in
  substl (list_tabulate make_Fi nbodies) bodies.(bodynum)

let reduce_mind_case mia =
  match kind_of_term mia.mconstr with
    | IsMutConstruct (ind_sp,i as cstr_sp) ->
(*	let ncargs = (fst mia.mci).(i-1) in*)
	let real_cargs = snd (list_chop (fst mia.mci) mia.mcargs) in
        applist (mia.mlf.(i-1),real_cargs)
    | IsCoFix cofix ->
	let cofix_def = contract_cofix cofix in
	mkMutCase (mia.mci, mia.mP, applist(cofix_def,mia.mcargs), mia.mlf)
    | _ -> assert false

(* contracts fix==FIX[nl;i](A1...Ak;[F1...Fk]{B1....Bk}) to produce
   Bi[Fj --> FIX[nl;j](A1...Ak;[F1...Fk]{B1...Bk})] *)

let contract_fix ((recindices,bodynum),(types,names,bodies as typedbodies)) =
  let nbodies = Array.length recindices in
  let make_Fi j = mkFix ((recindices,nbodies-j-1),typedbodies) in
  substl (list_tabulate make_Fi nbodies) bodies.(bodynum)

let fix_recarg ((recindices,bodynum),_) stack =
  assert (0 <= bodynum & bodynum < Array.length recindices);
  let recargnum = Array.get recindices bodynum in
  try 
    Some (recargnum, stack_nth stack recargnum)
  with Not_found ->
    None

type fix_reduction_result = NotReducible | Reduced of state

let reduce_fix whdfun fix stack =
  match fix_recarg fix stack with
    | None -> NotReducible
    | Some (recargnum,recarg) ->
        let (recarg'hd,_ as recarg') = whdfun (recarg, empty_stack) in
        let stack' = stack_assign stack recargnum (app_stack recarg') in
	(match kind_of_term recarg'hd with
           | IsMutConstruct _ -> Reduced (contract_fix fix, stack')
	   | _ -> NotReducible)

(* Generic reduction function *)

(* Y avait un commentaire pour whd_betadeltaiota :

   NB : Cette fonction alloue peu c'est l'appel 
     ``let (c,cargs) = whfun (recarg, empty_stack)''
                              -------------------
   qui coute cher *)

let rec whd_state_gen flags env sigma = 
  let rec whrec (x, stack as s) =
    match kind_of_term x with
      | IsRel n when red_delta flags ->
	  (match lookup_rel_value n env with
	     | Some body -> whrec (lift n body, stack)
	     | None -> s)
      | IsVar id when red_delta flags ->
	  (match lookup_named_value id env with
	     | Some body -> whrec (body, stack)
	     | None -> s)
      | IsEvar ev when red_evar flags ->
	  (match existential_opt_value sigma ev with
	     | Some body -> whrec (body, stack)
	     | None -> s)
      | IsConst const when red_delta flags ->
	  (match constant_opt_value env const with
	     | Some  body -> whrec (body, stack)
	     | None -> s)
      | IsLetIn (_,b,_,c) when red_zeta flags -> stacklam whrec [b] c stack
      | IsCast (c,_) -> whrec (c, stack)
      | IsApp (f,cl)  -> whrec (f, append_stack cl stack)
      | IsLambda (na,t,c) ->
          (match decomp_stack stack with
             | Some (a,m) when red_beta flags -> stacklam whrec [a] c m
             | None when red_eta flags ->
		 let env' = push_rel_assum (na,t) env in
		 let whrec' = whd_state_gen flags env' sigma in
                 (match kind_of_term (app_stack (whrec' (c, empty_stack))) with
                    | IsApp (f,cl) ->
			let napp = Array.length cl in
			if napp > 0 then
			  let x', l' = whrec' (array_last cl, empty_stack) in
                          match kind_of_term x', decomp_stack l' with
                            | IsRel 1, None ->
				let lc = Array.sub cl 0 (napp-1) in
				let u = if napp=1 then f else appvect (f,lc) in
				if noccurn 1 u then (pop u,empty_stack) else s
                            | _ -> s
			else s
		    | _ -> s)
	     | _ -> s)

      | IsMutCase (ci,p,d,lf) when red_iota flags ->
          let (c,cargs) = whrec (d, empty_stack) in
          if reducible_mind_case c then
            whrec (reduce_mind_case
                     {mP=p; mconstr=c; mcargs=list_of_stack cargs;
		      mci=ci; mlf=lf}, stack)
          else 
	    (mkMutCase (ci, p, app_stack (c,cargs), lf), stack)
            
      | IsFix fix when red_iota flags ->
	  (match reduce_fix whrec fix stack with
             | Reduced s' -> whrec s'
	     | NotReducible -> s)

      | x -> s
  in 
  whrec

let local_whd_state_gen flags = 
  let rec whrec (x, stack as s) =
    match kind_of_term x with
      | IsLetIn (_,b,_,c) when red_zeta flags -> stacklam whrec [b] c stack
      | IsCast (c,_) -> whrec (c, stack)
      | IsApp (f,cl)  -> whrec (f, append_stack cl stack)
      | IsLambda (_,_,c) ->
          (match decomp_stack stack with
             | Some (a,m) when red_beta flags -> stacklam whrec [a] c m
             | None when red_eta flags ->
                 (match kind_of_term (app_stack (whrec (c, empty_stack))) with 
                    | IsApp (f,cl) ->
			let napp = Array.length cl in
			if napp > 0 then
			  let x', l' = whrec (array_last cl, empty_stack) in
                          match kind_of_term x', decomp_stack l' with
                            | IsRel 1, None ->
				let lc = Array.sub cl 0 (napp-1) in
				let u = if napp=1 then f else appvect (f,lc) in
				if noccurn 1 u then (pop u,empty_stack) else s
                            | _ -> s
			else s
		    | _ -> s)
	     | _ -> s)

      | IsMutCase (ci,p,d,lf) when red_iota flags ->
          let (c,cargs) = whrec (d, empty_stack) in
          if reducible_mind_case c then
            whrec (reduce_mind_case
                     {mP=p; mconstr=c; mcargs=list_of_stack cargs;
		      mci=ci; mlf=lf}, stack)
          else 
	    (mkMutCase (ci, p, app_stack (c,cargs), lf), stack)
            
      | IsFix fix when red_iota flags ->
	  (match reduce_fix whrec fix stack with
             | Reduced s' -> whrec s'
	     | NotReducible -> s)

      | x -> s
  in 
  whrec

(* 1. Beta Reduction Functions *)

let whd_beta_state = local_whd_state_gen beta
let whd_beta_stack x = appterm_of_stack (whd_beta_state (x, empty_stack))
let whd_beta x = app_stack (whd_beta_state (x,empty_stack))

(* Nouveau ! *)
let whd_betaetalet_state = local_whd_state_gen betaetalet
let whd_betaetalet_stack x =
  appterm_of_stack (whd_betaetalet_state (x, empty_stack))
let whd_betaetalet x = app_stack (whd_betaetalet_state (x,empty_stack))

(* 2. Delta Reduction Functions *)

let whd_delta_state e = whd_state_gen delta e
let whd_delta_stack env sigma x =
  appterm_of_stack (whd_delta_state env sigma (x, empty_stack))
let whd_delta env sigma c =
  app_stack (whd_delta_state env sigma (c, empty_stack))

let whd_betadelta_state e = whd_state_gen betadelta e
let whd_betadelta_stack env sigma x =
  appterm_of_stack (whd_betadelta_state env sigma (x, empty_stack))
let whd_betadelta env sigma c =
  app_stack (whd_betadelta_state env sigma (c, empty_stack))

let whd_betaevar_state e = whd_state_gen betaevar e
let whd_betaevar_stack env sigma c =
  appterm_of_stack (whd_betaevar_state env sigma (c, empty_stack))
let whd_betaevar env sigma c =
  app_stack (whd_betaevar_state env sigma (c, empty_stack))


let whd_betadeltaeta_state e = whd_state_gen betadeltaeta e
let whd_betadeltaeta_stack env sigma x =
  appterm_of_stack (whd_betadeltaeta_state env sigma (x, empty_stack))
let whd_betadeltaeta env sigma x = 
  app_stack (whd_betadeltaeta_state env sigma (x, empty_stack))

(* 3. Iota reduction Functions *)

let whd_betaiota_state = local_whd_state_gen betaiota
let whd_betaiota_stack x =
  appterm_of_stack (whd_betaiota_state (x, empty_stack))
let whd_betaiota x =
  app_stack (whd_betaiota_state (x, empty_stack))

let whd_betaiotazeta_state = local_whd_state_gen betaiotazeta
let whd_betaiotazeta_stack x =
  appterm_of_stack (whd_betaiotazeta_state (x, empty_stack))
let whd_betaiotazeta x =
  app_stack (whd_betaiotazeta_state (x, empty_stack))

let whd_betaiotaevar_state e = whd_state_gen betaiotaevar e
let whd_betaiotaevar_stack env sigma x =
  appterm_of_stack (whd_betaiotaevar_state env sigma (x, empty_stack))
let whd_betaiotaevar env sigma x = 
  app_stack (whd_betaiotaevar_state env sigma (x, empty_stack))

let whd_betadeltaiota_state e = whd_state_gen betadeltaiota e
let whd_betadeltaiota_stack env sigma x =
  appterm_of_stack (whd_betadeltaiota_state env sigma (x, empty_stack))
let whd_betadeltaiota env sigma x = 
  app_stack (whd_betadeltaiota_state env sigma (x, empty_stack))

let whd_betadeltaiotaeta_state e = whd_state_gen betadeltaiotaeta e
let whd_betadeltaiotaeta_stack env sigma x =
  appterm_of_stack (whd_betadeltaiotaeta_state env sigma (x, empty_stack))
let whd_betadeltaiotaeta env sigma x = 
  app_stack (whd_betadeltaiotaeta_state env sigma (x, empty_stack))

let whd_betadeltaiota_nolet_state e = whd_state_gen betadeltaiota_nolet e
let whd_betadeltaiota_nolet_stack env sigma x =
  appterm_of_stack (whd_betadeltaiota_nolet_state env sigma (x, empty_stack))
let whd_betadeltaiota_nolet env sigma x = 
  app_stack (whd_betadeltaiota_nolet_state env sigma (x, empty_stack))

(********************************************************************)
(*                         Conversion                               *)
(********************************************************************)
(*
let fkey = Profile.declare_profile "fhnf";;
let fhnf info v = Profile.profile2 fkey fhnf info v;;

let fakey = Profile.declare_profile "fhnf_apply";;
let fhnf_apply info k h a = Profile.profile4 fakey fhnf_apply info k h a;;
*)

type 'a conversion_function = 
    env -> 'a evar_map -> constr -> constr -> constraints

(* Conversion utility functions *)

type conversion_test = constraints -> constraints

exception NotConvertible

(* Convertibility of sorts *)

type conv_pb = 
  | CONV 
  | CUMUL

let pb_is_equal pb = pb = CONV

let pb_equal = function
  | CUMUL -> CONV
  | CONV -> CONV

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

let base_sort_cmp pb s0 s1 =
  match (s0,s1) with
    | (Prop c1, Prop c2) -> c1 = c2
    | (Prop c1, Type u)  -> pb = CUMUL
    | (Type u1, Type u2) -> true
    | (_, _) -> false

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
	   | (IsSort s1, IsSort s2) -> 
	       if stack_args_size v1 = 0 && stack_args_size v2 = 0
	       then sort_cmp cv_pb s1 s2 cuniv
               else raise NotConvertible
	   | (IsMeta n, IsMeta m) ->
               if n=m
	       then convert_stacks infos lft1 lft2 v1 v2 cuniv
               else raise NotConvertible
	   | _ -> raise NotConvertible)

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
         if op1 = op2
         then convert_stacks infos lft1 lft2 v1 v2 cuniv
         else raise NotConvertible

     | (FConstruct op1, FConstruct op2) ->
         if op1 = op2
         then convert_stacks infos lft1 lft2 v1 v2 cuniv
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



let fconv cv_pb env sigma t1 t2 =
  if eq_constr t1 t2 then 
    Constraint.empty
  else
    let infos = create_clos_infos hnf_flags env sigma in
    ccnv cv_pb infos ELID ELID (inject t1) (inject t2)
      Constraint.empty

let conv env = fconv CONV env
let conv_leq env = fconv CUMUL env 

(*
let convleqkey = Profile.declare_profile "conv_leq";;
let conv_leq env sigma t1 t2 =
  Profile.profile4 convleqkey conv_leq env sigma t1 t2;;

let convkey = Profile.declare_profile "conv";;
let conv env sigma t1 t2 =
  Profile.profile4 convleqkey conv env sigma t1 t2;;
*)

let conv_forall2 f env sigma v1 v2 =
  array_fold_left2 
    (fun c x y -> let c' = f env sigma x y in Constraint.union c c')
    Constraint.empty
    v1 v2

let conv_forall2_i f env sigma v1 v2 =
  array_fold_left2_i 
    (fun i c x y -> let c' = f i env sigma x y in Constraint.union c c')
    Constraint.empty
    v1 v2

let test_conversion f env sigma x y =
  try let _ = f env sigma x y in true with NotConvertible -> false

let is_conv env sigma = test_conversion conv env sigma
let is_conv_leq env sigma = test_conversion conv_leq env sigma
let is_fconv = function | CONV -> is_conv | CUMUL -> is_conv_leq

(********************************************************************)
(*             Special-Purpose Reduction                            *)
(********************************************************************)

let whd_meta metamap c = match kind_of_term c with
  | IsMeta p -> (try List.assoc p metamap with Not_found -> c)
  | _ -> c
	
(* Try to replace all metas. Does not replace metas in the metas' values
 * Differs from (strong whd_meta). *)
let plain_instance s c = 
  let rec irec u = match kind_of_term u with
    | IsMeta p -> (try List.assoc p s with Not_found -> u)
    | IsCast (m,_) when isMeta m ->
	(try List.assoc (destMeta m) s with Not_found -> u)
    | _ -> map_constr irec u
  in 
  if s = [] then c else irec c
    
(* Pourquoi ne fait-on pas nf_betaiota si s=[] ? *)
let instance s c = 
  if s = [] then c else local_strong whd_betaiota (plain_instance s c)


(* pseudo-reduction rule:
 * [hnf_prod_app env s (Prod(_,B)) N --> B[N]
 * with an HNF on the first argument to produce a product.
 * if this does not work, then we use the string S as part of our
 * error message. *)

let hnf_prod_app env sigma t n =
  match kind_of_term (whd_betadeltaiota env sigma t) with
    | IsProd (_,_,b) -> subst1 n b
    | _ -> anomaly "hnf_prod_app: Need a product"

let hnf_prod_appvect env sigma t nl = 
  Array.fold_left (hnf_prod_app env sigma) t nl

let hnf_prod_applist env sigma t nl = 
  List.fold_left (hnf_prod_app env sigma) t nl
				    
let hnf_lam_app env sigma t n =
  match kind_of_term (whd_betadeltaiota env sigma t) with
    | IsLambda (_,_,b) -> subst1 n b
    | _ -> anomaly "hnf_lam_app: Need an abstraction"

let hnf_lam_appvect env sigma t nl = 
  Array.fold_left (hnf_lam_app env sigma) t nl

let hnf_lam_applist env sigma t nl = 
  List.fold_left (hnf_lam_app env sigma) t nl

let splay_prod env sigma = 
  let rec decrec env m c =
    let t = whd_betadeltaiota env sigma c in
    match kind_of_term t with
      | IsProd (n,a,c0) ->
	  decrec (push_rel_assum (n,a) env)
	    ((n,a)::m) c0
      | _ -> m,t
  in 
  decrec env []

let splay_prod_assum env sigma = 
  let rec prodec_rec env l c =
    let t = whd_betadeltaiota_nolet env sigma c in
    match kind_of_term c with
    | IsProd (x,t,c)  ->
	prodec_rec (push_rel_assum (x,t) env)
	  (Sign.add_rel_assum (x, t) l) c
    | IsLetIn (x,b,t,c) ->
	prodec_rec (push_rel_def (x,b, t) env)
	  (Sign.add_rel_def (x,b, t) l) c
    | IsCast (c,_)    -> prodec_rec env l c
    | _               -> l,t
  in
  prodec_rec env Sign.empty_rel_context

let splay_arity env sigma c =
  let l, c = splay_prod env sigma c in
  match kind_of_term c with
    | IsSort s -> l,s
    | _ -> error "not an arity"

let sort_of_arity env c = snd (splay_arity env Evd.empty c)
  
let decomp_n_prod env sigma n = 
  let rec decrec env m ln c = if m = 0 then (ln,c) else 
    match kind_of_term (whd_betadeltaiota env sigma c) with
      | IsProd (n,a,c0) ->
	  decrec (push_rel_assum (n,a) env)
	    (m-1) (Sign.add_rel_assum (n,a) ln) c0
      | _                      -> error "decomp_n_prod: Not enough products"
  in 
  decrec env n Sign.empty_rel_context

(* One step of approximation *)

let rec apprec env sigma s =
  let (t, stack as s) = whd_betaiota_state s in
  match kind_of_term t with
    | IsMutCase (ci,p,d,lf) ->
        let (cr,crargs) = whd_betadeltaiota_stack env sigma d in
        let rslt = mkMutCase (ci, p, applist (cr,crargs), lf) in
        if reducible_mind_case cr then 
	  apprec env sigma (rslt, stack)
        else 
	  s
    | IsFix fix ->
	  (match reduce_fix (whd_betadeltaiota_state env sigma) fix stack with
             | Reduced s -> apprec env sigma s
	     | NotReducible -> s)
    | _ -> s

let hnf env sigma c = apprec env sigma (c, empty_stack)

(* A reduction function like whd_betaiota but which keeps casts
 * and does not reduce redexes containing existential variables.
 * Used in Correctness.
 * Added by JCF, 29/1/98. *)

let whd_programs_stack env sigma = 
  let rec whrec (x, stack as s) =
    match kind_of_term x with
      | IsApp (f,cl) ->
	  let n = Array.length cl - 1 in
	  let c = cl.(n) in
	  if occur_existential c then 
	    s 
	  else 
	    whrec (mkApp (f, Array.sub cl 0 n), append_stack [|c|] stack)
      | IsLetIn (_,b,_,c) ->
	  if occur_existential b then
	    s
	  else
	    stacklam whrec [b] c stack
      | IsLambda (_,_,c) ->
          (match decomp_stack stack with
             | None -> s
             | Some (a,m) -> stacklam whrec [a] c m)
      | IsMutCase (ci,p,d,lf) ->
	  if occur_existential d then
	    s
	  else
            let (c,cargs) = whrec (d, empty_stack) in
            if reducible_mind_case c then
	      whrec (reduce_mind_case
		       {mP=p; mconstr=c; mcargs=list_of_stack cargs;
			mci=ci; mlf=lf}, stack)
	    else
	      (mkMutCase (ci, p, app_stack(c,cargs), lf), stack)
      | IsFix fix ->
	  (match reduce_fix whrec fix stack with
             | Reduced s' -> whrec s'
	     | NotReducible -> s)
      | _ -> s
  in 
  whrec

let whd_programs env sigma x =
  app_stack (whd_programs_stack env sigma (x, empty_stack))

exception IsType

let find_conclusion env sigma =
  let rec decrec env c =
    let t = whd_betadeltaiota env sigma c in
    match kind_of_term t with
      | IsProd (x,t,c0) -> decrec (push_rel_assum (x,t) env) c0
      | IsLambda (x,t,c0) -> decrec (push_rel_assum (x,t) env) c0
      | t -> t
  in 
  decrec env

let is_arity env sigma c =
  match find_conclusion env sigma c with
    | IsSort _ -> true
    | _ -> false
 
let info_arity env sigma c =
  match find_conclusion env sigma c with
    | IsSort (Prop Null) -> false 
    | IsSort (Prop Pos) -> true 
    | _ -> raise IsType
    
let is_info_arity env sigma c =
  try (info_arity env sigma c) with IsType -> true
  
let is_type_arity env sigma c = 
  match find_conclusion env sigma c with
    | IsSort (Type _) -> true
    | _ -> false

let is_info_type env sigma t =
  let s = t.utj_type in
  (s = Prop Pos) ||
  (s <> Prop Null && 
   try info_arity env sigma t.utj_val with IsType -> true)
