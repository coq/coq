(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Util
open Names
open Term
open Termops
open Univ
open Evd
open Declarations
open Environ
open Closure
open Esubst
open Reduction

exception Elimconst


(**********************************************************************)
(* The type of (machine) stacks (= lambda-bar-calculus' contexts)     *)

type 'a stack_member =
  | Zapp of 'a list
  | Zcase of case_info * 'a * 'a array
  | Zfix of 'a * 'a stack
  | Zshift of int
  | Zupdate of 'a

and 'a stack = 'a stack_member list

let empty_stack = []
let append_stack_list l s =
  match (l,s) with
  | ([],s) -> s
  | (l1, Zapp l :: s) -> Zapp (l1@l) :: s
  | (l1, s) -> Zapp l1 :: s
let append_stack v s = append_stack_list (Array.to_list v) s

(* Collapse the shifts in the stack *)
let zshift n s =
  match (n,s) with
      (0,_) -> s
    | (_,Zshift(k)::s) -> Zshift(n+k)::s
    | _ -> Zshift(n)::s

let rec stack_args_size = function
  | Zapp l::s -> List.length l + stack_args_size s
  | Zshift(_)::s -> stack_args_size s
  | Zupdate(_)::s -> stack_args_size s
  | _ -> 0

(* When used as an argument stack (only Zapp can appear) *)
let rec decomp_stack = function
  | Zapp[v]::s -> Some (v, s)
  | Zapp(v::l)::s -> Some (v, (Zapp l :: s))
  | Zapp [] :: s -> decomp_stack s
  | _ -> None
let rec decomp_stackn = function
  | Zapp [] :: s -> decomp_stackn s
  | Zapp l :: s -> (Array.of_list l, s)
  | _ -> assert false
let array_of_stack s =
  let rec stackrec = function
  | [] -> []
  | Zapp args :: s -> args :: (stackrec s)
  | _ -> assert false
  in Array.of_list (List.concat (stackrec s))
let rec list_of_stack = function
  | [] -> []
  | Zapp args :: s -> args @ (list_of_stack s)
  | _ -> assert false
let rec app_stack = function
  | f, [] -> f
  | f, (Zapp [] :: s) -> app_stack (f, s)
  | f, (Zapp args :: s) ->
      app_stack (applist (f, args), s)
  | _ -> assert false
let rec stack_assign s p c = match s with
  | Zapp args :: s ->
      let q = List.length args in
      if p >= q then
	Zapp args :: stack_assign s (p-q) c
      else
        (match list_chop p args with
            (bef, _::aft) -> Zapp (bef@c::aft) :: s
          | _ -> assert false)
  | _ -> s
let rec stack_tail p s =
  if p = 0 then s else
    match s with
      | Zapp args :: s ->
	  let q = List.length args in
	  if p >= q then stack_tail (p-q) s
	  else Zapp (list_skipn p args) :: s
      | _ -> failwith "stack_tail"
let rec stack_nth s p = match s with
  | Zapp args :: s ->
      let q = List.length args in
      if p >= q then stack_nth s (p-q)
      else List.nth args p
  | _ -> raise Not_found

(**************************************************************)
(* The type of (machine) states (= lambda-bar-calculus' cuts) *)
type state = constr * constr stack

type  contextual_reduction_function = env ->  evar_map -> constr -> constr
type  reduction_function =  contextual_reduction_function
type local_reduction_function = evar_map -> constr -> constr

type  contextual_stack_reduction_function =
    env ->  evar_map -> constr -> constr * constr list
type  stack_reduction_function =  contextual_stack_reduction_function
type local_stack_reduction_function =
    evar_map -> constr -> constr * constr list

type  contextual_state_reduction_function =
    env ->  evar_map -> state -> state
type  state_reduction_function =  contextual_state_reduction_function
type local_state_reduction_function = evar_map -> state -> state

(*************************************)
(*** Reduction Functions Operators ***)
(*************************************)

let safe_evar_value sigma ev =
  try Some (Evd.existential_value sigma ev)
  with NotInstantiatedEvar | Not_found -> None

let rec whd_app_state sigma (x, stack as s) =
  match kind_of_term x with
    | App (f,cl) -> whd_app_state sigma (f, append_stack cl stack)
    | Cast (c,_,_)  -> whd_app_state sigma (c, stack)
    | Evar ev ->
        (match safe_evar_value sigma ev with
            Some c -> whd_app_state sigma (c,stack)
          | _ -> s)
    | _             -> s

let safe_meta_value sigma ev =
  try Some (Evd.meta_value sigma ev)
  with Not_found -> None

let appterm_of_stack (f,s) = (f,list_of_stack s)

let whd_stack sigma x =
  appterm_of_stack (whd_app_state sigma (x, empty_stack))
let whd_castapp_stack = whd_stack

let stack_reduction_of_reduction red_fun env sigma s =
  let t = red_fun env sigma (app_stack s) in
  whd_stack t

let strong whdfun env sigma t =
  let rec strongrec env t =
    map_constr_with_full_binders push_rel strongrec env (whdfun env sigma t) in
  strongrec env t

let local_strong whdfun sigma =
  let rec strongrec t = map_constr strongrec (whdfun sigma t) in
  strongrec

let rec strong_prodspine redfun sigma c =
  let x = redfun sigma c in
  match kind_of_term x with
    | Prod (na,a,b) -> mkProd (na,a,strong_prodspine redfun sigma b)
    | _ -> x

(*************************************)
(*** Reduction using bindingss ***)
(*************************************)

(* This signature is very similar to Closure.RedFlagsSig except there
   is eta but no per-constant unfolding *)

module type RedFlagsSig = sig
  type flags
  type flag
  val fbeta : flag
  val fdelta : flag
  val feta : flag
  val fiota : flag
  val fzeta : flag
  val mkflags : flag list -> flags
  val red_beta : flags -> bool
  val red_delta : flags -> bool
  val red_eta : flags -> bool
  val red_iota : flags -> bool
  val red_zeta : flags -> bool
end

(* Compact Implementation *)
module RedFlags = (struct
  type flag = int
  type flags = int
  let fbeta = 1
  let fdelta = 2
  let feta = 8
  let fiota = 16
  let fzeta = 32
  let mkflags = List.fold_left (lor) 0
  let red_beta f = f land fbeta <> 0
  let red_delta f = f land fdelta <> 0
  let red_eta f = f land feta <> 0
  let red_iota f = f land fiota <> 0
  let red_zeta f = f land fzeta <> 0
end : RedFlagsSig)

open RedFlags

(* Local *)
let beta = mkflags [fbeta]
let eta = mkflags [feta]
let zeta = mkflags [fzeta]
let betaiota = mkflags [fiota; fbeta]
let betaiotazeta = mkflags [fiota; fbeta;fzeta]

(* Contextual *)
let delta = mkflags [fdelta]
let betadelta = mkflags [fbeta;fdelta;fzeta]
let betadeltaeta = mkflags [fbeta;fdelta;fzeta;feta]
let betadeltaiota = mkflags [fbeta;fdelta;fzeta;fiota]
let betadeltaiota_nolet = mkflags [fbeta;fdelta;fiota]
let betadeltaiotaeta = mkflags [fbeta;fdelta;fzeta;fiota;feta]
let betaetalet = mkflags [fbeta;feta;fzeta]
let betalet = mkflags [fbeta;fzeta]

(* Beta Reduction tools *)

let rec stacklam recfun env t stack =
  match (decomp_stack stack,kind_of_term t) with
    | Some (h,stacktl), Lambda (_,_,c) -> stacklam recfun (h::env) c stacktl
    | _ -> recfun (substl env t, stack)

let beta_applist (c,l) =
  stacklam app_stack [] c (append_stack_list l empty_stack)

(* Iota reduction tools *)

type 'a miota_args = {
  mP      : constr;     (* the result type *)
  mconstr : constr;     (* the constructor *)
  mci     : case_info;  (* special info to re-build pattern *)
  mcargs  : 'a list;    (* the constructor's arguments *)
  mlf     : 'a array }  (* the branch code vector *)

let reducible_mind_case c = match kind_of_term c with
  | Construct _ | CoFix _ -> true
  | _  -> false

let contract_cofix (bodynum,(types,names,bodies as typedbodies)) =
  let nbodies = Array.length bodies in
  let make_Fi j = mkCoFix (nbodies-j-1,typedbodies) in
  substl (list_tabulate make_Fi nbodies) bodies.(bodynum)

let reduce_mind_case mia =
  match kind_of_term mia.mconstr with
    | Construct (ind_sp,i) ->
(*	let ncargs = (fst mia.mci).(i-1) in*)
	let real_cargs = list_skipn mia.mci.ci_npar mia.mcargs in
        applist (mia.mlf.(i-1),real_cargs)
    | CoFix cofix ->
	let cofix_def = contract_cofix cofix in
	mkCase (mia.mci, mia.mP, applist(cofix_def,mia.mcargs), mia.mlf)
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

let reduce_fix whdfun sigma fix stack =
  match fix_recarg fix stack with
    | None -> NotReducible
    | Some (recargnum,recarg) ->
        let (recarg'hd,_ as recarg') = whdfun sigma (recarg, empty_stack) in
        let stack' = stack_assign stack recargnum (app_stack recarg') in
	(match kind_of_term recarg'hd with
           | Construct _ -> Reduced (contract_fix fix, stack')
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
      | Rel n when red_delta flags ->
	  (match lookup_rel n env with
	     | (_,Some body,_) -> whrec (lift n body, stack)
	     | _ -> s)
      | Var id when red_delta flags ->
	  (match lookup_named id env with
	     | (_,Some body,_) -> whrec (body, stack)
	     | _ -> s)
      | Evar ev ->
	  (match safe_evar_value sigma ev with
	     | Some body -> whrec (body, stack)
	     | None -> s)
      | Meta ev ->
	  (match safe_meta_value sigma ev with
	     | Some body -> whrec (body, stack)
	     | None -> s)
      | Const const when red_delta flags ->
	  (match constant_opt_value env const with
	     | Some  body -> whrec (body, stack)
	     | None -> s)
      | LetIn (_,b,_,c) when red_zeta flags -> stacklam whrec [b] c stack
      | Cast (c,_,_) -> whrec (c, stack)
      | App (f,cl)  -> whrec (f, append_stack cl stack)
      | Lambda (na,t,c) ->
          (match decomp_stack stack with
             | Some (a,m) when red_beta flags -> stacklam whrec [a] c m
             | None when red_eta flags ->
		 let env' = push_rel (na,None,t) env in
		 let whrec' = whd_state_gen flags env' sigma in
                 (match kind_of_term (app_stack (whrec' (c, empty_stack))) with
                    | App (f,cl) ->
			let napp = Array.length cl in
			if napp > 0 then
			  let x', l' = whrec' (array_last cl, empty_stack) in
                          match kind_of_term x', decomp_stack l' with
                            | Rel 1, None ->
				let lc = Array.sub cl 0 (napp-1) in
				let u = if napp=1 then f else appvect (f,lc) in
				if noccurn 1 u then (pop u,empty_stack) else s
                            | _ -> s
			else s
		    | _ -> s)
	     | _ -> s)

      | Case (ci,p,d,lf) when red_iota flags ->
          let (c,cargs) = whrec (d, empty_stack) in
          if reducible_mind_case c then
            whrec (reduce_mind_case
                     {mP=p; mconstr=c; mcargs=list_of_stack cargs;
		      mci=ci; mlf=lf}, stack)
          else
	    (mkCase (ci, p, app_stack (c,cargs), lf), stack)

      | Fix fix when red_iota flags ->
	  (match reduce_fix (fun _ -> whrec) sigma fix stack with
             | Reduced s' -> whrec s'
	     | NotReducible -> s)

      | x -> s
  in
  whrec

let local_whd_state_gen flags sigma =
  let rec whrec (x, stack as s) =
    match kind_of_term x with
      | LetIn (_,b,_,c) when red_zeta flags -> stacklam whrec [b] c stack
      | Cast (c,_,_) -> whrec (c, stack)
      | App (f,cl)  -> whrec (f, append_stack cl stack)
      | Lambda (_,_,c) ->
          (match decomp_stack stack with
             | Some (a,m) when red_beta flags -> stacklam whrec [a] c m
             | None when red_eta flags ->
                 (match kind_of_term (app_stack (whrec (c, empty_stack))) with
                    | App (f,cl) ->
			let napp = Array.length cl in
			if napp > 0 then
			  let x', l' = whrec (array_last cl, empty_stack) in
                          match kind_of_term x', decomp_stack l' with
                            | Rel 1, None ->
				let lc = Array.sub cl 0 (napp-1) in
				let u = if napp=1 then f else appvect (f,lc) in
				if noccurn 1 u then (pop u,empty_stack) else s
                            | _ -> s
			else s
		    | _ -> s)
	     | _ -> s)

      | Case (ci,p,d,lf) when red_iota flags ->
          let (c,cargs) = whrec (d, empty_stack) in
          if reducible_mind_case c then
            whrec (reduce_mind_case
                     {mP=p; mconstr=c; mcargs=list_of_stack cargs;
		      mci=ci; mlf=lf}, stack)
          else
	    (mkCase (ci, p, app_stack (c,cargs), lf), stack)

      | Fix fix when red_iota flags ->
	  (match reduce_fix (fun _ ->whrec) sigma fix stack with
             | Reduced s' -> whrec s'
	     | NotReducible -> s)

      | Evar ev ->
          (match safe_evar_value sigma ev with
              Some c -> whrec (c,stack)
            | None -> s)

      | Meta ev ->
          (match safe_meta_value sigma ev with
              Some c -> whrec (c,stack)
            | None -> s)

      | x -> s
  in
  whrec


let stack_red_of_state_red f sigma x =
  appterm_of_stack (f sigma (x, empty_stack))

let red_of_state_red f sigma x =
  app_stack (f sigma (x,empty_stack))

(* 1. Beta Reduction Functions *)

let whd_beta_state = local_whd_state_gen beta
let whd_beta_stack = stack_red_of_state_red whd_beta_state
let whd_beta = red_of_state_red whd_beta_state

(* Nouveau ! *)
let whd_betaetalet_state = local_whd_state_gen betaetalet
let whd_betaetalet_stack = stack_red_of_state_red whd_betaetalet_state
let whd_betaetalet = red_of_state_red whd_betaetalet_state

let whd_betalet_state = local_whd_state_gen betalet
let whd_betalet_stack = stack_red_of_state_red whd_betalet_state
let whd_betalet = red_of_state_red whd_betalet_state

(* 2. Delta Reduction Functions *)

let whd_delta_state e = whd_state_gen delta e
let whd_delta_stack env = stack_red_of_state_red (whd_delta_state env)
let whd_delta env = red_of_state_red  (whd_delta_state env)

let whd_betadelta_state e = whd_state_gen betadelta e
let whd_betadelta_stack env =
  stack_red_of_state_red (whd_betadelta_state env)
let whd_betadelta env =
  red_of_state_red (whd_betadelta_state env)


let whd_betadeltaeta_state e = whd_state_gen betadeltaeta e
let whd_betadeltaeta_stack env =
  stack_red_of_state_red (whd_betadeltaeta_state env)
let whd_betadeltaeta env =
  red_of_state_red (whd_betadeltaeta_state env)

(* 3. Iota reduction Functions *)

let whd_betaiota_state = local_whd_state_gen betaiota
let whd_betaiota_stack = stack_red_of_state_red whd_betaiota_state
let whd_betaiota = red_of_state_red whd_betaiota_state

let whd_betaiotazeta_state = local_whd_state_gen betaiotazeta
let whd_betaiotazeta_stack = stack_red_of_state_red whd_betaiotazeta_state
let whd_betaiotazeta = red_of_state_red whd_betaiotazeta_state

let whd_betadeltaiota_state e = whd_state_gen betadeltaiota e
let whd_betadeltaiota_stack env =
  stack_red_of_state_red (whd_betadeltaiota_state env)
let whd_betadeltaiota env =
  red_of_state_red (whd_betadeltaiota_state env)

let whd_betadeltaiotaeta_state e = whd_state_gen betadeltaiotaeta e
let whd_betadeltaiotaeta_stack env =
  stack_red_of_state_red (whd_betadeltaiotaeta_state env)
let whd_betadeltaiotaeta env =
  red_of_state_red (whd_betadeltaiotaeta_state env)

let whd_betadeltaiota_nolet_state e = whd_state_gen betadeltaiota_nolet e
let whd_betadeltaiota_nolet_stack env =
  stack_red_of_state_red (whd_betadeltaiota_nolet_state env)
let whd_betadeltaiota_nolet env =
  red_of_state_red (whd_betadeltaiota_nolet_state env)

(* 4. Eta reduction Functions *)

let whd_eta c = app_stack (local_whd_state_gen eta Evd.empty (c,empty_stack))

(* 5. Zeta Reduction Functions *)

let whd_zeta c = app_stack (local_whd_state_gen zeta Evd.empty (c,empty_stack))

(****************************************************************************)
(*                   Reduction Functions                                    *)
(****************************************************************************)

(* Replacing defined evars for error messages *)
let rec whd_evar sigma c =
  match kind_of_term c with
    | Evar ev ->
        (match safe_evar_value sigma ev with
            Some c -> whd_evar sigma c
          | None -> c)
    | Sort s -> whd_sort_variable sigma c
    | _ -> c

let nf_evar =
  local_strong whd_evar

(* lazy reduction functions. The infos must be created for each term *)
(* Note by HH [oct 08] : why would it be the job of clos_norm_flags to add
   a [nf_evar] here *)
let clos_norm_flags flgs env sigma t =
  norm_val
    (create_clos_infos ~evars:(safe_evar_value sigma) flgs env)
    (inject t)

let nf_beta = clos_norm_flags Closure.beta empty_env
let nf_betaiota = clos_norm_flags Closure.betaiota empty_env
let nf_betadeltaiota env sigma =
  clos_norm_flags Closure.betadeltaiota env sigma


(* Attention reduire un beta-redexe avec un argument qui n'est pas
   une variable, peut changer enormement le temps de conversion lors
   du type checking :
     (fun x => x + x) M
*)
let rec whd_betaiota_preserving_vm_cast env sigma t =
   let rec stacklam_var subst t stack =
     match (decomp_stack stack,kind_of_term t) with
     | Some (h,stacktl), Lambda (_,_,c) ->
         begin match kind_of_term h with
         | Rel i when not (evaluable_rel i env) ->
             stacklam_var (h::subst) c stacktl
         | Var id when  not (evaluable_named id env)->
             stacklam_var (h::subst) c stacktl
         | _ -> whrec (substl subst t, stack)
         end
     | _ -> whrec (substl subst t, stack)
   and whrec (x, stack as s) =
     match kind_of_term x with
       | Evar ev ->
           (match safe_evar_value sigma ev with
              | Some body -> whrec (body, stack)
              | None -> s)
       | Cast (c,VMcast,t) ->
           let c = app_stack (whrec (c,empty_stack)) in
           let t = app_stack (whrec (t,empty_stack)) in
           (mkCast(c,VMcast,t),stack)
       | Cast (c,DEFAULTcast,_) ->
           whrec (c, stack)
       | App (f,cl)  -> whrec (f, append_stack cl stack)
       | Lambda (na,t,c) ->
           (match decomp_stack stack with
            | Some (a,m) -> stacklam_var [a] c m
            | _ -> s)
       | Case (ci,p,d,lf) ->
           let (c,cargs) = whrec (d, empty_stack) in
           if reducible_mind_case c then
             whrec (reduce_mind_case
                      {mP=p; mconstr=c; mcargs=list_of_stack cargs;
                       mci=ci; mlf=lf}, stack)
           else
             (mkCase (ci, p, app_stack (c,cargs), lf), stack)
       | x -> s
   in
   app_stack (whrec (t,empty_stack))

let nf_betaiota_preserving_vm_cast =
  strong whd_betaiota_preserving_vm_cast

(* lazy weak head reduction functions *)
let whd_flags flgs env sigma t =
  whd_val
    (create_clos_infos ~evars:(safe_evar_value sigma) flgs env)
    (inject t)

(********************************************************************)
(*                         Conversion                               *)
(********************************************************************)
(*
let fkey = Profile.declare_profile "fhnf";;
let fhnf info v = Profile.profile2 fkey fhnf info v;;

let fakey = Profile.declare_profile "fhnf_apply";;
let fhnf_apply info k h a = Profile.profile4 fakey fhnf_apply info k h a;;
*)

let is_transparent k =
  Conv_oracle.get_strategy k <> Conv_oracle.Opaque

(* Conversion utility functions *)

type conversion_test = constraints -> constraints

let pb_is_equal pb = pb = CONV

let pb_equal = function
  | CUMUL -> CONV
  | CONV -> CONV

let sort_cmp = sort_cmp

let test_conversion (f:?evars:'a->'b) env sigma x y =
  try let _ =
    f ~evars:(safe_evar_value sigma) env x y in true
  with NotConvertible -> false

let is_conv env sigma = test_conversion Reduction.conv env sigma
let is_conv_leq env sigma = test_conversion Reduction.conv_leq env sigma
let is_fconv = function | CONV -> is_conv | CUMUL -> is_conv_leq

let test_trans_conversion f reds env sigma x y =
  try let _ = f reds env (nf_evar sigma x) (nf_evar sigma y) in true
  with NotConvertible -> false

let is_trans_conv reds env sigma = test_trans_conversion Reduction.trans_conv reds env sigma
let is_trans_conv_leq reds env sigma = test_trans_conversion Reduction.trans_conv_leq reds env sigma
let is_trans_fconv = function | CONV -> is_trans_conv | CUMUL -> is_trans_conv_leq

(********************************************************************)
(*             Special-Purpose Reduction                            *)
(********************************************************************)

let whd_meta metasubst c = match kind_of_term c with
  | Meta p -> (try List.assoc p metasubst with Not_found -> c)
  | _ -> c

(* Try to replace all metas. Does not replace metas in the metas' values
 * Differs from (strong whd_meta). *)
let plain_instance s c =
  let rec irec n u = match kind_of_term u with
    | Meta p -> (try lift n (List.assoc p s) with Not_found -> u)
    | App (f,l) when isCast f ->
        let (f,_,t) = destCast f in
        let l' = Array.map (irec n) l in
        (match kind_of_term f with
        | Meta p ->
	    (* Don't flatten application nodes: this is used to extract a
               proof-term from a proof-tree and we want to keep the structure
               of the proof-tree *)
	    (try let g = List.assoc p s in
	    match kind_of_term g with
            | App _ ->
                let h = id_of_string "H" in
                mkLetIn (Name h,g,t,mkApp(mkRel 1,Array.map (lift 1) l'))
            | _ -> mkApp (g,l')
	    with Not_found -> mkApp (f,l'))
        | _ -> mkApp (irec n f,l'))
    | Cast (m,_,_) when isMeta m ->
	(try lift n (List.assoc (destMeta m) s) with Not_found -> u)
    | _ ->
	map_constr_with_binders succ irec n u
  in
  if s = [] then c else irec 0 c

(* [instance] is used for [res_pf]; the call to [local_strong whd_betaiota]
   has (unfortunately) different subtle side effects:

   - ** Order of subgoals **
     If the lemma is a case analysis with parameters, it will move the
     parameters as first subgoals (e.g. "case H" applied on
     "H:D->A/\B|-C" will present the subgoal |-D first while w/o
     betaiota the subgoal |-D would have come last).

   - ** Betaiota-contraction in statement **
     If the lemma has a parameter which is a function and this
     function is applied in the lemma, then the _strong_ betaiota will
     contract the application of the function to its argument (e.g.
     "apply (H (fun x => x))" in "H:forall f, f 0 = 0 |- 0=0" will
     result in applying the lemma 0=0 in which "(fun x => x) 0" has
     been contracted). A goal to rewrite may then fail or succeed
     differently.

   - ** Naming of hypotheses **
     If a lemma is a function of the form "fun H:(forall a:A, P a)
     => .. F H .." where the expected type of H is "forall b:A, P b",
     then, without reduction, the application of the lemma will
     generate a subgoal "forall a:A, P a" (and intro will use name
     "a"), while with reduction, it will generate a subgoal "forall
     b:A, P b" (and intro will use name "b").

   - ** First-order pattern-matching **
     If a lemma has the type "(fun x => p) t" then rewriting t may fail
     if the type of the lemma is first beta-reduced (this typically happens
     when rewriting a single variable and the type of the lemma is obtained
     by meta_instance (with empty map) which itself calls instance with this
     empty map).
 *)

let instance sigma s c =
  (* if s = [] then c else *)
  local_strong whd_betaiota sigma (plain_instance s c)

(* pseudo-reduction rule:
 * [hnf_prod_app env s (Prod(_,B)) N --> B[N]
 * with an HNF on the first argument to produce a product.
 * if this does not work, then we use the string S as part of our
 * error message. *)

let hnf_prod_app env sigma t n =
  match kind_of_term (whd_betadeltaiota env sigma t) with
    | Prod (_,_,b) -> subst1 n b
    | _ -> anomaly "hnf_prod_app: Need a product"

let hnf_prod_appvect env sigma t nl =
  Array.fold_left (hnf_prod_app env sigma) t nl

let hnf_prod_applist env sigma t nl =
  List.fold_left (hnf_prod_app env sigma) t nl

let hnf_lam_app env sigma t n =
  match kind_of_term (whd_betadeltaiota env sigma t) with
    | Lambda (_,_,b) -> subst1 n b
    | _ -> anomaly "hnf_lam_app: Need an abstraction"

let hnf_lam_appvect env sigma t nl =
  Array.fold_left (hnf_lam_app env sigma) t nl

let hnf_lam_applist env sigma t nl =
  List.fold_left (hnf_lam_app env sigma) t nl

let splay_prod env sigma =
  let rec decrec env m c =
    let t = whd_betadeltaiota env sigma c in
    match kind_of_term t with
      | Prod (n,a,c0) ->
	  decrec (push_rel (n,None,a) env)
	    ((n,a)::m) c0
      | _ -> m,t
  in
  decrec env []

let splay_lam env sigma =
  let rec decrec env m c =
    let t = whd_betadeltaiota env sigma c in
    match kind_of_term t with
      | Lambda (n,a,c0) ->
	  decrec (push_rel (n,None,a) env)
	    ((n,a)::m) c0
      | _ -> m,t
  in
  decrec env []

let splay_prod_assum env sigma =
  let rec prodec_rec env l c =
    let t = whd_betadeltaiota_nolet env sigma c in
    match kind_of_term t with
    | Prod (x,t,c)  ->
	prodec_rec (push_rel (x,None,t) env)
	  (add_rel_decl (x, None, t) l) c
    | LetIn (x,b,t,c) ->
	prodec_rec (push_rel (x, Some b, t) env)
	  (add_rel_decl (x, Some b, t) l) c
    | Cast (c,_,_)    -> prodec_rec env l c
    | _               -> l,t
  in
  prodec_rec env empty_rel_context

let splay_arity env sigma c =
  let l, c = splay_prod env sigma c in
  match kind_of_term c with
    | Sort s -> l,s
    | _ -> invalid_arg "splay_arity"

let sort_of_arity env c = snd (splay_arity env Evd.empty c)

let splay_prod_n env sigma n =
  let rec decrec env m ln c = if m = 0 then (ln,c) else
    match kind_of_term (whd_betadeltaiota env sigma c) with
      | Prod (n,a,c0) ->
	  decrec (push_rel (n,None,a) env)
	    (m-1) (add_rel_decl (n,None,a) ln) c0
      | _                      -> invalid_arg "splay_prod_n"
  in
  decrec env n empty_rel_context

let splay_lam_n env sigma n =
  let rec decrec env m ln c = if m = 0 then (ln,c) else
    match kind_of_term (whd_betadeltaiota env sigma c) with
      | Lambda (n,a,c0) ->
	  decrec (push_rel (n,None,a) env)
	    (m-1) (add_rel_decl (n,None,a) ln) c0
      | _                      -> invalid_arg "splay_lam_n"
  in
  decrec env n empty_rel_context

exception NotASort

let decomp_sort env sigma t =
  match kind_of_term (whd_betadeltaiota env sigma t) with
  | Sort s -> s
  | _ -> raise NotASort

let is_sort env sigma arity =
  try let _ = decomp_sort env sigma arity in true
  with NotASort -> false

(* reduction to head-normal-form allowing delta/zeta only in argument
   of case/fix (heuristic used by evar_conv) *)

let whd_betaiota_deltazeta_for_iota_state env sigma s =
  let rec whrec s =
    let (t, stack as s) = whd_betaiota_state sigma s in
    match kind_of_term t with
    | Case (ci,p,d,lf) ->
        let (cr,crargs) = whd_betadeltaiota_stack env sigma d in
        let rslt = mkCase (ci, p, applist (cr,crargs), lf) in
        if reducible_mind_case cr then
	  whrec (rslt, stack)
        else
	  s
    | Fix fix ->
	  (match reduce_fix (whd_betadeltaiota_state env) sigma fix stack with
             | Reduced s -> whrec s
	     | NotReducible -> s)
    | _ -> s
  in whrec s

(* A reduction function like whd_betaiota but which keeps casts
 * and does not reduce redexes containing existential variables.
 * Used in Correctness.
 * Added by JCF, 29/1/98. *)

let whd_programs_stack env sigma =
  let rec whrec (x, stack as s) =
    match kind_of_term x with
      | App (f,cl) ->
	  let n = Array.length cl - 1 in
	  let c = cl.(n) in
	  if occur_existential c then
	    s
	  else
	    whrec (mkApp (f, Array.sub cl 0 n), append_stack [|c|] stack)
      | LetIn (_,b,_,c) ->
	  if occur_existential b then
	    s
	  else
	    stacklam whrec [b] c stack
      | Lambda (_,_,c) ->
          (match decomp_stack stack with
             | None -> s
             | Some (a,m) -> stacklam whrec [a] c m)
      | Case (ci,p,d,lf) ->
	  if occur_existential d then
	    s
	  else
            let (c,cargs) = whrec (d, empty_stack) in
            if reducible_mind_case c then
	      whrec (reduce_mind_case
		       {mP=p; mconstr=c; mcargs=list_of_stack cargs;
			mci=ci; mlf=lf}, stack)
	    else
	      (mkCase (ci, p, app_stack(c,cargs), lf), stack)
      | Fix fix ->
	  (match reduce_fix (fun _ ->whrec) sigma  fix stack with
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
      | Prod (x,t,c0) -> decrec (push_rel (x,None,t) env) c0
      | Lambda (x,t,c0) -> decrec (push_rel (x,None,t) env) c0
      | t -> t
  in
  decrec env

let is_arity env sigma c =
  match find_conclusion env sigma c with
    | Sort _ -> true
    | _ -> false

(*************************************)
(* Metas *)

let meta_value evd mv =
  let rec valrec mv =
    match meta_opt_fvalue evd mv with
    | Some (b,_) ->
      instance evd
        (List.map (fun mv' -> (mv',valrec mv')) (Metaset.elements b.freemetas))
        b.rebus
    | None -> mkMeta mv
  in
  valrec mv

let meta_instance sigma b =
  let c_sigma =
    List.map
      (fun mv -> (mv,meta_value sigma mv)) (Metaset.elements b.freemetas)
  in
  if c_sigma = [] then b.rebus else instance sigma c_sigma b.rebus

let nf_meta sigma c = meta_instance sigma (mk_freelisted c)

(* Instantiate metas that create beta/iota redexes *)

let meta_value evd mv =
  let rec valrec mv =
    match meta_opt_fvalue evd mv with
    | Some (b,_) ->
      instance evd
        (List.map (fun mv' -> (mv',valrec mv')) (Metaset.elements b.freemetas))
        b.rebus
    | None -> mkMeta mv
  in
  valrec mv

let meta_reducible_instance evd b =
  let fm = Metaset.elements b.freemetas in
  let metas = List.fold_left (fun l mv ->
    match (try meta_opt_fvalue evd mv with Not_found -> None) with
    | Some (g,(_,s)) -> (mv,(g.rebus,s))::l
    | None -> l) [] fm in
  let rec irec u =
    let u = whd_betaiota Evd.empty u in
    match kind_of_term u with
    | Case (ci,p,c,bl) when isMeta c or isCast c & isMeta (pi1 (destCast c)) ->
	let m = try destMeta c with _ -> destMeta (pi1 (destCast c)) in
	(match
	  try
	    let g,s = List.assoc m metas in
	    if isConstruct g or s <> CoerceToType then Some g else None
	  with Not_found -> None
	  with
	    | Some g -> irec (mkCase (ci,p,g,bl))
	    | None -> mkCase (ci,irec p,c,Array.map irec bl))
    | App (f,l) when isMeta f or isCast f & isMeta (pi1 (destCast f)) ->
	let m = try destMeta f with _ -> destMeta (pi1 (destCast f)) in
	(match
	  try
	    let g,s = List.assoc m metas in
	    if isLambda g or s <> CoerceToType then Some g else None
	  with Not_found -> None
	 with
	   | Some g -> irec (mkApp (g,l))
	   | None -> mkApp (f,Array.map irec l))
    | Meta m ->
	(try let g,s = List.assoc m metas in if s<>CoerceToType then irec g else u
	 with Not_found -> u)
    | _ -> map_constr irec u
  in
  if fm = [] then (* nf_betaiota? *) b.rebus else irec b.rebus


let head_unfold_under_prod ts env _ c =
  let unfold cst =
    if Cpred.mem cst (snd ts) then
      match constant_opt_value env cst with
	| Some c -> c
	| None -> mkConst cst
    else mkConst cst in
  let rec aux c =
    match kind_of_term c with
      | Prod (n,t,c) -> mkProd (n,aux t, aux c)
      | _ ->
	  let (h,l) = decompose_app c in
	  match kind_of_term h with
	    | Const cst -> beta_applist (unfold cst,l)
	    | _ -> c in
  aux c
