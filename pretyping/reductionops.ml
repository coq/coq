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
open Termops
open Univ
open Evd
open Declarations
open Environ
open Instantiate
open Closure
open Esubst
open Reduction

exception Elimconst

(* The type of (machine) states (= lambda-bar-calculus' cuts) *) 
type state = constr * constr stack

type  contextual_reduction_function = env ->  evar_map -> constr -> constr
type  reduction_function =  contextual_reduction_function
type local_reduction_function = constr -> constr

type  contextual_stack_reduction_function = 
    env ->  evar_map -> constr -> constr * constr list
type  stack_reduction_function =  contextual_stack_reduction_function
type local_stack_reduction_function = constr -> constr * constr list

type  contextual_state_reduction_function = 
    env ->  evar_map -> state -> state
type  state_reduction_function =  contextual_state_reduction_function
type local_state_reduction_function = state -> state

(*************************************)
(*** Reduction Functions Operators ***)
(*************************************)

let rec whd_state (x, stack as s) =
  match kind_of_term x with
    | App (f,cl) -> whd_state (f, append_stack cl stack)
    | Cast (c,_)  -> whd_state (c, stack)
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
    | Prod (na,a,b) -> mkProd (na,a,strong_prodspine redfun b)
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
let evar = mkflags [fevar]
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
let betalet = mkflags [fbeta;fzeta]

(* Beta Reduction tools *)

let rec stacklam recfun env t stack =
  match (decomp_stack stack,kind_of_term t) with
    | Some (h,stacktl), Lambda (_,_,c) -> stacklam recfun (h::env) c stacktl
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
  | Construct _ | CoFix _ -> true
  | _  -> false

let contract_cofix (bodynum,(types,names,bodies as typedbodies)) =
  let nbodies = Array.length bodies in
  let make_Fi j = mkCoFix (nbodies-j-1,typedbodies) in
  substl (list_tabulate make_Fi nbodies) bodies.(bodynum)

let reduce_mind_case mia =
  match kind_of_term mia.mconstr with
    | Construct (ind_sp,i as cstr_sp) ->
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

let reduce_fix whdfun fix stack =
  match fix_recarg fix stack with
    | None -> NotReducible
    | Some (recargnum,recarg) ->
        let (recarg'hd,_ as recarg') = whdfun (recarg, empty_stack) in
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
      | Evar ev when red_evar flags ->
	  (match existential_opt_value sigma ev with
	     | Some body -> whrec (body, stack)
	     | None -> s)
      | Const const when red_delta flags ->
	  (match constant_opt_value env const with
	     | Some  body -> whrec (body, stack)
	     | None -> s)
      | LetIn (_,b,_,c) when red_zeta flags -> stacklam whrec [b] c stack
      | Cast (c,_) -> whrec (c, stack)
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
	  (match reduce_fix whrec fix stack with
             | Reduced s' -> whrec s'
	     | NotReducible -> s)

      | x -> s
  in 
  whrec

let local_whd_state_gen flags = 
  let rec whrec (x, stack as s) =
    match kind_of_term x with
      | LetIn (_,b,_,c) when red_zeta flags -> stacklam whrec [b] c stack
      | Cast (c,_) -> whrec (c, stack)
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

let whd_betalet_state = local_whd_state_gen betalet
let whd_betalet_stack x = appterm_of_stack (whd_betalet_state (x, empty_stack))
let whd_betalet x = app_stack (whd_betalet_state (x,empty_stack))

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

(****************************************************************************)
(*                   Reduction Functions                                    *)
(****************************************************************************)

(* Replacing defined evars for error messages *)
let rec whd_evar sigma c =
  match kind_of_term c with
    | Evar (ev,args) when Evd.in_dom sigma ev & Evd.is_defined sigma ev ->
	whd_evar sigma (Instantiate.existential_value sigma (ev,args))
    | _ -> collapse_appl c

let nf_evar sigma =
  local_strong (whd_evar sigma)

(* lazy reduction functions. The infos must be created for each term *)
let clos_norm_flags flgs env sigma t =
  norm_val (create_clos_infos flgs env) (inject (nf_evar sigma t))

let nf_beta = clos_norm_flags Closure.beta empty_env Evd.empty
let nf_betaiota = clos_norm_flags Closure.betaiota empty_env Evd.empty
let nf_betadeltaiota env sigma =
  clos_norm_flags Closure.betadeltaiota env sigma

(* lazy weak head reduction functions *)
let whd_flags flgs env sigma t =
  whd_val (create_clos_infos flgs env) (inject (nf_evar sigma t))

(********************************************************************)
(*                         Conversion                               *)
(********************************************************************)
(*
let fkey = Profile.declare_profile "fhnf";;
let fhnf info v = Profile.profile2 fkey fhnf info v;;

let fakey = Profile.declare_profile "fhnf_apply";;
let fhnf_apply info k h a = Profile.profile4 fakey fhnf_apply info k h a;;
*)

(* Conversion utility functions *)

type conversion_test = constraints -> constraints

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


let test_conversion f env sigma x y =
  try let _ = f env (nf_evar sigma x) (nf_evar sigma y) in true
  with NotConvertible -> false

let is_conv env sigma = test_conversion Reduction.conv env sigma
let is_conv_leq env sigma = test_conversion Reduction.conv_leq env sigma
let is_fconv = function | CONV -> is_conv | CUMUL -> is_conv_leq

(********************************************************************)
(*             Special-Purpose Reduction                            *)
(********************************************************************)

let whd_meta metamap c = match kind_of_term c with
  | Meta p -> (try List.assoc p metamap with Not_found -> c)
  | _ -> c
	
(* Try to replace all metas. Does not replace metas in the metas' values
 * Differs from (strong whd_meta). *)
let plain_instance s c = 
  let rec irec u = match kind_of_term u with
    | Meta p -> (try List.assoc p s with Not_found -> u)
    | App (f,l) when isCast f ->
        let (f,t) = destCast f in
        let l' = Array.map irec l in 
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
          | _ -> mkApp (irec f,l'))
    | Cast (m,_) when isMeta m ->
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

let splay_prod_assum env sigma = 
  let rec prodec_rec env l c =
    let t = whd_betadeltaiota_nolet env sigma c in
    match kind_of_term c with
    | Prod (x,t,c)  ->
	prodec_rec (push_rel (x,None,t) env)
	  (Sign.add_rel_decl (x, None, t) l) c
    | LetIn (x,b,t,c) ->
	prodec_rec (push_rel (x, Some b, t) env)
	  (Sign.add_rel_decl (x, Some b, t) l) c
    | Cast (c,_)    -> prodec_rec env l c
    | _               -> l,t
  in
  prodec_rec env Sign.empty_rel_context

let splay_arity env sigma c =
  let l, c = splay_prod env sigma c in
  match kind_of_term c with
    | Sort s -> l,s
    | _ -> error "not an arity"

let sort_of_arity env c = snd (splay_arity env Evd.empty c)
  
let decomp_n_prod env sigma n = 
  let rec decrec env m ln c = if m = 0 then (ln,c) else 
    match kind_of_term (whd_betadeltaiota env sigma c) with
      | Prod (n,a,c0) ->
	  decrec (push_rel (n,None,a) env)
	    (m-1) (Sign.add_rel_decl (n,None,a) ln) c0
      | _                      -> error "decomp_n_prod: Not enough products"
  in 
  decrec env n Sign.empty_rel_context

(* One step of approximation *)

let rec apprec env sigma s =
  let (t, stack as s) = whd_betaiota_state s in
  match kind_of_term t with
    | Case (ci,p,d,lf) ->
        let (cr,crargs) = whd_betadeltaiota_stack env sigma d in
        let rslt = mkCase (ci, p, applist (cr,crargs), lf) in
        if reducible_mind_case cr then 
	  apprec env sigma (rslt, stack)
        else 
	  s
    | Fix fix ->
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
      | Prod (x,t,c0) -> decrec (push_rel (x,None,t) env) c0
      | Lambda (x,t,c0) -> decrec (push_rel (x,None,t) env) c0
      | t -> t
  in 
  decrec env

let is_arity env sigma c =
  match find_conclusion env sigma c with
    | Sort _ -> true
    | _ -> false
 
let info_arity env sigma c =
  match find_conclusion env sigma c with
    | Sort (Prop Null) -> false 
    | Sort (Prop Pos) -> true 
    | _ -> raise IsType
    
let is_info_arity env sigma c =
  try (info_arity env sigma c) with IsType -> true
  
let is_type_arity env sigma c = 
  match find_conclusion env sigma c with
    | Sort (Type _) -> true
    | _ -> false

let is_info_type env sigma t =
  let s = t.utj_type in
  (s = Prop Pos) ||
  (s <> Prop Null && 
   try info_arity env sigma t.utj_val with IsType -> true)
