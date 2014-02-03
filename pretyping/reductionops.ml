(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Errors
open Util
open Names
open Term
open Vars
open Context
open Termops
open Univ
open Evd
open Environ

exception Elimconst

(** This module implements a call by name reduction used by (at
    least) evarconv unification and cbn tactic.

    It has an ability to "refold" constants by storing constants and
    their parameters in its stack.
*)


(** The type of (machine) stacks (= lambda-bar-calculus' contexts) *)
module Stack = struct
  type 'a app_node = int * 'a array * int
  (* first releavnt position, arguments, last relevant position *)

  (*
     Invariant that this module must ensure :
     (behare of direct access to app_node by the rest of Reductionops)
     - in app_node (i,_,j) i <= j
     - There is no array realocation (outside of debug printing)
   *)

  let pr_app_node pr (i,a,j) =
    let open Pp in surround (
		     prvect_with_sep pr_comma pr (Array.sub a i (j - i + 1))
		     )

  type 'a member =
  | App of 'a app_node
  | Case of Term.case_info * 'a * 'a array * ('a * 'a list) option
  | Fix of fixpoint * 'a t * ('a * 'a list) option
  | Shift of int
  | Update of 'a
  and 'a t = 'a member list

  let rec pr_member pr_c member =
    let open Pp in
    let pr_c x = hov 1 (pr_c x) in
    match member with
    | App app -> str "ZApp" ++ pr_app_node pr_c app
    | Case (_,_,br,cst) ->
       str "ZCase(" ++
	 prvect_with_sep (pr_bar) pr_c br
       ++ str ")"
    | Fix (f,args,cst) ->
       str "ZFix(" ++ Termops.pr_fix Termops.print_constr f
       ++ pr_comma () ++ pr pr_c args ++ str ")"
    | Shift i -> str "ZShift(" ++ int i ++ str ")"
    | Update t -> str "ZUpdate(" ++ pr_c t ++ str ")"
  and pr pr_c l =
    let open Pp in
    prlist_with_sep pr_semicolon (fun x -> hov 1 (pr_member pr_c x)) l

  let empty = []

  let append_app v s =
    let le = Array.length v in
    if Int.equal le 0 then s else App (0,v,pred le) :: s

  let decomp_node (i,l,j) sk =
    if i < j then (l.(i), App (succ i,l,j) :: sk)
    else (l.(i), sk)

  let decomp = function
    | App node::s -> Some (decomp_node node s)
    | _ -> None

  let decomp_node_last (i,l,j) sk =
    if i < j then (l.(j), App (i,l,pred j) :: sk)
    else (l.(j), sk)

  let compare_shape stk1 stk2 =
    let rec compare_rec bal stk1 stk2 =
      match (stk1,stk2) with
	([],[]) -> Int.equal bal 0
      | ((Update _|Shift _)::s1, _) -> compare_rec bal s1 stk2
      | (_, (Update _|Shift _)::s2) -> compare_rec bal stk1 s2
      | (App (i,_,j)::s1, _) -> compare_rec (bal + j + 1 - i) s1 stk2
      | (_, App (i,_,j)::s2) -> compare_rec (bal - j - 1 + i) stk1 s2
      | (Case(c1,_,_,_)::s1, Case(c2,_,_,_)::s2) ->
        Int.equal bal 0 (* && c1.ci_ind  = c2.ci_ind *) && compare_rec 0 s1 s2
      | (Fix(_,a1,_)::s1, Fix(_,a2,_)::s2) ->
        Int.equal bal 0 && compare_rec 0 a1 a2 && compare_rec 0 s1 s2
      | (_,_) -> false in
    compare_rec 0 stk1 stk2

  let fold2 f o sk1 sk2 =
    let rec aux o lft1 sk1 lft2 sk2 =
      let fold_array =
	Array.fold_left2 (fun a x y -> f a (Vars.lift lft1 x) (Vars.lift lft2 y))
      in
      match sk1,sk2 with
      | [], [] -> o,lft1,lft2
      | Shift n :: q1, _ -> aux o (lft1+n) q1 lft2 sk2
      | _, Shift n :: q2 -> aux o lft1 sk1 (lft2+n) q2
      | App n1 :: q1, App n2 :: q2 ->
	 let t1,l1 = decomp_node_last n1 q1 in
	 let t2,l2 = decomp_node_last n2 q2 in
	 aux (f o (Vars.lift lft1 t1) (Vars.lift lft2 t2))
	     lft1 l1 lft2 l2
      | Case (_,t1,a1,_) :: q1, Case (_,t2,a2,_) :: q2 ->
	aux (fold_array
	       (f o (Vars.lift lft1 t1) (Vars.lift lft2 t2))
	       a1 a2) lft1 q1 lft2 q2
      | Fix ((_,(_,a1,b1)),s1,_) :: q1, Fix ((_,(_,a2,b2)),s2,_) :: q2 ->
	let (o',_,_) = aux (fold_array (fold_array o b1 b2) a1 a2)
	  lft1 s1 lft2 s2 in
	aux o' lft1 q1 lft2 q2
      | _, _ -> raise (Invalid_argument "Reductionops.Stack.fold2")
    in aux o 0 (List.rev sk1) 0 (List.rev sk2)

  let append_app_list l s =
    let a = Array.of_list l in
    append_app a s

  let rec args_size = function
    | App (i,_,j)::s -> j + 1 - i + args_size s
    | Shift(_)::s -> args_size s
    | Update(_)::s -> args_size s
    | _ -> 0

  let strip_app s =
    let rec aux out = function
      | ( App _ | Shift _ as e) :: s -> aux (e :: out) s
      | s -> List.rev out,s
    in aux [] s
  let strip_n_app n s =
    let rec aux n out = function
      | Shift k as e :: s -> aux n (e :: out) s
      | App (i,a,j) as e :: s ->
	 let nb = j  - i + 1 in
	 if n >= nb then
	   aux (n - nb) (e::out) s
	 else
	   let p = i+n in
	   Some (CList.rev
	      (if Int.equal n 0 then out else App (i,a,p-1) :: out),
	    a.(p),
	    if j > p then App(succ p,a,j)::s else s)
      | s -> None
    in aux n [] s

  let not_purely_applicative args =
    List.exists (function (Fix _ | Case _) -> true | _ -> false) args
  let list_of_app_stack s =
    let rec aux = function
      | App (i,a,j) :: s ->
	 let (k,(args',s')) = aux s in
	 let a' = Array.map (Vars.lift k) (Array.sub a i (j - i + 1)) in
	 k,(Array.fold_right (fun x y -> x::y) a' args', s')
      | Shift n :: s ->
	 let (k,(args',s')) = aux s in (k+n,(args', s'))
      | s -> (0,([],s)) in
    let (lft,(out,s')) = aux s in
    let init = match s' with [] when Int.equal lft 0 -> true | _ -> false in
    Option.init init out

  let assign s p c =
    match strip_n_app p s with
    | Some (pre,_,sk) -> pre @ (App (0,[|c|],0)::sk)
    | None -> assert false

  let tail n0 s0 =
    let rec aux lft n s =
      let out s = if Int.equal lft 0 then s else Shift lft :: s in
      if Int.equal n 0 then out s else
	match s with
      | App (i,a,j) :: s ->
	 let nb = j  - i + 1 in
	 if n >= nb then
	   aux lft (n - nb) s
	 else
	   let p = i+n in
	   if j >= p then App(p,a,j)::s else s
	| Shift k :: s' -> aux (lft+k) n s'
	| _ -> raise (Invalid_argument "Reductionops.Stack.tail")
    in aux 0 n0 s0

  let nth s p =
    match strip_n_app p s with
    | Some (_,el,_) -> el
    | None -> raise Not_found

  let rec zip ?(refold=false) = function
    | f, [] -> f
    | f, (App (i,a,j) :: s) ->
       let a' = if Int.equal i 0 && Int.equal j (Array.length a - 1)
		then a
		else Array.sub a i (j - i + 1) in
       zip ~refold (mkApp (f, a'), s)
    | f, (Case (ci,rt,br,Some(cst, params))::s) when refold ->
       zip ~refold (cst, append_app_list (List.rev params) s)
    | f, (Case (ci,rt,br,_)::s) -> zip ~refold (mkCase (ci,rt,f,br), s)
    | f, (Fix (fix,st,Some(cst, params))::s) when refold ->
       zip ~refold (cst, append_app_list (List.rev params)
      (st @ (append_app [|f|] s)))
  | f, (Fix (fix,st,_)::s) -> zip ~refold
    (mkFix fix, st @ (append_app [|f|] s))
  | f, (Shift n::s) -> zip ~refold (lift n f, s)
  | _ -> assert false
end

(** The type of (machine) states (= lambda-bar-calculus' cuts) *)
type state = constr * constr Stack.t

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

let pr_state (tm,sk) =
  let open Pp in
  h 0 (Termops.print_constr tm ++ str "|" ++ cut () ++ Stack.pr Termops.print_constr sk)

(*************************************)
(*** Reduction Functions Operators ***)
(*************************************)

let safe_evar_value sigma ev =
  try Some (Evd.existential_value sigma ev)
  with NotInstantiatedEvar | Not_found -> None

let safe_meta_value sigma ev =
  try Some (Evd.meta_value sigma ev)
  with Not_found -> None

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

(* Local *)
let nored = Closure.RedFlags.no_red
let beta = Closure.beta
let eta = Closure.RedFlags.mkflags [Closure.RedFlags.fETA]
let zeta = Closure.RedFlags.mkflags [Closure.RedFlags.fZETA]
let betaiota = Closure.betaiota
let betaiotazeta = Closure.betaiotazeta

(* Contextual *)
let delta = Closure.RedFlags.mkflags [Closure.RedFlags.fDELTA]
let betalet = Closure.RedFlags.mkflags [Closure.RedFlags.fBETA;Closure.RedFlags.fZETA]
let betaetalet = Closure.RedFlags.red_add betalet Closure.RedFlags.fETA
let betadelta = Closure.RedFlags.red_add betalet Closure.RedFlags.fDELTA
let betadeltaeta = Closure.RedFlags.red_add betadelta Closure.RedFlags.fETA
let betadeltaiota = Closure.RedFlags.red_add betadelta Closure.RedFlags.fIOTA
let betadeltaiota_nolet = Closure.betadeltaiotanolet
let betadeltaiotaeta = Closure.RedFlags.red_add betadeltaiota Closure.RedFlags.fETA

(** Machinery about stack of unfolded constants *)
module Cst_stack = struct
  type t = (Term.constr * Term.constr list * int)  list

  let empty = []

  let drop_useless = function
    | _ :: ((_,_,0)::_ as q) -> q
    | l -> l

  let add_param h cst_l =
    let append2cst (c,params,nb_skip) =
      if nb_skip <= 0
      then (c, h::params, nb_skip)
      else (c, params, pred nb_skip) in
    drop_useless (List.map append2cst cst_l)

  let add_args cl =
    List.map (fun (a,b,nb_skip) -> (a,b,nb_skip+Array.length cl))

  let add_cst cst = function
    | (_,_,0) :: q as l -> l
    | l -> (cst,[],0)::l

  let best_cst = function
    | (cst,params,0)::_ -> Some(cst,params)
    | _ -> None
end

(* Beta Reduction tools *)

let apply_subst recfun env cst_l t stack =
  let rec aux env cst_l t stack =
    match (Stack.decomp stack,kind_of_term t) with
    | Some (h,stacktl), Lambda (_,_,c) ->
      aux (h::env) (Cst_stack.add_param h cst_l) c stacktl
    | _ -> recfun cst_l (substl env t, stack)
  in aux env cst_l t stack

let rec stacklam recfun env t stack =
apply_subst (fun _ -> recfun) env [] t stack

let beta_applist (c,l) =
  stacklam Stack.zip [] c (Stack.append_app_list l Stack.empty)

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

(** @return c if there is a constant c whose body is bd
    @return bd else.

    It has only a meaning because internal representation of "Fixpoint f x
    := t" is Definition f := fix f x => t

    Even more fragile that we could hope because do Module M. Fixpoint
    f x := t. End M. Definition f := u. and say goodbye to any hope
    of refolding M.f this way ...
*)
let magicaly_constant_of_fixbody env bd = function
  | Name.Anonymous -> bd
  | Name.Name id ->
    try
      let cst = Nametab.locate_constant
	(Libnames.make_qualid DirPath.empty id) in
      match constant_opt_value env cst with
      | None -> bd
      | Some t -> if eq_constr t bd then mkConst cst else bd
    with
    | Not_found -> bd

let contract_cofix ?env (bodynum,(names,types,bodies as typedbodies)) cst =
  let nbodies = Array.length bodies in
  let make_Fi j =
    let ind = nbodies-j-1 in
    if Int.equal bodynum ind && not (Option.is_empty cst) then
      let (c,params) = Option.get cst in
      applist(c, List.rev params)
    else
      let bd = mkCoFix (ind,typedbodies) in
      match env with
      | None -> bd
      | Some e -> magicaly_constant_of_fixbody e bd names.(ind) in
  let closure = List.init nbodies make_Fi in
  substl closure bodies.(bodynum)

let reduce_mind_case mia =
  match kind_of_term mia.mconstr with
    | Construct (ind_sp,i) ->
(*	let ncargs = (fst mia.mci).(i-1) in*)
	let real_cargs = List.skipn mia.mci.ci_npar mia.mcargs in
        applist (mia.mlf.(i-1),real_cargs)
    | CoFix cofix ->
	let cofix_def = contract_cofix cofix None in
	mkCase (mia.mci, mia.mP, applist(cofix_def,mia.mcargs), mia.mlf)
    | _ -> assert false

(* contracts fix==FIX[nl;i](A1...Ak;[F1...Fk]{B1....Bk}) to produce
   Bi[Fj --> FIX[nl;j](A1...Ak;[F1...Fk]{B1...Bk})] *)

let contract_fix ?env ((recindices,bodynum),(names,types,bodies as typedbodies)) cst =
    let nbodies = Array.length recindices in
    let make_Fi j =
      let ind = nbodies-j-1 in
      if Int.equal bodynum ind && not (Option.is_empty cst) then
	let (c,params) = Option.get cst in
	applist(c, List.rev params)
      else
	let bd = mkFix ((recindices,ind),typedbodies) in
	match env with
	| None -> bd
	| Some e -> magicaly_constant_of_fixbody e bd names.(ind) in
    let closure = List.init nbodies make_Fi in
    substl closure bodies.(bodynum)

let fix_recarg ((recindices,bodynum),_) stack =
  assert (0 <= bodynum && bodynum < Array.length recindices);
  let recargnum = Array.get recindices bodynum in
  try
    Some (recargnum, Stack.nth stack recargnum)
  with Not_found ->
    None

(** Generic reduction function with environment

    Here is where unfolded constant are stored in order to be
    eventualy refolded.

    It uses the flag refold when it reaches a value and because it
    substitutes fix and cofix by the constant they come from in
    contract_*.
*)
let rec whd_state_gen ?csts refold flags env sigma =
  let noth = [] in
  let rec whrec cst_l (x, stack as s) =
    let best_state def (cst,params,nb_skip) =
      try
	let s' = Stack.tail nb_skip stack in
	(cst, Stack.append_app_list (List.rev params) s')
      with Failure _ -> def in
    let fold () =
      if refold then (List.fold_left best_state s cst_l,noth) else (s,cst_l)
    in
    match kind_of_term x with
    | Rel n when Closure.RedFlags.red_set flags Closure.RedFlags.fDELTA ->
      (match lookup_rel n env with
      | (_,Some body,_) -> whrec noth (lift n body, stack)
      | _ -> fold ())
    | Var id when Closure.RedFlags.red_set flags (Closure.RedFlags.fVAR id) ->
      (match lookup_named id env with
      | (_,Some body,_) -> whrec (Cst_stack.add_cst (mkVar id) cst_l) (body, stack)
      | _ -> fold ())
    | Evar ev ->
      (match safe_evar_value sigma ev with
      | Some body -> whrec cst_l (body, stack)
      | None -> fold ())
    | Meta ev ->
      (match safe_meta_value sigma ev with
      | Some body -> whrec cst_l (body, stack)
      | None -> fold ())
    | Const const when Closure.RedFlags.red_set flags (Closure.RedFlags.fCONST const) ->
      (match constant_opt_value env const with
      | Some  body -> whrec (Cst_stack.add_cst (mkConst const) cst_l) (body, stack)
      | None -> fold ())
    | LetIn (_,b,_,c) when Closure.RedFlags.red_set flags Closure.RedFlags.fZETA ->
      apply_subst whrec [b] cst_l c stack
    | Cast (c,_,_) -> whrec cst_l (c, stack)
    | App (f,cl)  ->
      whrec
	(Cst_stack.add_args cl cst_l)
	(f, Stack.append_app cl stack)
    | Lambda (na,t,c) ->
      (match Stack.decomp stack with
      | Some _ when Closure.RedFlags.red_set flags Closure.RedFlags.fBETA ->
	apply_subst whrec [] cst_l x stack
      | None when Closure.RedFlags.red_set flags Closure.RedFlags.fETA ->
	let env' = push_rel (na,None,t) env in
	let whrec' = whd_state_gen refold flags env' sigma in
        (match kind_of_term (Stack.zip ~refold (fst (whrec' (c, Stack.empty)))) with
        | App (f,cl) ->
	  let napp = Array.length cl in
	  if napp > 0 then
	    let (x', l'),_ = whrec' (Array.last cl, Stack.empty) in
            match kind_of_term x', l' with
            | Rel 1, [] ->
	      let lc = Array.sub cl 0 (napp-1) in
	      let u = if Int.equal napp 1 then f else appvect (f,lc) in
	      if noccurn 1 u then (pop u,Stack.empty),noth else fold ()
            | _ -> fold ()
	  else fold ()
	| _ -> fold ())
      | _ -> fold ())

    | Case (ci,p,d,lf) ->
      whrec noth (d, Stack.Case (ci,p,lf,Cst_stack.best_cst cst_l) :: stack)

    | Fix ((ri,n),_ as f) ->
      (match Stack.strip_n_app ri.(n) stack with
      |None -> fold ()
      |Some (bef,arg,s') ->
	whrec noth (arg, Stack.Fix(f,bef,Cst_stack.best_cst cst_l)::s'))

    | Construct (ind,c) ->
      if Closure.RedFlags.red_set flags Closure.RedFlags.fIOTA then
	match Stack.strip_app stack with
	|args, (Stack.Case(ci, _, lf,_)::s') ->
	  whrec noth (lf.(c-1), (Stack.tail ci.ci_npar args) @ s')
	|args, (Stack.Fix (f,s',cst)::s'') ->
	  let x' = Stack.zip(x,args) in
	  whrec noth ((if refold then contract_fix ~env f else contract_fix f) cst,
		      s' @ (Stack.append_app [|x'|] s''))
	|_ -> fold ()
      else fold ()

    | CoFix cofix ->
      if Closure.RedFlags.red_set flags Closure.RedFlags.fIOTA then
	match Stack.strip_app stack with
	|args, (Stack.Case(ci, _, lf,_)::s') ->
	  whrec noth ((if refold
	    then contract_cofix ~env cofix
	    else contract_cofix cofix) (Cst_stack.best_cst cst_l), stack)
	|_ -> fold ()
      else fold ()

    | Rel _ | Var _ | Const _ | LetIn _ -> fold ()
    | Sort _ | Ind _ | Prod _ -> fold ()
  in
  whrec (Option.default noth csts)

(** reduction machine without global env and refold machinery *)
let local_whd_state_gen flags sigma =
  let rec whrec (x, stack as s) =
    match kind_of_term x with
    | LetIn (_,b,_,c) when Closure.RedFlags.red_set flags Closure.RedFlags.fZETA ->
      stacklam whrec [b] c stack
    | Cast (c,_,_) -> whrec (c, stack)
    | App (f,cl)  -> whrec (f, Stack.append_app cl stack)
    | Lambda (_,_,c) ->
      (match Stack.decomp stack with
      | Some (a,m) when Closure.RedFlags.red_set flags Closure.RedFlags.fBETA ->
	stacklam whrec [a] c m
      | None when Closure.RedFlags.red_set flags Closure.RedFlags.fETA ->
        (match kind_of_term (Stack.zip (whrec (c, Stack.empty))) with
        | App (f,cl) ->
	  let napp = Array.length cl in
	  if napp > 0 then
	    let x', l' = whrec (Array.last cl, Stack.empty) in
            match kind_of_term x', l' with
            | Rel 1, [] ->
	      let lc = Array.sub cl 0 (napp-1) in
	      let u = if Int.equal napp 1 then f else appvect (f,lc) in
	      if noccurn 1 u then (pop u,Stack.empty) else s
            | _ -> s
	  else s
	| _ -> s)
      | _ -> s)

    | Case (ci,p,d,lf) ->
      whrec (d, Stack.Case (ci,p,lf,None) :: stack)

    | Fix ((ri,n),_ as f) ->
      (match Stack.strip_n_app ri.(n) stack with
      |None -> s
      |Some (bef,arg,s') -> whrec (arg, Stack.Fix(f,bef,None)::s'))

    | Evar ev ->
      (match safe_evar_value sigma ev with
        Some c -> whrec (c,stack)
      | None -> s)

    | Meta ev ->
      (match safe_meta_value sigma ev with
        Some c -> whrec (c,stack)
      | None -> s)

    | Construct (ind,c) ->
      if Closure.RedFlags.red_set flags Closure.RedFlags.fIOTA then
	match Stack.strip_app stack with
	|args, (Stack.Case(ci, _, lf,_)::s') ->
	  whrec (lf.(c-1), (Stack.tail ci.ci_npar args) @ s')
	|args, (Stack.Fix (f,s',cst)::s'') ->
	  let x' = Stack.zip(x,args) in
	  whrec (contract_fix f cst, s' @ (Stack.append_app [|x'|] s''))
	|_ -> s
      else s

    | CoFix cofix ->
      if Closure.RedFlags.red_set flags Closure.RedFlags.fIOTA then
	match Stack.strip_app stack with
	|args, (Stack.Case(ci, _, lf,_)::s') ->
	  whrec (contract_cofix cofix None, stack)
	|_ -> s
      else s

    | x -> s
  in
  whrec

let raw_whd_state_gen flags env =
  let f sigma s = fst (whd_state_gen false flags env sigma s) in
  f

let stack_red_of_state_red f =
  let f sigma x = decompose_app (Stack.zip (f sigma (x, Stack.empty))) in
  f

let red_of_state_red f sigma x =
  Stack.zip (f sigma (x,Stack.empty))

(* 0. No Reduction Functions *)

let whd_nored_state = local_whd_state_gen nored
let whd_nored_stack = stack_red_of_state_red whd_nored_state
let whd_nored = red_of_state_red whd_nored_state

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

let whd_delta_state e = raw_whd_state_gen delta e
let whd_delta_stack env = stack_red_of_state_red (whd_delta_state env)
let whd_delta env = red_of_state_red  (whd_delta_state env)

let whd_betadelta_state e = raw_whd_state_gen betadelta e
let whd_betadelta_stack env =
  stack_red_of_state_red (whd_betadelta_state env)
let whd_betadelta env =
  red_of_state_red (whd_betadelta_state env)


let whd_betadeltaeta_state e = raw_whd_state_gen betadeltaeta e
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

let whd_betadeltaiota_state env = raw_whd_state_gen betadeltaiota env
let whd_betadeltaiota_stack env =
  stack_red_of_state_red (whd_betadeltaiota_state env)
let whd_betadeltaiota env =
  red_of_state_red (whd_betadeltaiota_state env)

let whd_betadeltaiota_state_using ts env =
  raw_whd_state_gen (Closure.RedFlags.red_add_transparent betadeltaiota ts) env
let whd_betadeltaiota_stack_using ts env =
  stack_red_of_state_red (whd_betadeltaiota_state_using ts env)
let whd_betadeltaiota_using ts env =
  red_of_state_red (whd_betadeltaiota_state_using ts env)

let whd_betadeltaiotaeta_state env = raw_whd_state_gen betadeltaiotaeta env
let whd_betadeltaiotaeta_stack env =
  stack_red_of_state_red (whd_betadeltaiotaeta_state env)
let whd_betadeltaiotaeta env =
  red_of_state_red (whd_betadeltaiotaeta_state env)

let whd_betadeltaiota_nolet_state env = raw_whd_state_gen betadeltaiota_nolet env
let whd_betadeltaiota_nolet_stack env =
  stack_red_of_state_red (whd_betadeltaiota_nolet_state env)
let whd_betadeltaiota_nolet env =
  red_of_state_red (whd_betadeltaiota_nolet_state env)

(* 4. Eta reduction Functions *)

let whd_eta c = Stack.zip (local_whd_state_gen eta Evd.empty (c,Stack.empty))

(* 5. Zeta Reduction Functions *)

let whd_zeta c = Stack.zip (local_whd_state_gen zeta Evd.empty (c,Stack.empty))

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
  try
    let evars ev = safe_evar_value sigma ev in
    Closure.norm_val
      (Closure.create_clos_infos ~evars flgs env)
      (Closure.inject t)
  with e when is_anomaly e -> error "Tried to normalize ill-typed term"

let nf_beta = clos_norm_flags Closure.beta empty_env
let nf_betaiota = clos_norm_flags Closure.betaiota empty_env
let nf_betaiotazeta = clos_norm_flags Closure.betaiotazeta empty_env
let nf_betadeltaiota env sigma =
  clos_norm_flags Closure.betadeltaiota env sigma


(* Attention reduire un beta-redexe avec un argument qui n'est pas
   une variable, peut changer enormement le temps de conversion lors
   du type checking :
     (fun x => x + x) M
*)
let whd_betaiota_preserving_vm_cast env sigma t =
   let rec stacklam_var subst t stack =
     match (Stack.decomp stack,kind_of_term t) with
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
           let c = Stack.zip (whrec (c,Stack.empty)) in
           let t = Stack.zip (whrec (t,Stack.empty)) in
           (mkCast(c,VMcast,t),stack)
       | Cast (c,NATIVEcast,t) ->
           let c = Stack.zip (whrec (c,Stack.empty)) in
           let t = Stack.zip (whrec (t,Stack.empty)) in
           (mkCast(c,NATIVEcast,t),stack)
       | Cast (c,DEFAULTcast,_) ->
           whrec (c, stack)
       | App (f,cl)  -> whrec (f, Stack.append_app cl stack)
       | Lambda (na,t,c) ->
           (match Stack.decomp stack with
            | Some (a,m) -> stacklam_var [a] c m
            | _ -> s)
       | Case (ci,p,d,lf) ->
	 whrec (d, Stack.Case (ci,p,lf,None) :: stack)

       | Construct (ind,c) -> begin
	 match Stack.strip_app stack with
	   |args, (Stack.Case(ci, _, lf,_)::s') ->
	     whrec (lf.(c-1), (Stack.tail ci.ci_npar args) @ s')
	   |args, (Stack.Fix (f,s',cst)::s'') ->
	     let x' = Stack.zip(x,args) in
	     whrec (contract_fix f cst,s' @ (Stack.append_app [|x'|] s''))
	   |_ -> s
       end

       | CoFix cofix -> begin
	 match Stack.strip_app stack with
	   |args, (Stack.Case(ci, _, lf,_)::s') ->
	     whrec (contract_cofix cofix None, stack)
	   |_ -> s
       end

       | x -> s
   in
   Stack.zip (whrec (t,Stack.empty))

let nf_betaiota_preserving_vm_cast =
  strong whd_betaiota_preserving_vm_cast

(********************************************************************)
(*                         Conversion                               *)
(********************************************************************)
(*
let fkey = Profile.declare_profile "fhnf";;
let fhnf info v = Profile.profile2 fkey fhnf info v;;

let fakey = Profile.declare_profile "fhnf_apply";;
let fhnf_apply info k h a = Profile.profile4 fakey fhnf_apply info k h a;;
*)

let is_transparent e k =
  match Conv_oracle.get_strategy (Environ.oracle e) k with
  | Conv_oracle.Opaque -> false
  | _ -> true

(* Conversion utility functions *)

type conversion_test = constraints -> constraints

let pb_is_equal pb = pb == Reduction.CONV

let pb_equal = function
  | Reduction.CUMUL -> Reduction.CONV
  | Reduction.CONV -> Reduction.CONV

let sort_cmp = Reduction.sort_cmp

let test_conversion (f: ?l2r:bool-> ?evars:'a->'b) env sigma x y =
  try
    let evars ev = safe_evar_value sigma ev in
    let _ = f ~evars env x y in
    true
  with Reduction.NotConvertible -> false
    | e when is_anomaly e -> error "Conversion test raised an anomaly"

let is_conv env sigma = test_conversion Reduction.conv env sigma
let is_conv_leq env sigma = test_conversion Reduction.conv_leq env sigma
let is_fconv = function | Reduction.CONV -> is_conv | Reduction.CUMUL -> is_conv_leq

let test_trans_conversion (f: ?l2r:bool-> ?evars:'a->'b) reds env sigma x y =
  try
    let evars ev = safe_evar_value sigma ev in
    let _ = f ~evars reds env x y in
    true
  with Reduction.NotConvertible -> false
    | e when is_anomaly e -> error "Conversion test raised an anomaly"

let is_trans_conv reds env sigma = test_trans_conversion Reduction.trans_conv reds env sigma
let is_trans_conv_leq reds env sigma = test_trans_conversion Reduction.trans_conv_leq reds env sigma
let is_trans_fconv = function | Reduction.CONV -> is_trans_conv | Reduction.CUMUL -> is_trans_conv_leq

(********************************************************************)
(*             Special-Purpose Reduction                            *)
(********************************************************************)

let whd_meta sigma c = match kind_of_term c with
  | Meta p -> (try meta_value sigma p with Not_found -> c)
  | _ -> c

let hid = Id.of_string "H"

(* Try to replace all metas. Does not replace metas in the metas' values
 * Differs from (strong whd_meta). *)
let plain_instance s c =
  let rec irec n u = match kind_of_term u with
    | Meta p -> (try lift n (Metamap.find p s) with Not_found -> u)
    | App (f,l) when isCast f ->
        let (f,_,t) = destCast f in
        let l' = CArray.Fun1.smartmap irec n l in
        (match kind_of_term f with
        | Meta p ->
	    (* Don't flatten application nodes: this is used to extract a
               proof-term from a proof-tree and we want to keep the structure
               of the proof-tree *)
	    (try let g = Metamap.find p s in
	    match kind_of_term g with
            | App _ ->
                let l' = CArray.Fun1.smartmap lift 1 l' in
                mkLetIn (Name hid,g,t,mkApp(mkRel 1, l'))
            | _ -> mkApp (g,l')
	    with Not_found -> mkApp (f,l'))
        | _ -> mkApp (irec n f,l'))
    | Cast (m,_,_) when isMeta m ->
	(try lift n (Metamap.find (destMeta m) s) with Not_found -> u)
    | _ ->
	map_constr_with_binders succ irec n u
  in
  if Metamap.is_empty s then c
  else irec 0 c

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
    | _ -> anomaly ~label:"hnf_prod_app" (Pp.str "Need a product")

let hnf_prod_appvect env sigma t nl =
  Array.fold_left (hnf_prod_app env sigma) t nl

let hnf_prod_applist env sigma t nl =
  List.fold_left (hnf_prod_app env sigma) t nl

let hnf_lam_app env sigma t n =
  match kind_of_term (whd_betadeltaiota env sigma t) with
    | Lambda (_,_,b) -> subst1 n b
    | _ -> anomaly ~label:"hnf_lam_app" (Pp.str "Need an abstraction")

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

let sort_of_arity env sigma c = snd (splay_arity env sigma c)

let splay_prod_n env sigma n =
  let rec decrec env m ln c = if Int.equal m 0 then (ln,c) else
    match kind_of_term (whd_betadeltaiota env sigma c) with
      | Prod (n,a,c0) ->
	  decrec (push_rel (n,None,a) env)
	    (m-1) (add_rel_decl (n,None,a) ln) c0
      | _                      -> invalid_arg "splay_prod_n"
  in
  decrec env n empty_rel_context

let splay_lam_n env sigma n =
  let rec decrec env m ln c = if Int.equal m 0 then (ln,c) else
    match kind_of_term (whd_betadeltaiota env sigma c) with
      | Lambda (n,a,c0) ->
	  decrec (push_rel (n,None,a) env)
	    (m-1) (add_rel_decl (n,None,a) ln) c0
      | _                      -> invalid_arg "splay_lam_n"
  in
  decrec env n empty_rel_context

let is_sort env sigma t =
  match kind_of_term (whd_betadeltaiota env sigma t) with
  | Sort s -> true
  | _ -> false

(* reduction to head-normal-form allowing delta/zeta only in argument
   of case/fix (heuristic used by evar_conv) *)

let whd_betaiota_deltazeta_for_iota_state ts env sigma csts s =
  let rec whrec csts s =
    let (t, stack as s),csts' = whd_state_gen ~csts false betaiota env sigma s in
    match Stack.strip_app stack with
      |args, (Stack.Case _ :: _ as stack') ->
	let (t_o,stack_o),csts_o = whd_state_gen ~csts:csts' false
	  (Closure.RedFlags.red_add_transparent betadeltaiota ts) env sigma (t,args) in
	if reducible_mind_case t_o then whrec csts_o (t_o, stack_o@stack') else s,csts'
      |args, (Stack.Fix _ :: _ as stack') ->
	let (t_o,stack_o),csts_o = whd_state_gen ~csts:csts' false
	  (Closure.RedFlags.red_add_transparent betadeltaiota ts) env sigma (t,args) in
	if isConstruct t_o then whrec csts_o (t_o, stack_o@stack') else s,csts'
      |_ -> s,csts'
  in whrec csts s

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
	    whrec (mkApp (f, Array.sub cl 0 n), Stack.append_app [|c|] stack)
      | LetIn (_,b,_,c) ->
	  if occur_existential b then
	    s
	  else
	    stacklam whrec [b] c stack
      | Lambda (_,_,c) ->
          (match Stack.decomp stack with
             | None -> s
             | Some (a,m) -> stacklam whrec [a] c m)
      | Case (ci,p,d,lf) ->
	  if occur_existential d then
	    s
	  else
	    whrec (d, Stack.Case (ci,p,lf,None) :: stack)
      | Fix ((ri,n),_ as f) ->
	(match Stack.strip_n_app ri.(n) stack with
	  |None -> s
	  |Some (bef,arg,s') -> whrec (arg, Stack.Fix(f,bef,None)::s'))
      | Construct (ind,c) -> begin
	match Stack.strip_app stack with
	  |args, (Stack.Case(ci, _, lf,_)::s') ->
	    whrec (lf.(c-1), (Stack.tail ci.ci_npar args) @ s')
	  |args, (Stack.Fix (f,s',cst)::s'') ->
	    let x' = Stack.zip(x,args) in
	    whrec (contract_fix f cst,s' @ (Stack.append_app [|x'|] s''))
	  |_ -> s
      end
      | CoFix cofix -> begin
	match Stack.strip_app stack with
	  |args, (Stack.Case(ci, _, lf,_)::s') ->
	     whrec (contract_cofix cofix None, stack)
	  |_ -> s
      end
      | _ -> s
  in
  whrec

let whd_programs env sigma x =
  Stack.zip (whd_programs_stack env sigma (x, Stack.empty))

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
      let metas = Metamap.bind valrec b.freemetas in
      instance evd metas b.rebus
    | None -> mkMeta mv
  in
  valrec mv

let meta_instance sigma b =
  let fm = b.freemetas in
  if Metaset.is_empty fm then b.rebus
  else
    let c_sigma = Metamap.bind (fun mv -> meta_value sigma mv) fm in
    instance sigma c_sigma b.rebus

let nf_meta sigma c = meta_instance sigma (mk_freelisted c)

(* Instantiate metas that create beta/iota redexes *)

let meta_reducible_instance evd b =
  let fm = b.freemetas in
  let fold mv accu =
    let fvalue = try meta_opt_fvalue evd mv with Not_found -> None in
    match fvalue with
    | None -> accu
    | Some (g, (_, s)) -> Metamap.add mv (g.rebus, s) accu
  in
  let metas = Metaset.fold fold fm Metamap.empty in
  let rec irec u =
    let u = whd_betaiota Evd.empty u in
    match kind_of_term u with
    | Case (ci,p,c,bl) when isMeta (strip_outer_cast c) ->
	let m = destMeta (strip_outer_cast c) in
	(match
	  try
	    let g, s = Metamap.find m metas in
            let is_coerce = match s with CoerceToType -> true | _ -> false in
	    if isConstruct g || not is_coerce then Some g else None
	  with Not_found -> None
	  with
	    | Some g -> irec (mkCase (ci,p,g,bl))
	    | None -> mkCase (ci,irec p,c,Array.map irec bl))
    | App (f,l) when isMeta (strip_outer_cast f) ->
	let m = destMeta (strip_outer_cast f) in
	(match
	  try
	    let g, s = Metamap.find m metas in
            let is_coerce = match s with CoerceToType -> true | _ -> false in
	    if isLambda g || not is_coerce then Some g else None
	  with Not_found -> None
	 with
	   | Some g -> irec (mkApp (g,l))
	   | None -> mkApp (f,Array.map irec l))
    | Meta m ->
	(try let g, s = Metamap.find m metas in
          let is_coerce = match s with CoerceToType -> true | _ -> false in
          if not is_coerce then irec g else u
	 with Not_found -> u)
    | _ -> map_constr irec u
  in
  if Metaset.is_empty fm then (* nf_betaiota? *) b.rebus
  else irec b.rebus


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
