
(* $Id$ *)

open Pp
open Util
open Names
(* open Generic *)
open Term
open Univ
open Evd
open Declarations
open Environ
open Instantiate
open Closure

exception Elimconst

(* The type of (machine) stacks (= lambda-bar-calculus' contexts) *) 
type stack =
  | EmptyStack
  | ConsStack of constr array * int * stack

(* The type of (machine) states (= lambda-bar-calculus' cuts) *) 
type state = constr * stack

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

let empty_stack = EmptyStack

let decomp_stack = function
  | EmptyStack -> None
  | ConsStack (v, n, s) ->
      Some (v.(n), (if n+1 = Array.length v then s else ConsStack (v, n+1, s)))

let append_stack v s = if Array.length v = 0 then s else ConsStack (v,0,s)

let rec app_stack = function
  | f, EmptyStack -> f
  | f, ConsStack (v, n, s) -> 
      let args = if n=0 then v else Array.sub v n (Array.length v - n) in
      app_stack (appvect (f, args), s)

let rec list_of_stack = function
  | EmptyStack -> []
  | ConsStack (v, n, s) ->
      let args = if n=0 then v else  Array.sub v n (Array.length v - n) in
      Array.fold_right (fun a l -> a::l) args (list_of_stack s)

let appterm_of_stack (f,s) = (f,list_of_stack s)

let rec stack_assign s p c = match s with
  | EmptyStack -> EmptyStack
  | ConsStack (v, n, s) ->
      let q = Array.length v - n in 
      if p >= q then
	ConsStack (v, n, stack_assign s (p-q) c)
      else
	let v' = Array.sub v n q in
	v'.(p) <- c;
	ConsStack (v', 0, s)

let rec stack_nth s p = match s with
  | EmptyStack -> raise Not_found
  | ConsStack (v, n, s) ->
      let q = Array.length v - n in
      if p >= q then stack_nth s (p-q)
      else v.(p+n)

let rec stack_args_size = function
  | EmptyStack -> 0
  | ConsStack (v, n, s) -> Array.length v - n + stack_args_size s


(* Version avec listes
type stack = constr list

let decomp_stack = function
  | [] -> None
  | v :: s -> Some (v,s)

let append_stack v s = v@s
*)
(*************************************)
(*** Reduction Functions Operators ***)
(*************************************)

let rec whd_state (x, stack as s) =
  match kind_of_term x with
    | IsApp (f,cl) -> whd_state (f, append_stack cl stack)
    | IsCast (c,_)  -> whd_state (c, stack)
    | _             -> s

let whd_stack x = appterm_of_stack (whd_state (x, empty_stack))
let whd_castapp_stack = whd_stack

let stack_reduction_of_reduction red_fun env sigma s =
  let t = red_fun env sigma (app_stack s) in
  whd_stack t

(* BUGGE : NE PREND PAS EN COMPTE LES DEFS LOCALES *)
let strong whdfun env sigma = 
  let rec strongrec t = map_constr strongrec (whdfun env sigma t) in
  strongrec

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

let nf_beta env = clos_norm_flags beta env
let nf_betaiota env = clos_norm_flags betaiota env
let nf_betadeltaiota env =  clos_norm_flags betadeltaiota env

(* lazy weak head reduction functions *)
(* Pb: whd_val parcourt tout le terme, meme si aucune reduction n'a lieu *)
let whd_flags flgs env sigma t =
  whd_val (create_clos_infos flgs env sigma) (inject t)

(*************************************)
(*** Reduction using substitutions ***)
(*************************************)

(* Naive Implementation
type flags = BETA | DELTA | EVAR | IOTA

let red_beta = List.mem BETA
let red_delta = List.mem DELTA
let red_evar = List.mem EVAR
let red_eta = List.mem ETA
let red_iota = List.mem IOTA

(* Local *)
let beta = [BETA]
let betaevar = [BETA;EVAR]
let betaiota = [BETA;IOTA]

(* Contextual *)
let delta = [DELTA;EVAR]
let betadelta = [BETA;DELTA;EVAR]
let betadeltaeta = [BETA;DELTA;EVAR;ETA]
let betadeltaiota = [BETA;DELTA;EVAR;IOTA]
let betadeltaiotaeta = [BETA;DELTA;EVAR;IOTA;ETA]
let betaiotaevar = [BETA;IOTA;EVAR]
let betaeta = [BETA;ETA]
*)

(* Compact Implementation *)
type flags = int
let fbeta = 1 and fdelta = 2 and fevar = 4 and feta = 8 and fiota = 16
							and fletin = 32

let red_beta f = f land fbeta <> 0
let red_delta f = f land fdelta <> 0
let red_evar f = f land fevar <> 0
let red_eta f = f land feta <> 0
let red_iota f = f land fiota <> 0
let red_letin f = f land fletin <> 0


(* Local *)
let beta = fbeta
let betaevar = fbeta lor fevar
let betaiota = fbeta lor fiota

(* Contextual *)
let delta = fdelta lor fevar
let betadelta = fbeta lor fdelta lor fletin lor fevar
let betadeltaeta = fbeta lor fdelta lor fletin lor fevar lor feta
let betadeltaiota = fbeta lor fdelta lor fletin lor fevar lor fiota
let betadeltaiota_nolet = fbeta lor fdelta lor fevar lor fiota
let betadeltaiotaeta = fbeta lor fdelta lor fletin lor fevar lor fiota lor feta
let betaiotaevar = fbeta lor fiota lor fevar
let betaetalet = fbeta lor feta lor fletin

(* Beta Reduction tools *)

let rec stacklam recfun env t stack =
  match (decomp_stack stack,kind_of_term t) with
    | Some (h,stacktl), IsLambda (_,_,c) -> stacklam recfun (h::env) c stacktl
    | _ -> recfun (substl env t, stack)

let beta_applist (c,l) =
  stacklam app_stack [] c (append_stack (Array.of_list l) EmptyStack)

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
    | IsMutConstruct (ind_sp,i as cstr_sp, args) ->
	let ncargs = (fst mia.mci).(i-1) in
	let real_cargs = list_lastn ncargs mia.mcargs in
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
  if 0 <= bodynum & bodynum < Array.length recindices then
    let recargnum = Array.get recindices bodynum in
    (try 
       Some (recargnum, stack_nth stack recargnum)
     with Not_found ->
       None)
  else 
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

let whd_state_gen flags env sigma = 
  let rec whrec (x, stack as s) =
    match kind_of_term x with
(*
      | IsRel n when red_delta flags ->
	  (match lookup_rel_value n env with
	     | Some body -> whrec (lift n body, stack)
	     | None -> s)
      | IsVar id when red_delta flags ->
	  (match lookup_var_value id env with
	     | Some body -> whrec (body, stack)
	     | None -> s)
*)
      | IsEvar ev when red_evar flags ->
	  (match existential_opt_value sigma ev with
	     | Some body -> whrec (body, stack)
	     | None -> s)
      | IsConst const when red_delta flags ->
	  (match constant_opt_value env const with
	     | Some  body -> whrec (body, stack)
	     | None -> s)
      | IsLetIn (_,b,_,c) when red_letin flags -> stacklam whrec [b] c stack
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

let local_whd_state_gen flags = 
  let rec whrec (x, stack as s) =
    match kind_of_term x with
      | IsLetIn (_,b,_,c) when red_delta flags -> stacklam whrec [b] c stack
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
(*
let whd_beta_state =
  let rec whrec (x, stack as s) =
    match kind_of_term x with
      | IsLambda (name,c1,c2) ->
	  (match decomp_stack stack with
             | None -> (x,empty_stack)
	     | Some (a1,rest) -> stacklam whrec [a1] c2 rest)

      | IsCast (c,_) -> whrec (c, stack)
      | IsApp (f,cl) -> whrec (f, append_stack cl stack)
      | x -> s
  in
  whrec
*)

let whd_beta_state = local_whd_state_gen beta
let whd_beta_stack x = appterm_of_stack (whd_beta_state (x, empty_stack))
let whd_beta x = app_stack (whd_beta_state (x,empty_stack))

(* Nouveau ! *)
let whd_betaetalet_state = local_whd_state_gen betaetalet
let whd_betaetalet_stack x =
  appterm_of_stack (whd_betaetalet_state (x, empty_stack))
let whd_betaetalet x = app_stack (whd_betaetalet_state (x,empty_stack))

(* 2. Delta Reduction Functions *)

(*
let whd_delta_state env sigma = 
  let rec whrec (x, l as s) =
    match kind_of_term x with
      | IsConst const when evaluable_constant env const ->
	  whrec (constant_value env const, l)
      | IsEvar (ev,args) when Evd.is_defined sigma ev ->
          whrec (existential_value sigma (ev,args), l)
      | IsLetIn (_,b,_,c) -> stacklam whrec [b] c l
      | IsCast (c,_) -> whrec (c, l)
      | IsApp (f,cl) -> whrec (f, append_stack cl l)
      | x -> s
  in 
  whrec
*)

let whd_delta_state e = whd_state_gen delta e
let whd_delta_stack env sigma x =
  appterm_of_stack (whd_delta_state env sigma (x, empty_stack))
let whd_delta env sigma c =
  app_stack (whd_delta_state env sigma (c, empty_stack))

(*
let whd_betadelta_state env sigma = 
  let rec whrec (x, l as s) =
    match kind_of_term x with
      | IsConst const ->
          if evaluable_constant env const then 
	    whrec (constant_value env const, l)
          else 
	    s
      | IsEvar (ev,args) ->
          if Evd.is_defined sigma ev then 
	    whrec (existential_value sigma (ev,args), l)
          else 
	    s
      | IsLetIn (_,b,_,c) -> stacklam whrec [b] c l
      | IsCast (c,_) -> whrec (c, l)
      | IsApp (f,cl)  -> whrec (f, append_stack cl l)
      | IsLambda (_,_,c) ->
          (match decomp_stack l with
             | None -> s
             | Some (a,m) -> stacklam whrec [a] c m)
      | x -> s
  in 
  whrec
*)

let whd_betadelta_state e = whd_state_gen betadelta e
let whd_betadelta_stack env sigma x =
  appterm_of_stack (whd_betadelta_state env sigma (x, empty_stack))
let whd_betadelta env sigma c =
  app_stack (whd_betadelta_state env sigma (c, empty_stack))


(*
let whd_betaevar_stack env sigma = 
  let rec whrec (x, l as s) =
    match kind_of_term x with
      | IsEvar (ev,args) ->
          if Evd.is_defined sigma ev then 
	    whrec (existential_value sigma (ev,args), l)
          else 
	    s
      | IsCast (c,_) -> whrec (c, l)
      | IsApp (f,cl)  -> whrec (f, append_stack cl l)
      | IsLambda (_,_,c) ->
          (match decomp_stack l with
             | None -> s
             | Some (a,m) -> stacklam whrec [a] c m)
      | x -> s
  in 
  whrec
*)

let whd_betaevar_state e = whd_state_gen betaevar e
let whd_betaevar_stack env sigma c =
  appterm_of_stack (whd_betaevar_state env sigma (c, empty_stack))
let whd_betaevar env sigma c =
  app_stack (whd_betaevar_state env sigma (c, empty_stack))

(*
let whd_betadeltaeta_state env sigma = 
  let rec whrec (x, l as s) =
    match kind_of_term x with
      | IsConst const when evaluable_constant env const ->
	  whrec (constant_value env const, l)
      | IsEvar (ev,args) when Evd.is_defined sigma ev ->
	  whrec (existential_value sigma (ev,args), l)
      | IsLetIn (_,b,_,c) -> stacklam whrec [b] c l
      | IsCast (c,_) -> whrec (c, l)
      | IsApp (f,cl)  -> whrec (f, append_stack cl l)
      | IsLambda (_,_,c) ->
          (match decomp_stack l with
             | None ->
                 (match kind_of_term (app_stack (whrec (c, empty_stack))) with 
                    | IsApp (f,cl) ->
			let napp = Array.length cl in
			if napp > 0 then
			  let x',l' = whrec (array_last cl, empty_stack) in
                          match kind_of_term x', decomp_stack l' with
                            | IsRel 1, None ->
				let lc = Array.sub cl 0 (napp - 1) in
				let u = if napp=1 then f else appvect (f,lc) in
				if noccurn 1 u then (pop u,empty_stack) else s
                            | _ -> s
			else s
                    | _ -> s)
             | Some (a,m) -> stacklam whrec [a] c m)
      | x -> s
  in 
  whrec
*)

let whd_betadeltaeta_state e = whd_state_gen betadeltaeta e
let whd_betadeltaeta_stack env sigma x =
  appterm_of_stack (whd_betadeltaeta_state env sigma (x, empty_stack))
let whd_betadeltaeta env sigma x = 
  app_stack (whd_betadeltaeta_state env sigma (x, empty_stack))

(* 3. Iota reduction Functions *)

(* NB : Cette fonction alloue peu c'est l'appel 
     ``let (recarg'hd,_ as recarg') = whfun recarg empty_stack in''
                                     --------------------
qui coute cher dans whd_betadeltaiota *)

(*
let whd_betaiota_state = 
  let rec whrec (x,stack as s) =
    match kind_of_term x with
      | IsCast (c,_)     -> whrec (c, stack)
      | IsApp (f,cl)    -> whrec (f, append_stack cl stack)
      | IsLambda (_,_,c) ->
          (match decomp_stack stack with
             | None -> s
             | Some (a,m) -> stacklam whrec [a] c m)
      | IsMutCase (ci,p,d,lf) ->
          let (c,cargs) = whrec (d, empty_stack) in
          if reducible_mind_case c then
            whrec (reduce_mind_case
                     {mP=p; mconstr=c; mcargs=list_of_stack cargs;
		      mci=ci; mlf=lf}, stack)
          else 
	    (mkMutCase (ci, p, app_stack (c,cargs), lf), stack)
            
      | IsFix fix ->
	  (match reduce_fix whrec fix stack with
             | Reduced s' -> whrec s'
	     | NotReducible -> s)
      | _ -> s
  in 
  whrec
*)

let whd_betaiota_state = local_whd_state_gen betaiota
let whd_betaiota_stack x =
  appterm_of_stack (whd_betaiota_state (x, empty_stack))
let whd_betaiota x =
  app_stack (whd_betaiota_state (x, empty_stack))

(*
let whd_betaiotaevar_state env sigma = 
  let rec whrec (x, stack as s) =
    match kind_of_term x with
      | IsEvar (ev,args) ->
          if Evd.is_defined sigma ev then 
	    whrec (existential_value sigma (ev,args), stack)
          else 
	    s
      | IsCast (c,_) -> whrec (c, stack)
      | IsApp (f,cl)    -> whrec (f, append_stack cl stack)
      | IsLambda (_,_,c) ->
          (match decomp_stack stack with
             | None -> s
             | Some (a,m) -> stacklam whrec [a] c m)
      | IsMutCase (ci,p,d,lf) ->
          let (c,cargs) = whrec (d, empty_stack) in
          if reducible_mind_case c then
	    whrec (reduce_mind_case
                     {mP=p; mconstr=c; mcargs=list_of_stack cargs;
		      mci=ci; mlf=lf}, stack)
          else 
	    (mkMutCase (ci, p, app_stack (c,cargs), lf), stack)
      | IsFix fix ->
	  (match reduce_fix whrec fix stack with
             | Reduced s' -> whrec s'
	     | NotReducible -> s)
      | _ -> s
 in 
  whrec
*)

let whd_betaiotaevar_state e = whd_state_gen betaiotaevar e
let whd_betaiotaevar_stack env sigma x =
  appterm_of_stack (whd_betaiotaevar_state env sigma (x, empty_stack))
let whd_betaiotaevar env sigma x = 
  app_stack (whd_betaiotaevar_state env sigma (x, empty_stack))

(*
let whd_betadeltaiota_state env sigma =
  let rec whrec (x, stack as s) =
    match kind_of_term x with
      | IsConst const when evaluable_constant env const ->
	  whrec (constant_value env const, stack)
      | IsEvar (ev,args) when Evd.is_defined sigma ev ->
	  whrec (existential_value sigma (ev,args), stack)
      | IsLetIn (_,b,_,c) -> stacklam whrec [b] c stack
      | IsCast (c,_) -> whrec (c, stack)
      | IsApp (f,cl)    -> whrec (f, append_stack cl stack)
      | IsLambda (_,_,c) ->
          (match decomp_stack stack with
             | None -> s
             | Some (a,m) -> stacklam whrec [a] c m)
      | IsMutCase (ci,p,d,lf) ->
          let (c,cargs) = whrec (d, empty_stack) in
          if reducible_mind_case c then
	    whrec (reduce_mind_case
                     {mP=p; mconstr=c; mcargs=list_of_stack cargs;
		      mci=ci; mlf=lf}, stack)
          else 
	    (mkMutCase (ci, p, app_stack (c,cargs), lf), stack)
      | IsFix fix ->
	  (match reduce_fix whrec fix stack with
             | Reduced s' -> whrec s'
	     | NotReducible -> s)
      | _ -> s
  in
  whrec
*)

let whd_betadeltaiota_state e = whd_state_gen betadeltaiota e
let whd_betadeltaiota_stack env sigma x =
  appterm_of_stack (whd_betadeltaiota_state env sigma (x, empty_stack))
let whd_betadeltaiota env sigma x = 
  app_stack (whd_betadeltaiota_state env sigma (x, empty_stack))
				
(*				
let whd_betadeltaiotaeta_state env sigma = 
  let rec whrec (x, stack as s) =
    match kind_of_term x with
      | IsConst const when evaluable_constant env const ->
	  whrec (constant_value env const, stack)
      | IsEvar (ev,args) when Evd.is_defined sigma ev -> 
	  whrec (existential_value sigma (ev,args), stack)
      | IsLetIn (_,b,_,c) -> stacklam whrec [b] c stack
      | IsCast (c,_) -> whrec (c, stack)
      | IsApp (f,cl)    -> whrec (f, append_stack cl stack)
      | IsLambda (_,_,c) ->
          (match decomp_stack stack with
             | None ->
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
             | Some (a,m) -> stacklam whrec [a] c m)

      | IsMutCase (ci,p,d,lf) ->
          let (c,cargs) = whrec (d, empty_stack) in
          if reducible_mind_case c then
	    whrec (reduce_mind_case
                     {mP=p; mconstr=c; mcargs=list_of_stack cargs;
		      mci=ci; mlf=lf}, stack)
          else 
	    (mkMutCase (ci, p, app_stack (c,cargs), lf), stack)
      | IsFix fix ->
	  (match reduce_fix whrec fix stack with
             | Reduced s' -> whrec s'
	     | NotReducible -> s)
      | _ -> s
  in 
  whrec
*)

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

type conv_pb = 
  | CONV 
  | CONV_LEQ

let pb_is_equal pb = pb = CONV

let pb_equal = function
  | CONV_LEQ -> CONV
  | CONV -> CONV

type 'a conversion_function = 
    env -> 'a evar_map -> constr -> constr -> constraints

(* Conversion utility functions *)

type conversion_test = constraints -> constraints

exception NotConvertible

let convert_of_bool b c =
  if b then c else raise NotConvertible

let bool_and_convert b f c = 
  if b then f c else raise NotConvertible

let convert_and f1 f2 c = f2 (f1 c)

let convert_or f1 f2 c =
  try f1 c with NotConvertible -> f2 c

let convert_forall2 f v1 v2 c =
  if Array.length v1 = Array.length v2
  then array_fold_left2 (fun c x y -> f x y c) c v1 v2
  else raise NotConvertible

(* Convertibility of sorts *)

let sort_cmp pb s0 s1 =
  match (s0,s1) with
    | (Prop c1, Prop c2) -> convert_of_bool (c1 = c2)
    | (Prop c1, Type u)  -> convert_of_bool (not (pb_is_equal pb))
    | (Type u1, Type u2) ->
	(match pb with
           | CONV -> enforce_eq u1 u2
	   | CONV_LEQ -> enforce_geq u2 u1)
    | (_, _) -> fun _ -> raise NotConvertible

let base_sort_cmp pb s0 s1 =
  match (s0,s1) with
    | (Prop c1, Prop c2) -> c1 = c2
    | (Prop c1, Type u)  -> not (pb_is_equal pb)
    | (Type u1, Type u2) -> true
    | (_, _) -> false

(* Conversion between  [lft1]term1 and [lft2]term2 *)

let rec ccnv cv_pb infos lft1 lft2 term1 term2 = 
  eqappr cv_pb infos (lft1, fhnf infos term1) (lft2, fhnf infos term2)

(* Conversion between [lft1]([^n1]hd1 v1) and [lft2]([^n2]hd2 v2) *)

and eqappr cv_pb infos appr1 appr2 =
  let (lft1,(n1,hd1,v1)) = appr1
  and (lft2,(n2,hd2,v2)) = appr2 in
  let el1 = el_shft n1 lft1
  and el2 = el_shft n2 lft2 in
  match (frterm_of hd1, frterm_of hd2) with
    (* case of leaves *)
    | (FAtom a1, FAtom a2) ->
	(match kind_of_term a1, kind_of_term a2 with
	   | (IsSort s1, IsSort s2) -> 
	       bool_and_convert
		 (Array.length v1 = 0 && Array.length v2 = 0)
		 (sort_cmp cv_pb s1 s2)
	   | (IsMeta n, IsMeta m) ->
               bool_and_convert (n=m) 
		 (convert_forall2 (ccnv (pb_equal cv_pb) infos lft1 lft2)
		    v1 v2)
	   | IsXtra s1, IsXtra s2 ->
               bool_and_convert (s1=s2)
		 (convert_forall2 (ccnv (pb_equal cv_pb) infos lft1 lft2)
		    v1 v2)
	   | _ -> fun _ -> raise NotConvertible)

    (* 2 index known to be bound to no constant *)
    | (FRel n, FRel m) ->
        bool_and_convert 
          (reloc_rel n el1 = reloc_rel m el2)
          (convert_forall2 (ccnv (pb_equal cv_pb) infos lft1 lft2) v1 v2)

    (* 2 constants, 2 existentials or 2 local defined vars or 2 defined rels *)
    | (FFlex (fl1,al1), FFlex (fl2,al2)) ->
	convert_or
	  (* try first intensional equality *)
	  (bool_and_convert (fl1 = fl2)
	     (convert_and
		(convert_forall2 (ccnv (pb_equal cv_pb) infos el1 el2) al1 al2)
		(convert_forall2 (ccnv (pb_equal cv_pb) infos lft1 lft2)
		   v1 v2)))
          (* else expand the second occurrence (arbitrary heuristic) *)
          (fun u ->
	     match search_frozen_value infos fl2 al2 with
             | Some def2 -> 
		 eqappr cv_pb infos appr1 (lft2, fhnf_apply infos n2 def2 v2) u
             | None -> (match search_frozen_value infos fl1 al1 with
                          | Some def1 -> eqappr cv_pb infos
				(lft1, fhnf_apply infos n1 def1 v1) appr2 u
			  | None -> raise NotConvertible))

    (* only one constant, existential, defined var or defined rel *)
    | (FFlex (fl1,al1), _)      ->
        (match search_frozen_value infos fl1 al1 with
           | Some def1 -> 
	       eqappr cv_pb infos (lft1, fhnf_apply infos n1 def1 v1) appr2
           | None -> fun _ -> raise NotConvertible)
    | (_, FFlex (fl2,al2))      ->
        (match search_frozen_value infos fl2 al2 with
           | Some def2 -> 
	       eqappr cv_pb infos appr1 (lft2, fhnf_apply infos n2 def2 v2)
           | None -> fun _ -> raise NotConvertible)
	
    (* other constructors *)
    | (FLambda (_,c1,c2,_,_), FLambda (_,c'1,c'2,_,_)) ->
        bool_and_convert
	  (Array.length v1 = 0 && Array.length v2 = 0)
          (convert_and
	     (ccnv (pb_equal cv_pb) infos el1 el2 c1 c'1)
             (ccnv (pb_equal cv_pb) infos (el_lift el1) (el_lift el2) c2 c'2))

    | (FLetIn _, _) | (_, FLetIn _) -> anomaly "Normally removed by fhnf"

    | (FProd (_,c1,c2,_,_), FProd (_,c'1,c'2,_,_)) ->
	bool_and_convert
          (Array.length v1 = 0 && Array.length v2 = 0)
	  (convert_and
             (ccnv (pb_equal cv_pb) infos el1 el2 c1 c'1) (* Luo's system *)
             (ccnv cv_pb infos (el_lift el1) (el_lift el2) c2 c'2))

    (* Inductive types:  MutInd MutConstruct MutCase Fix Cofix *)

      (* Les annotations du MutCase ne servent qu'à l'affichage *)

    | (FCases (_,p1,c1,cl1), FCases (_,p2,c2,cl2)) ->
	convert_and
	  (ccnv (pb_equal cv_pb) infos el1 el2 p1 p2)
	  (convert_and
	     (ccnv (pb_equal cv_pb) infos el1 el2 c1 c2)
	     (convert_and
		(convert_forall2 (ccnv (pb_equal cv_pb) infos el1 el2) cl1 cl2)
		(convert_forall2 (ccnv (pb_equal cv_pb) infos lft1 lft2) v1 v2)
	     ))

     | (FInd (op1,cl1), FInd(op2,cl2)) ->
	 bool_and_convert (op1 = op2)
	   (convert_and
              (convert_forall2 (ccnv (pb_equal cv_pb) infos el1 el2) cl1 cl2)
              (convert_forall2 (ccnv (pb_equal cv_pb) infos lft1 lft2) v1 v2))
     | (FConstruct (op1,cl1), FConstruct(op2,cl2)) ->
	 bool_and_convert (op1 = op2)
	   (convert_and
              (convert_forall2 (ccnv (pb_equal cv_pb) infos el1 el2) cl1 cl2)
              (convert_forall2 (ccnv (pb_equal cv_pb) infos lft1 lft2) v1 v2))
     | (FFix (op1,(tys1,_,cl1),_,_), FFix(op2,(tys2,_,cl2),_,_)) ->
	 let n = Array.length cl1 in
	 bool_and_convert (op1 = op2)
	   (convert_and
              (convert_forall2 (ccnv (pb_equal cv_pb) infos el1 el2) tys1 tys2)
	      (convert_and
		 (convert_forall2 (ccnv (pb_equal cv_pb) infos 
				     (el_liftn n el1) (el_liftn n el2))
		    cl1 cl2)
		 (convert_forall2 (ccnv (pb_equal cv_pb) infos lft1 lft2)
		    v1 v2)))
     | (FCoFix (op1,(tys1,_,cl1),_,_), FCoFix(op2,(tys2,_,cl2),_,_)) ->
	 let n = Array.length cl1 in
	 bool_and_convert (op1 = op2)
	   (convert_and
              (convert_forall2 (ccnv (pb_equal cv_pb) infos el1 el2) tys1 tys2)
	      (convert_and
		 (convert_forall2 (ccnv (pb_equal cv_pb) infos
				     (el_liftn n el1) (el_liftn n el2))
		    cl1 cl2)
		 (convert_forall2 (ccnv (pb_equal cv_pb) infos lft1 lft2)
		    v1 v2)))

     | _ -> (fun _ -> raise NotConvertible)


let fconv cv_pb env sigma t1 t2 =
  let t1 = local_strong strip_outer_cast t1
  and t2 = local_strong strip_outer_cast t2 in
  if eq_constr t1 t2 then 
    Constraint.empty
  else
    let infos = create_clos_infos hnf_flags env sigma in
    ccnv cv_pb infos ELID ELID (inject t1) (inject t2)
      Constraint.empty

let conv env = fconv CONV env
let conv_leq env = fconv CONV_LEQ env 

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
let is_fconv = function | CONV -> is_conv | CONV_LEQ -> is_conv_leq

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
	  decrec (push_rel_decl (n,outcast_type a) env)
	    ((n,a)::m) c0
      | _ -> m,t
  in 
  decrec env []

let splay_prod_assum env sigma = 
  let rec prodec_rec env l c =
    let t = whd_betadeltaiota_nolet env sigma c in
    match kind_of_term c with
    | IsProd (x,t,c)  ->
	prodec_rec (push_rel_decl (x,outcast_type t) env)
	  (Sign.add_rel_decl (x,outcast_type t) l) c
    | IsLetIn (x,b,t,c) ->
	prodec_rec (push_rel_def (x,b,outcast_type t) env)
	  (Sign.add_rel_def (x,b,outcast_type t) l) c
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
	  let a = make_typed_lazy a (fun _ -> Type dummy_univ) in
	  decrec (push_rel_decl (n,a) env)
	    (m-1) (Sign.add_rel_decl (n,a) ln) c0
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
 * and does not reduce redexes containing meta-variables.
 * ASSUMES THAT APPLICATIONS ARE BINARY ONES.
 * Used in Programs.
 * Added by JCF, 29/1/98. *)

let whd_programs_stack env sigma = 
  let rec whrec (x, stack as s) =
    match kind_of_term x with
      | IsApp (f,([|c|] as cl)) ->
	  if occur_meta c then s else whrec (f, append_stack cl stack)
      | IsLambda (_,_,c) ->
          (match decomp_stack stack with
             | None -> s
             | Some (a,m) -> stacklam whrec [a] c m)
      | IsMutCase (ci,p,d,lf) ->
	  if occur_meta d then
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
      | IsProd (x,t,c0) -> decrec (push_rel_decl (x,outcast_type t) env) c0
      | IsLambda (x,t,c0) -> decrec (push_rel_decl (x,outcast_type t) env) c0
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

(* calcul des arguments implicites *)

(* la seconde liste est ordonne'e *)

let ord_add x l =
  let rec aux l = match l with 
    | []    -> [x]
    | y::l' -> if y > x then x::l else if x = y then l else y::(aux l')
  in 
  aux l
    
let add_free_rels_until bound m acc =
  let rec frec depth acc c = match kind_of_term c with
    | IsRel n when (n < bound+depth) & (n >= depth) ->
	Intset.add (bound+depth-n) acc
    | _ -> fold_constr_with_binders succ frec depth acc c
  in 
  frec 1 acc m 

(* calcule la liste des arguments implicites *)

let poly_args env sigma t =
  let rec aux env n t =
    match kind_of_term (whd_betadeltaiota env sigma t) with
      | IsProd (x,a,b) ->
	  add_free_rels_until n a
	    (aux (push_rel_decl (x,outcast_type a) env) (n+1) b)
      | _ -> Intset.empty
  in 
  match kind_of_term (whd_betadeltaiota env sigma t) with 
    | IsProd (x,a,b) ->
	Intset.elements (aux (push_rel_decl (x,outcast_type a) env) 1 b)
    | _ -> []

(* Expanding existential variables (pretyping.ml) *)
(* 1- whd_ise fails if an existential is undefined *)

exception Uninstantiated_evar of int

let rec whd_ise sigma c =
  match kind_of_term c with
    | IsEvar (ev,args) when Evd.in_dom sigma ev ->
	if Evd.is_defined sigma ev then
          whd_ise sigma (existential_value sigma (ev,args))
	else raise (Uninstantiated_evar ev)
  | IsCast (c,_) -> whd_ise sigma c
  | IsSort (Type _) -> mkSort (Type dummy_univ)
  | _ -> c


(* 2- undefined existentials are left unchanged *)
let rec whd_ise1 sigma c =
  match kind_of_term c with
    | IsEvar (ev,args) when Evd.in_dom sigma ev & Evd.is_defined sigma ev ->
	whd_ise1 sigma (existential_value sigma (ev,args))
    | IsCast (c,_) -> whd_ise1 sigma c
    (* A quoi servait cette ligne ???
    | IsSort (Type _) -> mkSort (Type dummy_univ)
    *)
    | _ -> c

let nf_ise1 sigma = local_strong (whd_ise1 sigma)

(* A form of [whd_ise1] with type "reduction_function" *)
let whd_evar env = whd_ise1
