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
open Nameops
open Term
open Libnames
open Termops
open Declarations
open Inductive
open Environ
open Reductionops
open Closure
open Instantiate
open Cbv
open Rawterm

exception Elimconst
exception Redelimination

let set_opaque_const = Conv_oracle.set_opaque_const
let set_transparent_const sp =
  let cb = Global.lookup_constant sp in
  if cb.const_body <> None & cb.const_opaque then
    errorlabstrm "set_transparent_const"
      (str "Cannot make" ++ spc () ++ 
         Nametab.pr_global_env None (ConstRef sp) ++
         spc () ++ str "transparent because it was declared opaque.");
  Conv_oracle.set_transparent_const sp

let set_opaque_var      = Conv_oracle.set_opaque_var
let set_transparent_var = Conv_oracle.set_transparent_var

let _ = 
  Summary.declare_summary "Transparent constants and variables"
    { Summary.freeze_function = Conv_oracle.freeze;
      Summary.unfreeze_function = Conv_oracle.unfreeze;
      Summary.init_function = Conv_oracle.init;
      Summary.survive_section = false }

let is_evaluable env ref =
  match ref with
      EvalConstRef kn ->
        let (ids,kns) = Conv_oracle.freeze() in
        KNpred.mem kn kns &
        let cb = Environ.lookup_constant kn env in
        cb.const_body <> None & not cb.const_opaque
    | EvalVarRef id ->
        let (ids,sps) = Conv_oracle.freeze() in
        Idpred.mem id ids &
        let (_,value,_) = Environ.lookup_named id env in
        value <> None

type evaluable_reference =
  | EvalConst of constant
  | EvalVar of identifier
  | EvalRel of int
  | EvalEvar of existential

let mkEvalRef = function
  | EvalConst cst -> mkConst cst
  | EvalVar id -> mkVar id
  | EvalRel n -> mkRel n
  | EvalEvar ev -> mkEvar ev

let isEvalRef env c = match kind_of_term c with
  | Const sp -> is_evaluable env (EvalConstRef sp)
  | Var id -> is_evaluable env (EvalVarRef id)
  | Rel _ | Evar _ -> true
  | _ -> false

let destEvalRef c = match kind_of_term c with
  | Const cst ->  EvalConst cst
  | Var id  -> EvalVar id
  | Rel n -> EvalRel n
  | Evar ev -> EvalEvar ev
  | _ -> anomaly "Not an evaluable reference"

let reference_opt_value sigma env = function
  | EvalConst cst -> constant_opt_value env cst
  | EvalVar id ->
      let (_,v,_) = lookup_named id env in
      v
  | EvalRel n ->
      let (_,v,_) = lookup_rel n env in
      option_app (lift n) v
  | EvalEvar ev -> existential_opt_value sigma ev

exception NotEvaluable
let reference_value sigma env c =
  match reference_opt_value sigma env c with
    | None -> raise NotEvaluable
    | Some d -> d

(************************************************************************)
(* Reduction of constant hiding fixpoints (e.g. for Simpl). The trick   *)
(* is to reuse the name of the function after reduction of the fixpoint *)

type constant_evaluation = 
  | EliminationFix of int * (int * (int * constr) list * int)
  | EliminationMutualFix of
      int * evaluable_reference *
      (evaluable_reference option array * (int * (int * constr) list * int))
  | EliminationCases of int
  | NotAnElimination

(* We use a cache registered as a global table *)


module CstOrdered =
  struct
    type t = constant
    let compare = Pervasives.compare
  end
module Cstmap = Map.Make(CstOrdered)

let eval_table = ref Cstmap.empty

type frozen = (int * constant_evaluation) Cstmap.t

let init () =
  eval_table := Cstmap.empty

let freeze () =
  !eval_table

let unfreeze ct =
  eval_table := ct

let _ = 
  Summary.declare_summary "evaluation"
    { Summary.freeze_function = freeze;
      Summary.unfreeze_function = unfreeze;
      Summary.init_function = init;
      Summary.survive_section = false }


(* Check that c is an "elimination constant"
   [xn:An]..[x1:A1](<P>MutCase (Rel i) of f1..fk end g1 ..gp)
   or [xn:An]..[x1:A1](Fix(f|t) (Rel i1) ..(Rel ip)) 
    with i1..ip distinct variables not occuring in t 
   keep relevenant information ([i1,Ai1;..;ip,Aip],n,b)
   with b = true in case of a fixpoint in order to compute 
   an equivalent of Fix(f|t)[xi<-ai] as 
   [yip:Bip]..[yi1:Bi1](F bn..b1) 
   == [yip:Bip]..[yi1:Bi1](Fix(f|t)[xi<-ai] (Rel 1)..(Rel p))
   with bj=aj if j<>ik and bj=(Rel c) and Bic=Aic[xn..xic-1 <- an..aic-1] *)

let check_fix_reversibility labs args ((lv,i),(_,tys,bds)) =
  let n = List.length labs in
  let nargs = List.length args in
  if nargs > n then raise Elimconst;
  let nbfix = Array.length bds in
  let li =
    List.map
      (function d -> match kind_of_term d with
         | Rel k ->
             if
	       array_for_all (noccurn k) tys
	       && array_for_all (noccurn (k+nbfix)) bds
	     then 
	       (k, List.nth labs (k-1)) 
	     else 
	       raise Elimconst
         | _ -> 
	     raise Elimconst) args
  in
  if list_distinct (List.map fst li) then 
    let k = lv.(i) in
    if k < nargs then
(*  Such an optimisation would need eta-expansion 
      let p = destRel (List.nth args k) in 
      EliminationFix (n-p+1,(nbfix,li,n))
*)
      EliminationFix (n,(nbfix,li,n))
    else
      EliminationFix (n-nargs+lv.(i)+1,(nbfix,li,n))
  else 
    raise Elimconst

(* Heuristic to look if global names are associated to other
   components of a mutual fixpoint *)

let invert_name labs l na0 env sigma ref = function
  | Name id -> 
      if na0 <> Name id then
	let refi = match ref with
	  | EvalRel _ | EvalEvar _ -> None
	  | EvalVar id' -> Some (EvalVar id)
	  | EvalConst kn ->
	      let (mp,dp,_) = repr_kn kn in
	      Some (EvalConst (make_kn mp dp (label_of_id id))) in
	match refi with
	  | None -> None
	  | Some ref ->
	      match reference_opt_value sigma env ref with
		| None -> None
		| Some c -> 
		    let labs',ccl = decompose_lam c in
		    let _, l' = whd_betaetalet_stack ccl in
		    let labs' = List.map snd labs' in
		    if labs' = labs & l = l' then Some ref else None
      else Some ref
  | Anonymous -> None (* Actually, should not occur *)

(* [compute_consteval_direct] expand all constant in a whole, but
   [compute_consteval_mutual_fix] only one by one, until finding the
   last one before the Fix if the latter is mutually defined *)

let compute_consteval_direct sigma env ref =
  let rec srec env n labs c =
    let c',l = whd_betadeltaeta_stack env sigma c in
    match kind_of_term c' with
      | Lambda (id,t,g) when l=[] ->
	  srec (push_rel (id,None,t) env) (n+1) (t::labs) g
      | Fix fix ->
	  (try check_fix_reversibility labs l fix 
	  with Elimconst -> NotAnElimination)
      | Case (_,_,d,_) when isRel d -> EliminationCases n
      | _ -> NotAnElimination
  in 
  match reference_opt_value sigma env ref with
    | None -> NotAnElimination
    | Some c -> srec env 0 [] c

let compute_consteval_mutual_fix sigma env ref =
  let rec srec env minarg labs ref c =
    let c',l = whd_betaetalet_stack c in
    let nargs = List.length l in
    match kind_of_term c' with
      | Lambda (na,t,g) when l=[] ->
	  srec (push_rel (na,None,t) env) (minarg+1) (t::labs) ref g
      | Fix ((lv,i),(names,_,_) as fix) ->
	  (* Last known constant wrapping Fix is ref = [labs](Fix l) *)
	  (match compute_consteval_direct sigma env ref with
	     | NotAnElimination -> (*Above const was eliminable but this not!*)
		 NotAnElimination
	     | EliminationFix (minarg',infos) ->
		 let refs =
		   Array.map
		     (invert_name labs l names.(i) env sigma ref) names in
		 let new_minarg = max (minarg'+minarg-nargs) minarg' in
		 EliminationMutualFix (new_minarg,ref,(refs,infos))
	     | _ -> assert false)
      | _ when isEvalRef env c' ->
	  (* Forget all \'s and args and do as if we had started with c' *)
	  let ref = destEvalRef c' in
	  (match reference_opt_value sigma env ref with
	    | None -> anomaly "Should have been trapped by compute_direct"
	    | Some c -> srec env (minarg-nargs) [] ref c)
      | _ -> (* Should not occur *) NotAnElimination
  in 
  match reference_opt_value sigma env ref with
    | None -> (* Should not occur *) NotAnElimination
    | Some c -> srec env 0 [] ref c

let compute_consteval sigma env ref =
  match compute_consteval_direct sigma env ref with
    | EliminationFix (_,(nbfix,_,_)) when nbfix <> 1 ->
	compute_consteval_mutual_fix sigma env ref
    | elim -> elim
	
let reference_eval sigma env = function
  | EvalConst cst as ref -> 
      (try
	 Cstmap.find cst !eval_table
       with Not_found -> begin
	 let v = compute_consteval sigma env ref in
	 eval_table := Cstmap.add cst v !eval_table;
	 v
       end)
  | ref -> compute_consteval sigma env ref

let rev_firstn_liftn fn ln = 
  let rec rfprec p res l = 
    if p = 0 then 
      res 
    else
      match l with
        | [] -> invalid_arg "Reduction.rev_firstn_liftn"
        | a::rest -> rfprec (p-1) ((lift ln a)::res) rest
  in 
  rfprec fn []

(*  EliminationFix ([(yi1,Ti1);...;(yip,Tip)],n) means f is some
   [y1:T1,...,yn:Tn](Fix(..) yi1 ... yip);
   f is applied to largs and we need for recursive calls to build
   [x1:Ti1',...,xp:Tip'](f a1..a(n-p) yi1 ... yip) 
   where a1...an are the n first arguments of largs and Tik' is Tik[yil=al]
   To check ... *)

let make_elim_fun (names,(nbfix,lv,n)) largs =
  let labs,_ = list_chop n (list_of_stack largs) in
  let p = List.length lv in
  let ylv = List.map fst lv in
  let la' = list_map_i 
	      (fun q aq ->
		 try (mkRel (p+1-(list_index (n-q) ylv))) 
		 with Not_found -> aq) 0
              (List.map (lift p) labs) 
  in 
  fun i ->
    match names.(i) with
      | None -> None
      | Some ref -> Some (
(*    let fi =
      if nbfix = 1 then
	mkEvalRef ref
      else
	match ref with
	  | EvalConst (sp,args) ->
	      mkConst (make_path (dirpath sp) id (kind_of_path sp),args)
	  | _ -> anomaly "elimination of local fixpoints not implemented"
    in
*)
      list_fold_left_i 
	(fun i c (k,a) -> 
	   mkLambda (Name(id_of_string"x"),
		     substl (rev_firstn_liftn (n-k) (-i) la') a,
		     c))
	0 (applistc (mkEvalRef ref) la') lv)

(* [f] is convertible to [Fix(recindices,bodynum),bodyvect)] make 
   the reduction using this extra information *)

let contract_fix_use_function f
  ((recindices,bodynum),(types,names,bodies as typedbodies)) =
  let nbodies = Array.length recindices in
  let make_Fi j = match f j with
    | None -> mkFix((recindices,j),typedbodies)
    | Some c -> c in
(*    match List.nth names j with Name id -> f id | _ -> assert false in*)
  let lbodies = list_tabulate make_Fi nbodies in
  substl (List.rev lbodies) bodies.(bodynum)

let reduce_fix_use_function f whfun fix stack =
  match fix_recarg fix stack with
    | None -> NotReducible
    | Some (recargnum,recarg) ->
        let (recarg'hd,_ as recarg') =
	  if isRel recarg then
	    (* The recarg cannot be a local def, no worry about the right env *)
	    (recarg, empty_stack) 
	  else
	    whfun (recarg, empty_stack) in
        let stack' = stack_assign stack recargnum (app_stack recarg') in
	(match kind_of_term recarg'hd with
           | Construct _ ->
	       Reduced (contract_fix_use_function f fix,stack')
	   | _ -> NotReducible)

let contract_cofix_use_function f (bodynum,(_,names,bodies as typedbodies)) =
  let nbodies = Array.length bodies in
  let make_Fi j = match f j with
    | None -> mkCoFix(j,typedbodies)
    | Some c -> c in
(*    match List.nth names j with Name id -> f id | _ -> assert false in*)
  let subbodies = list_tabulate make_Fi nbodies in
  substl subbodies bodies.(bodynum)

let reduce_mind_case_use_function func env mia =
  match kind_of_term mia.mconstr with 
    | Construct(ind_sp,i as cstr_sp) ->
	let real_cargs = snd (list_chop mia.mci.ci_npar mia.mcargs) in
	applist (mia.mlf.(i-1), real_cargs)
    | CoFix (_,(names,_,_) as cofix) ->
	let build_fix_name i =
	  match names.(i) with 
	    | Name id ->
                if isConst func then
		  let (mp,dp,_) = repr_kn (destConst func) in
		  let kn = make_kn mp dp (label_of_id id) in
		  (match constant_opt_value env kn with
		    | None -> None
		    | Some _ -> Some (mkConst kn))
                else None
	    | Anonymous -> None in 
	let cofix_def = contract_cofix_use_function build_fix_name cofix in
	mkCase (mia.mci, mia.mP, applist(cofix_def,mia.mcargs), mia.mlf)
    | _ -> assert false

let special_red_case sigma env whfun (ci, p, c, lf)  =
  let rec redrec s = 
    let (constr, cargs) = whfun s in 
    if isEvalRef env constr then
      let ref = destEvalRef constr in
      match reference_opt_value sigma env ref with
        | None -> raise Redelimination
        | Some gvalue ->
	    if reducible_mind_case gvalue then
	      reduce_mind_case_use_function constr env
	        {mP=p; mconstr=gvalue; mcargs=list_of_stack cargs;
                mci=ci; mlf=lf}
	    else
	      redrec (gvalue, cargs)
    else
      if reducible_mind_case constr then
        reduce_mind_case
	  {mP=p; mconstr=constr; mcargs=list_of_stack cargs;
	  mci=ci; mlf=lf}
      else 
	raise Redelimination
  in 
  redrec (c, empty_stack)


let rec red_elim_const env sigma ref largs =
  match reference_eval sigma env ref with
    | EliminationCases n when stack_args_size largs >= n ->
	let c = reference_value sigma env ref in
	let c', lrest = whd_betadeltaeta_state env sigma (c,largs) in
        (special_red_case sigma env (construct_const env sigma) (destCase c'),
	 lrest)
    | EliminationFix (min,infos) when stack_args_size largs >=min ->
	let c = reference_value sigma env ref in
	let d, lrest = whd_betadeltaeta_state env sigma (c,largs) in
	let f = make_elim_fun ([|Some ref|],infos) largs in
	let co = construct_const env sigma in
	(match reduce_fix_use_function f co (destFix d) lrest with
	   | NotReducible -> raise Redelimination
	   | Reduced (c,rest) -> (nf_beta c, rest))
    | EliminationMutualFix (min,refgoal,refinfos)
	when stack_args_size largs >= min ->
	let rec descend ref args =
	  let c = reference_value sigma env ref in
	  if ref = refgoal then
	    (c,args)
	  else
	    let c', lrest = whd_betaetalet_state (c,args) in
	    descend (destEvalRef c') lrest in
	let (_, midargs as s) = descend ref largs in
	let d, lrest = whd_betadeltaeta_state env sigma s in
	let f = make_elim_fun refinfos midargs in
	let co = construct_const env sigma in
	(match reduce_fix_use_function f co (destFix d) lrest with
	   | NotReducible -> raise Redelimination
	   | Reduced (c,rest) -> (nf_beta c, rest))
    | _ -> raise Redelimination

and construct_const env sigma = 
  let rec hnfstack (x, stack as s) =
    match kind_of_term x with
      | Cast (c,_) -> hnfstack (c, stack)
      | App (f,cl) -> hnfstack (f, append_stack cl stack)
      | Lambda (id,t,c) ->
          (match decomp_stack stack with 
             | None -> assert false
             | Some (c',rest) -> 
		   stacklam hnfstack [c'] c rest)
      | LetIn (n,b,t,c) -> stacklam hnfstack [b] c stack
      | Case (ci,p,c,lf) ->
          hnfstack 
	    (special_red_case sigma env
              (construct_const env sigma) (ci,p,c,lf), stack)
      | Construct _ -> s
      | CoFix _ -> s
      | Fix fix -> 
	  (match reduce_fix hnfstack fix stack with
             | Reduced s' -> hnfstack s'
	     | NotReducible -> raise Redelimination)
      | _ when isEvalRef env x ->
	  let ref = destEvalRef x in
          (try
	    hnfstack (red_elim_const env sigma ref stack)
           with Redelimination ->
	     (match reference_opt_value sigma env ref with
		| Some cval ->
		    (match kind_of_term cval with
                       | CoFix _ -> s
                       | _ -> hnfstack (cval, stack))
		| None ->
		    raise Redelimination))
      | _ -> raise Redelimination
  in 
  hnfstack 

(***********************************************************************)
(*            Special Purpose Reduction Strategies                     *)

(* Red reduction tactic: reduction to a product *)

let internal_red_product env sigma c = 
  let simpfun = clos_norm_flags betaiotazeta env sigma in
  let rec redrec env x =
    match kind_of_term x with
      | App (f,l) -> 
          (match kind_of_term f with
             | Fix fix ->
                 let stack = append_stack l empty_stack in
                 (match fix_recarg fix stack with
                    | None -> raise Redelimination
                    | Some (recargnum,recarg) ->
                        let recarg' = redrec env recarg in
                        let stack' = stack_assign stack recargnum recarg' in
                        simpfun (app_stack (f,stack')))
             | _ -> simpfun (appvect (redrec env f, l)))
      | Cast (c,_) -> redrec env c
      | Prod (x,a,b) -> mkProd (x, a, redrec (push_rel (x,None,a) env) b)
      | LetIn (x,a,b,t) -> redrec env (subst1 a t)
      | Case (ci,p,d,lf) -> simpfun (mkCase (ci,p,redrec env d,lf))
      | _ when isEvalRef env x -> 
          (* TO DO: re-fold fixpoints after expansion *)
          (* to get true one-step reductions *)
          let ref = destEvalRef x in
	  (match reference_opt_value sigma env ref with
	     | None -> raise Redelimination
	     | Some c -> c)
      | _ -> raise Redelimination
  in redrec env c

let red_product env sigma c = 
  try internal_red_product env sigma c
  with Redelimination -> error "Not reducible"

(* Hnf reduction tactic: *)

let hnf_constr env sigma c = 
  let rec redrec (x, largs as s) =
    match kind_of_term x with
      | Lambda (n,t,c) ->
          (match decomp_stack largs with
             | None      -> app_stack s
             | Some (a,rest) -> 
		 stacklam redrec [a] c rest)
      | LetIn (n,b,t,c) -> stacklam redrec [b] c largs
      | App (f,cl)   -> redrec (f, append_stack cl largs)
      | Cast (c,_) -> redrec (c, largs)
      | Case (ci,p,c,lf) ->
          (try
             redrec 
	       (special_red_case sigma env (whd_betadeltaiota_state env sigma) 
		  (ci, p, c, lf), largs)
           with Redelimination -> 
	     app_stack s)
      | Fix fix ->
	  (match reduce_fix (whd_betadeltaiota_state env sigma) fix largs with
             | Reduced s' -> redrec s'
	     | NotReducible -> app_stack s)
      | _ when isEvalRef env x ->
	  let ref = destEvalRef x in
          (try
            let (c',lrest) = red_elim_const env sigma ref largs in 
	    redrec (c', lrest)
           with Redelimination ->
             match reference_opt_value sigma env ref with
	       | Some c ->
		   (match kind_of_term (snd (decompose_lam c)) with 
                      | CoFix _ | Fix _ -> app_stack (x,largs)
		      | _ -> redrec (c, largs))
	       | None -> app_stack s)
      | _ -> app_stack s
  in 
  redrec (c, empty_stack)

(* Simpl_rew reduction tactic *)

let rew_nf env sigma = Cime.nf (cime env)

(* Simpl reduction tactic: same as simplify, but also reduces
   elimination constants *)

let whd_nf env sigma c = 
  let rec nf_app (c, stack as s) =
    match kind_of_term c with
      | Lambda (name,c1,c2)    ->
          (match decomp_stack stack with
             | None -> (c,empty_stack)
             | Some (a1,rest) -> 
		 stacklam nf_app [a1] c2 rest)
      | LetIn (n,b,t,c) -> stacklam nf_app [b] c stack
      | App (f,cl) -> nf_app (f, append_stack cl stack)
      | Cast (c,_) -> nf_app (c, stack)
      | Case (ci,p,d,lf) ->
          (try
             nf_app (special_red_case sigma env nf_app (ci,p,d,lf), stack)
           with Redelimination -> 
	     s)
      | Fix fix ->
	  (match reduce_fix nf_app fix stack with
             | Reduced s' -> nf_app s'
	     | NotReducible -> s)
      | _ when isEvalRef env c ->
          (try
	     nf_app (red_elim_const env sigma (destEvalRef c) stack)
           with Redelimination -> 
	     s)
      | _ -> s
  in 
  app_stack (nf_app (c, empty_stack))

let nf env sigma c = strong whd_nf env sigma c

let contextually (locs,c) f env sigma t =
  let maxocc = List.fold_right max locs 0 in
  let pos = ref 1 in
  let check = ref true in
  let except = List.exists (fun n -> n<0) locs in
  if except & (List.exists (fun n -> n>=0) locs) 
  then error "mixing of positive and negative occurences"
  else
   let rec traverse (env,c as envc) t =
    if locs <> [] & (not except) & (!pos > maxocc) then t
    else
    if eq_constr c t then
      let r =
	if except then 
	  if List.mem (- !pos) locs then t else f env sigma t
	else 
	  if locs = [] or List.mem !pos locs then f env sigma t else t
      in incr pos; r
    else
      map_constr_with_binders_left_to_right
	(fun d (env,c) -> (push_rel d env,lift 1 c))
        traverse envc t
  in
  let t' = traverse (env,c) t in
  if locs <> [] & List.exists (fun o -> o >= !pos or o <= - !pos) locs then
    errorlabstrm "contextually" (str "Too few occurences");
  t'

(* linear substitution (following pretty-printer) of the value of name in c.
 * n is the number of the next occurence of name.
 * ol is the occurence list to find. *)
let rec substlin env name n ol c =
  match kind_of_term c with
    | Const kn when EvalConstRef kn = name ->
        if List.hd ol = n then
          try 
	    (n+1, List.tl ol, constant_value env kn)
          with
	      NotEvaluableConst _ ->
		errorlabstrm "substlin"
		  (pr_kn kn ++ str " is not a defined constant")
        else 
	  ((n+1), ol, c)

    | Var id when EvalVarRef id = name ->
        if List.hd ol = n then
          match lookup_named id env with
	    | (_,Some c,_) -> (n+1, List.tl ol, c)
	    | _ -> 
		errorlabstrm "substlin"
		  (pr_id id ++ str " is not a defined constant")
        else 
	  ((n+1), ol, c)

    (* INEFFICIENT: OPTIMIZE *)
    | App (c1,cl) ->
        Array.fold_left 
	  (fun (n1,ol1,c1') c2 ->
	     (match ol1 with 
                | [] -> (n1,[],applist(c1',[c2]))
                | _  ->
                    let (n2,ol2,c2') = substlin env name n1 ol1 c2 in
                    (n2,ol2,applist(c1',[c2']))))
          (substlin env name n ol c1) cl

    | Lambda (na,c1,c2) ->
        let (n1,ol1,c1') = substlin env name n ol c1 in
        (match ol1 with 
           | [] -> (n1,[],mkLambda (na,c1',c2))
           | _  ->
               let (n2,ol2,c2') = substlin env name n1 ol1 c2 in
               (n2,ol2,mkLambda (na,c1',c2')))

    | LetIn (na,c1,t,c2) ->
        let (n1,ol1,c1') = substlin env name n ol c1 in
        (match ol1 with 
           | [] -> (n1,[],mkLetIn (na,c1',t,c2))
           | _  ->
               let (n2,ol2,c2') = substlin env name n1 ol1 c2 in
               (n2,ol2,mkLetIn (na,c1',t,c2')))

    | Prod (na,c1,c2) ->
        let (n1,ol1,c1') = substlin env name n ol c1 in
        (match ol1 with 
           | [] -> (n1,[],mkProd (na,c1',c2))
           | _  ->
               let (n2,ol2,c2') = substlin env name n1 ol1 c2 in
               (n2,ol2,mkProd (na,c1',c2')))
	
    | Case (ci,p,d,llf) -> 
        let rec substlist nn oll = function
          | []     -> (nn,oll,[])
          | f::lfe ->
              let (nn1,oll1,f') = substlin env name nn oll f in
              (match oll1 with
                 | [] -> (nn1,[],f'::lfe)
                 | _  ->
                     let (nn2,oll2,lfe') = substlist nn1 oll1 lfe in
                     (nn2,oll2,f'::lfe'))
	in
	let (n1,ol1,p') = substlin env name n ol p in  (* ATTENTION ERREUR *)
        (match ol1 with                                 (* si P pas affiche *)
           | [] -> (n1,[],mkCase (ci, p', d, llf))
           | _  ->
               let (n2,ol2,d') = substlin env name n1 ol1 d in
               (match ol2 with
		  | [] -> (n2,[],mkCase (ci, p', d', llf))
		  | _  -> 
	              let (n3,ol3,lf') = substlist n2 ol2 (Array.to_list llf)
                      in (n3,ol3,mkCase (ci, p', d', Array.of_list lf'))))
        
    | Cast (c1,c2)   ->
        let (n1,ol1,c1') = substlin env name n ol c1 in
        (match ol1 with 
           | [] -> (n1,[],mkCast (c1',c2))
           | _  ->
               let (n2,ol2,c2') = substlin env name n1 ol1 c2 in
               (n2,ol2,mkCast (c1',c2')))

    | Fix _ -> 
        (warning "do not consider occurrences inside fixpoints"; (n,ol,c))
	
    | CoFix _ -> 
        (warning "do not consider occurrences inside cofixpoints"; (n,ol,c))

    | (Rel _|Meta _|Var _|Sort _
      |Evar _|Const _|Ind _|Construct _) -> (n,ol,c)

let string_of_evaluable_ref = function
  | EvalVarRef id -> string_of_id id
  | EvalConstRef kn -> string_of_kn kn

let unfold env sigma name =
  if is_evaluable env name then
    clos_norm_flags (unfold_red name) env sigma
  else
    error (string_of_evaluable_ref name^" is opaque")

(* [unfoldoccs : (readable_constraints -> (int list * section_path) -> constr -> constr)]
 * Unfolds the constant name in a term c following a list of occurrences occl.
 * at the occurrences of occ_list. If occ_list is empty, unfold all occurences.
 * Performs a betaiota reduction after unfolding. *)
let unfoldoccs env sigma (occl,name) c =
  match occl with
    | []  -> unfold env sigma name c
    | l -> 
        match substlin env name 1 (Sort.list (<) l) c with
          | (_,[],uc) -> nf_betaiota_rew env uc
          | (1,_,_) -> error ((string_of_evaluable_ref name)^" does not occur")
          | _ -> error ("bad occurrence numbers of "
			^(string_of_evaluable_ref name))

(* Unfold reduction tactic: *)
let unfoldn loccname env sigma c = 
  List.fold_left (fun c occname -> unfoldoccs env sigma occname c) c loccname

(* Re-folding constants tactics: refold com in term c *)
let fold_one_com com env sigma c =
  let rcom =
    try red_product env sigma com
    with Redelimination -> error "Not reducible" in
  subst1 com (subst_term rcom c)

let fold_commands cl env sigma c =
  List.fold_right (fun com -> fold_one_com com env sigma) (List.rev cl) c


(* call by value reduction functions *)
let cbv_norm_flags flags env sigma t =
  cbv_norm (create_cbv_infos flags env) (nf_evar sigma t)

let cbv_beta = cbv_norm_flags beta empty_env Evd.empty
let cbv_betaiota = cbv_norm_flags betaiota empty_env Evd.empty
let cbv_betadeltaiota env sigma =  cbv_norm_flags betadeltaiota env sigma

let compute = cbv_betadeltaiota

(* Pattern *)

(* gives [na:ta]c' such that c converts to ([na:ta]c' a), abstracting only
 * the specified occurrences. *)

let abstract_scheme env sigma (locc,a) t =
  let ta = Retyping.get_type_of env sigma a in
  let na = named_hd env ta Anonymous in
  if occur_meta ta then error "cannot find a type for the generalisation";
  if occur_meta a then 
    mkLambda (na,ta,t)
  else 
    mkLambda (na, ta,subst_term_occ locc a t)


let pattern_occs loccs_trm env sigma c =
  let abstr_trm = List.fold_right (abstract_scheme env sigma) loccs_trm c in
  applist(abstr_trm, List.map snd loccs_trm)

(* Generic reduction: reduction functions used in reduction tactics *)

type red_expr = (constr, evaluable_global_reference) red_expr_gen

open RedFlags

let make_flag_constant = function
  | EvalVarRef id -> fVAR id
  | EvalConstRef sp -> fCONST sp

let make_flag f =
  let red = no_red in
  let red = if f.rBeta then red_add red fBETA else red in
  let red = if f.rIota then red_add red fIOTA else red in
  let red = if f.rZeta then red_add red fZETA else red in
  let red =
    if f.rDelta then (* All but rConst *)
        let red = red_add red fDELTA in
        let red = red_add_transparent red (Conv_oracle.freeze ()) in
	List.fold_right
	  (fun v red -> red_sub red (make_flag_constant v))
	  f.rConst red
    else (* Only rConst *)
        let red = red_add_transparent (red_add red fDELTA) all_opaque in
	List.fold_right
	  (fun v red -> red_add red (make_flag_constant v))
	  f.rConst red
  in red

let red_expr_tab = ref Stringmap.empty

let declare_red_expr s f =
  try 
    let _ = Stringmap.find s !red_expr_tab in
    error ("There is already a reduction expression of name "^s)
  with Not_found ->
    red_expr_tab := Stringmap.add s f !red_expr_tab

let reduction_of_redexp = function
  | Red internal -> if internal then internal_red_product else red_product
  | Hnf -> hnf_constr
  | Simpl (Some lp) -> contextually lp nf
  | Simpl None -> nf
  | Simpl_rew -> rew_nf
  | Cbv f -> cbv_norm_flags (make_flag f)
  | Lazy f -> clos_norm_flags (make_flag f)
  | Unfold ubinds -> unfoldn ubinds
  | Fold cl -> fold_commands cl
  | Pattern lp -> pattern_occs lp
  | ExtraRedExpr (s,c) -> Stringmap.find s !red_expr_tab

(* Used in several tactics. *)

exception NotStepReducible

let one_step_reduce env sigma c = 
  let rec redrec (x, largs as s) =
    match kind_of_term x with
      | Lambda (n,t,c)  ->
          (match decomp_stack largs with
             | None      -> raise NotStepReducible
             | Some (a,rest) -> (subst1 a c, rest))
      | App (f,cl) -> redrec (f, append_stack cl largs)
      | LetIn (_,f,_,cl) -> (subst1 f cl,largs)
      | Case (ci,p,c,lf) ->
          (try
	     (special_red_case sigma env (whd_betadeltaiota_state env sigma)
	       (ci,p,c,lf), largs)
           with Redelimination -> raise NotStepReducible)
      | Fix fix ->
	  (match reduce_fix (whd_betadeltaiota_state env sigma) fix largs with
             | Reduced s' -> s'
	     | NotReducible -> raise NotStepReducible)
      | Cast (c,_) -> redrec (c,largs)
      | _ when isEvalRef env x ->
	  let ref =
            try destEvalRef x
            with Redelimination -> raise NotStepReducible in
          (try
            red_elim_const env sigma ref largs
           with Redelimination ->
	     match reference_opt_value sigma env ref with
	       | Some d -> d, largs
	       | None -> raise NotStepReducible)

      | _ -> raise NotStepReducible
  in 
  app_stack (redrec (c, empty_stack))

(* put t as t'=(x1:A1)..(xn:An)B with B an inductive definition of name name
   return name, B and t' *)

let reduce_to_ind_gen allow_product env sigma t = 
  let rec elimrec env t l = 
    let c, _ = Reductionops.whd_stack t in
    match kind_of_term c with
      | Ind (mind,args) -> ((mind,args),it_mkProd_or_LetIn t l)
      | Prod (n,ty,t') ->
	  if allow_product then
	    elimrec (push_rel (n,None,t) env) t' ((n,None,ty)::l)
	  else
	     errorlabstrm "tactics__reduce_to_mind"
	       (str"Not an inductive definition")
      | _ ->
          (try 
	     let t' = nf_betaiota_rew env (one_step_reduce env sigma t) in 
	     elimrec env t' l
           with NotStepReducible ->
	     errorlabstrm "tactics__reduce_to_mind"
               (str"Not an inductive product"))
  in
  elimrec env t []

let reduce_to_quantified_ind x = reduce_to_ind_gen true x
let reduce_to_atomic_ind x = reduce_to_ind_gen false x
