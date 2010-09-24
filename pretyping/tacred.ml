(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Util
open Names
open Nameops
open Term
open Libnames
open Termops
open Namegen
open Declarations
open Inductive
open Environ
open Closure
open Reductionops
open Cbv
open Rawterm
open Pattern
open Matching

(* Errors *)

type reduction_tactic_error =
    InvalidAbstraction of env * constr * (env * Type_errors.type_error)

exception ReductionTacticError of reduction_tactic_error

(* Evaluable reference *)

exception Elimconst
exception Redelimination

let error_not_evaluable r =
  errorlabstrm "error_not_evaluable"
    (str "Cannot coerce" ++ spc () ++ Nametab.pr_global_env Idset.empty r ++
     spc () ++ str "to an evaluable reference.")

let is_evaluable_const env cst =
  is_transparent (ConstKey cst) && evaluable_constant cst env

let is_evaluable_var env id =
  is_transparent (VarKey id) && evaluable_named id env

let is_evaluable env = function
  | EvalConstRef cst -> is_evaluable_const env cst
  | EvalVarRef id -> is_evaluable_var env id

let value_of_evaluable_ref env = function
  | EvalConstRef con -> constant_value env con
  | EvalVarRef id -> Option.get (pi2 (lookup_named id env))

let constr_of_evaluable_ref = function
  | EvalConstRef con -> mkConst con
  | EvalVarRef id -> mkVar id

let evaluable_of_global_reference env = function
  | ConstRef cst when is_evaluable_const env cst -> EvalConstRef cst
  | VarRef id when is_evaluable_var env id -> EvalVarRef id
  | r -> error_not_evaluable r

let global_of_evaluable_reference = function
  | EvalConstRef cst -> ConstRef cst
  | EvalVarRef id -> VarRef id

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
  | _ -> anomaly "Not an unfoldable reference"

let reference_opt_value sigma env = function
  | EvalConst cst -> constant_opt_value env cst
  | EvalVar id ->
      let (_,v,_) = lookup_named id env in
      v
  | EvalRel n ->
      let (_,v,_) = lookup_rel n env in
      Option.map (lift n) v
  | EvalEvar ev -> Evd.existential_opt_value sigma ev

exception NotEvaluable
let reference_value sigma env c =
  match reference_opt_value sigma env c with
    | None -> raise NotEvaluable
    | Some d -> d

(************************************************************************)
(* Reduction of constants hiding a fixpoint (e.g. for "simpl" tactic).  *)
(* One reuses the name of the function after reduction of the fixpoint  *)

type constant_evaluation =
  | EliminationFix of int * int * (int * (int * constr) list * int)
  | EliminationMutualFix of
      int * evaluable_reference *
      ((int*evaluable_reference) option array *
       (int * (int * constr) list * int))
  | EliminationCases of int
  | NotAnElimination

(* We use a cache registered as a global table *)

let eval_table = ref Cmap.empty

type frozen = (int * constant_evaluation) Cmap.t

let init () =
  eval_table := Cmap.empty

let freeze () =
  !eval_table

let unfreeze ct =
  eval_table := ct

let _ =
  Summary.declare_summary "evaluation"
    { Summary.freeze_function = freeze;
      Summary.unfreeze_function = unfreeze;
      Summary.init_function = init }

(* [compute_consteval] determines whether c is an "elimination constant"

   either [yn:Tn]..[y1:T1](match yi with f1..fk end g1 ..gp)

   or     [yn:Tn]..[y1:T1](Fix(f|t) yi1..yip)
          with yi1..yip distinct variables among the yi, not occurring in t

   In the second case, [check_fix_reversibility [T1;...;Tn] args fix]
   checks that [args] is a subset of disjoint variables in y1..yn (a necessary
   condition for reversibility). It also returns the relevant
   information ([i1,Ti1;..;ip,Tip],n) in order to compute an
   equivalent of Fix(f|t) such that

   g := [xp:Tip']..[x1:Ti1'](f a1..an)
     == [xp:Tip']..[x1:Ti1'](Fix(f|t) yi1..yip)

   with a_k:=y_k if k<>i_j, a_k:=args_k otherwise, and
   Tij':=Tij[x1..xi(j-1) <- a1..ai(j-1)]

   Note that the types Tk, when no i_j=k, must not be dependent on
   the xp..x1.
*)

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
  let reversible_rels = List.map fst li in
  if not (list_distinct reversible_rels) then
    raise Elimconst;
  list_iter_i (fun i t_i ->
    if not (List.mem_assoc (i+1) li) then
      let fvs = List.map ((+) (i+1)) (Intset.elements (free_rels t_i)) in
      if list_intersect fvs reversible_rels <> [] then raise Elimconst)
    labs;
  let k = lv.(i) in
  if k < nargs then
(*  Such an optimisation would need eta-expansion
      let p = destRel (List.nth args k) in
      EliminationFix (n-p+1,(nbfix,li,n))
*)
    EliminationFix (n,nargs,(nbfix,li,n))
  else
    EliminationFix (n-nargs+k+1,nargs,(nbfix,li,n))

(* Heuristic to look if global names are associated to other
   components of a mutual fixpoint *)

let invert_name labs l na0 env sigma ref = function
  | Name id ->
      let minfxargs = List.length l in
      if na0 <> Name id then
	let refi = match ref with
	  | EvalRel _ | EvalEvar _ -> None
	  | EvalVar id' -> Some (EvalVar id)
	  | EvalConst kn ->
	      let (mp,dp,_) = repr_con kn in
	      Some (EvalConst (make_con mp dp (label_of_id id))) in
	match refi with
	  | None -> None
	  | Some ref ->
	      try match reference_opt_value sigma env ref with
		| None -> None
		| Some c ->
		    let labs',ccl = decompose_lam c in
		    let _, l' = whd_betalet_stack sigma ccl in
		    let labs' = List.map snd labs' in
		    if labs' = labs & l = l' then Some (minfxargs,ref)
                    else None
	      with Not_found (* Undefined ref *) -> None
      else Some (minfxargs,ref)
  | Anonymous -> None (* Actually, should not occur *)

(* [compute_consteval_direct] expand all constant in a whole, but
   [compute_consteval_mutual_fix] only one by one, until finding the
   last one before the Fix if the latter is mutually defined *)

let compute_consteval_direct sigma env ref =
  let rec srec env n labs c =
    let c',l = whd_betadelta_stack env sigma c in
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
    let c',l = whd_betalet_stack sigma c in
    let nargs = List.length l in
    match kind_of_term c' with
      | Lambda (na,t,g) when l=[] ->
	  srec (push_rel (na,None,t) env) (minarg+1) (t::labs) ref g
      | Fix ((lv,i),(names,_,_)) ->
	  (* Last known constant wrapping Fix is ref = [labs](Fix l) *)
	  (match compute_consteval_direct sigma env ref with
	     | NotAnElimination -> (*Above const was eliminable but this not!*)
		 NotAnElimination
	     | EliminationFix (minarg',minfxargs,infos) ->
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
    | EliminationFix (_,_,(nbfix,_,_)) when nbfix <> 1 ->
	compute_consteval_mutual_fix sigma env ref
    | elim -> elim

let reference_eval sigma env = function
  | EvalConst cst as ref ->
      (try
	 Cmap.find cst !eval_table
       with Not_found -> begin
	 let v = compute_consteval sigma env ref in
	 eval_table := Cmap.add cst v !eval_table;
	 v
       end)
  | ref -> compute_consteval sigma env ref

(* If f is bound to EliminationFix (n',infos), then n' is the minimal
   number of args for starting the reduction and infos is
   (nbfix,[(yi1,Ti1);...;(yip,Tip)],n) indicating that f converts
   to some [y1:T1,...,yn:Tn](Fix(..) yip .. yi1) where the y_{i_j} consist in a
   disjoint subset of the yi, i.e. 1 <= ij <= n and the ij are disjoint (in
   particular, p <= n).

   f is applied to largs := arg1 .. argn and we need for recursive
   calls to build the function

      g := [xp:Tip',...,x1:Ti1'](f a1 ... an)

   s.t. (g u1 ... up) reduces to (Fix(..) u1 ... up)

   This is made possible by setting
      a_k:=x_j    if k=i_j for some j
      a_k:=arg_k  otherwise

   The type Tij' is Tij[yi(j-1)..y1 <- ai(j-1)..a1]
*)

let x = Name (id_of_string "x")

let make_elim_fun (names,(nbfix,lv,n)) largs =
  let lu = list_firstn n (list_of_stack largs) in
  let p = List.length lv in
  let lyi = List.map fst lv in
  let la =
    list_map_i (fun q aq ->
      (* k from the comment is q+1 *)
      try mkRel (p+1-(list_index (n-q) lyi))
      with Not_found -> aq)
      0 (List.map (lift p) lu)
  in
  fun i ->
    match names.(i) with
      | None -> None
      | Some (minargs,ref) ->
          let body = applistc (mkEvalRef ref) la in
          let g =
            list_fold_left_i (fun q (* j = n+1-q *) c (ij,tij) ->
              let subst = List.map (lift (-q)) (list_firstn (n-ij) la) in
              let tij' = substl (List.rev subst) tij in
	      mkLambda (x,tij',c)) 1 body (List.rev lv)
          in Some (minargs,g)

(* [f] is convertible to [Fix(recindices,bodynum),bodyvect)]:
   do so that the reduction uses this extra information *)

let dummy = mkProp
let vfx = id_of_string"_expanded_fix_"
let vfun = id_of_string"_eliminator_function_"

(* Mark every occurrence of substituted vars (associated to a function)
   as a problem variable: an evar that can be instantiated either by
   vfx (expanded fixpoint) or vfun (named function). *)
let substl_with_function subst constr =
  let cnt = ref 0 in
  let evd = ref Evd.empty in
  let minargs = ref Intmap.empty in
  let v = Array.of_list subst in
  let rec subst_total k c =
    match kind_of_term c with
        Rel i when k<i ->
          if i <= k + Array.length v then
            match v.(i-k-1) with
              | (fx,Some(min,ref)) ->
                  decr cnt;
                  evd := Evd.add !evd !cnt
                    (Evd.make_evar
                      (val_of_named_context
                        [(vfx,None,dummy);(vfun,None,dummy)])
                      dummy);
                  minargs := Intmap.add !cnt min !minargs;
                  lift k (mkEvar(!cnt,[|fx;ref|]))
              | (fx,None) -> lift k fx
          else mkRel (i - Array.length v)
      | _ ->
          map_constr_with_binders succ subst_total k c in
  let c = subst_total 0 constr in
  (c,!evd,!minargs)

exception Partial

(* each problem variable that cannot be made totally applied even by
   reduction is solved by the expanded fix term. *)
let solve_arity_problem env sigma fxminargs c =
  let evm = ref sigma in
  let set_fix i = evm := Evd.define i (mkVar vfx) !evm in
  let rec check strict c =
    let c' = whd_betaiotazeta sigma c in
    let (h,rcargs) = decompose_app c' in
    match kind_of_term h with
        Evar(i,_) when Intmap.mem i fxminargs && not (Evd.is_defined !evm i) ->
          let minargs = Intmap.find i fxminargs in
          if List.length rcargs < minargs then
            if strict then set_fix i
            else raise Partial;
          List.iter (check strict) rcargs
      | (Var _|Const _) when isEvalRef env h ->
          (match reference_opt_value sigma env (destEvalRef h) with
              Some h' ->
                let bak = !evm in
                (try List.iter (check false) rcargs
                with Partial ->
                  evm := bak;
                  check strict (applist(h',rcargs)))
            | None -> List.iter (check strict) rcargs)
      | _ -> iter_constr (check strict) c' in
  check true c;
  !evm

let substl_checking_arity env subst c =
  (* we initialize the problem: *)
  let body,sigma,minargs = substl_with_function subst c in
  (* we collect arity constraints *)
  let sigma' = solve_arity_problem env sigma minargs body in
  (* we propagate the constraints: solved problems are substituted;
     the other ones are replaced by the function symbol *)
  let rec nf_fix c =
    match kind_of_term c with
        Evar(i,[|fx;f|] as ev) when Intmap.mem i minargs ->
          (match Evd.existential_opt_value sigma' ev with
              Some c' -> c'
            | None -> f)
      | _ -> map_constr nf_fix c in
  nf_fix body



let contract_fix_use_function env sigma f
  ((recindices,bodynum),(_names,_types,bodies as typedbodies)) =
  let nbodies = Array.length recindices in
  let make_Fi j = (mkFix((recindices,j),typedbodies), f j) in
  let lbodies = list_tabulate make_Fi nbodies in
  substl_checking_arity env (List.rev lbodies) (nf_beta sigma bodies.(bodynum))

let reduce_fix_use_function env sigma f whfun fix stack =
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
	       Reduced (contract_fix_use_function env sigma f fix,stack')
	   | _ -> NotReducible)

let contract_cofix_use_function env sigma f
  (bodynum,(_names,_,bodies as typedbodies)) =
  let nbodies = Array.length bodies in
  let make_Fi j = (mkCoFix(j,typedbodies), f j) in
  let subbodies = list_tabulate make_Fi nbodies in
  substl_checking_arity env (List.rev subbodies)
    (nf_beta sigma bodies.(bodynum))

let reduce_mind_case_use_function func env sigma mia =
  match kind_of_term mia.mconstr with
    | Construct(ind_sp,i) ->
	let real_cargs = list_skipn mia.mci.ci_npar mia.mcargs in
	applist (mia.mlf.(i-1), real_cargs)
    | CoFix (bodynum,(names,_,_) as cofix) ->
	let build_cofix_name =
	  if isConst func then
	    let (mp,dp,_) = repr_con (destConst func) in
            let minargs = List.length mia.mcargs in
	    fun i ->
	      if i = bodynum then Some (minargs,func)
	      else match names.(i) with
		| Anonymous -> None
		| Name id ->
		    (* In case of a call to another component of a block of
		       mutual inductive, try to reuse the global name if
		       the block was indeed initially built as a global
		       definition *)
		    let kn = make_con mp dp (label_of_id id) in
		    try match constant_opt_value env kn with
		      | None -> None
                          (* TODO: check kn is correct *)
		      | Some _ -> Some (minargs,mkConst kn)
		    with Not_found -> None
	  else
	    fun _ -> None in
	let cofix_def =
          contract_cofix_use_function env sigma build_cofix_name cofix in
	mkCase (mia.mci, mia.mP, applist(cofix_def,mia.mcargs), mia.mlf)
    | _ -> assert false

let special_red_case env sigma whfun (ci, p, c, lf)  =
  let rec redrec s =
    let (constr, cargs) = whfun s in
    if isEvalRef env constr then
      let ref = destEvalRef constr in
      match reference_opt_value sigma env ref with
        | None -> raise Redelimination
        | Some gvalue ->
	    if reducible_mind_case gvalue then
	      reduce_mind_case_use_function constr env sigma
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

(* [red_elim_const] contracts iota/fix/cofix redexes hidden behind
   constants by keeping the name of the constants in the recursive calls;
   it fails if no redex is around *)

let rec red_elim_const env sigma ref largs =
  match reference_eval sigma env ref with
    | EliminationCases n when stack_args_size largs >= n ->
	let c = reference_value sigma env ref in
	let c', lrest = whd_betadelta_state env sigma (c,largs) in
	let whfun = whd_simpl_state env sigma in
        (special_red_case env sigma whfun (destCase c'), lrest)
    | EliminationFix (min,minfxargs,infos) when stack_args_size largs >=min ->
	let c = reference_value sigma env ref in
	let d, lrest = whd_betadelta_state env sigma (c,largs) in
	let f = make_elim_fun ([|Some (minfxargs,ref)|],infos) largs in
	let whfun = whd_construct_state env sigma in
	(match reduce_fix_use_function env sigma f whfun (destFix d) lrest with
	   | NotReducible -> raise Redelimination
	   | Reduced (c,rest) -> (nf_beta sigma c, rest))
    | EliminationMutualFix (min,refgoal,refinfos)
	when stack_args_size largs >= min ->
	let rec descend ref args =
	  let c = reference_value sigma env ref in
	  if ref = refgoal then
	    (c,args)
	  else
	    let c', lrest = whd_betalet_state sigma (c,args) in
	    descend (destEvalRef c') lrest in
	let (_, midargs as s) = descend ref largs in
	let d, lrest = whd_betadelta_state env sigma s in
	let f = make_elim_fun refinfos midargs in
	let whfun = whd_construct_state env sigma in
	(match reduce_fix_use_function env sigma f whfun (destFix d) lrest with
	   | NotReducible -> raise Redelimination
	   | Reduced (c,rest) -> (nf_beta sigma c, rest))
    | _ -> raise Redelimination

(* reduce to whd normal form or to an applied constant that does not hide
   a reducible iota/fix/cofix redex (the "simpl" tactic) *)

and whd_simpl_state env sigma s =
  let rec redrec (x, stack as s) =
    match kind_of_term x with
      | Lambda (na,t,c) ->
          (match decomp_stack stack with
             | None -> s
             | Some (a,rest) -> stacklam redrec [a] c rest)
      | LetIn (n,b,t,c) -> stacklam redrec [b] c stack
      | App (f,cl) -> redrec (f, append_stack cl stack)
      | Cast (c,_,_) -> redrec (c, stack)
      | Case (ci,p,c,lf) ->
          (try
	    redrec (special_red_case env sigma redrec (ci,p,c,lf), stack)
	  with
	      Redelimination -> s)
      | Fix fix ->
	  (try match reduce_fix (whd_construct_state env) sigma fix stack with
            | Reduced s' -> redrec s'
	    | NotReducible -> s
	  with Redelimination -> s)
      | _ when isEvalRef env x ->
	  let ref = destEvalRef x in
          (try
	    redrec (red_elim_const env sigma ref stack)
           with Redelimination ->
	     s)
      | _ -> s
  in
  redrec s

(* reduce until finding an applied constructor or fail *)

and whd_construct_state env sigma s =
  let (constr, cargs as s') = whd_simpl_state env sigma s in
  if reducible_mind_case constr then s'
  else if isEvalRef env constr then
    let ref = destEvalRef constr in
    match reference_opt_value sigma env ref with
      | None -> raise Redelimination
      | Some gvalue -> whd_construct_state env sigma (gvalue, cargs)
  else
    raise Redelimination

(************************************************************************)
(*            Special Purpose Reduction Strategies                     *)

(* Red reduction tactic: one step of delta reduction + full
   beta-iota-fix-cofix-zeta-cast at the head of the conclusion of a
   sequence of products; fails if no delta redex is around
*)

let try_red_product env sigma c =
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
      | Cast (c,_,_) -> redrec env c
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
  try try_red_product env sigma c
  with Redelimination -> error "Not reducible."

(*
(* This old version of hnf uses betadeltaiota instead of itself (resp
   whd_construct_state) to reduce the argument of Case (resp Fix);
   The new version uses the "simpl" strategy instead. For instance,

   Variable n:nat.
   Eval hnf in match (plus (S n) O) with S n => n | _ => O end.

   returned

   (fix plus (n m : nat) {struct n} : nat :=
        match n with
        | O => m
        | S p => S (plus p m)
        end) n 0

   while the new version returns (plus n O)
 *)

let whd_simpl_orelse_delta_but_fix_old env sigma c =
  let whd_all = whd_betadeltaiota_state env sigma in
  let rec redrec (x, stack as s) =
    match kind_of_term x with
      | Lambda (na,t,c) ->
          (match decomp_stack stack with
             | None      -> s
             | Some (a,rest) -> stacklam redrec [a] c rest)
      | LetIn (n,b,t,c) -> stacklam redrec [b] c stack
      | App (f,cl)   -> redrec (f, append_stack cl stack)
      | Cast (c,_,_) -> redrec (c, stack)
      | Case (ci,p,d,lf) ->
          (try
             redrec (special_red_case env sigma whd_all (ci,p,d,lf), stack)
           with Redelimination ->
	     s)
      | Fix fix ->
	  (match reduce_fix whd_all fix stack with
             | Reduced s' -> redrec s'
	     | NotReducible -> s)
      | _ when isEvalRef env x ->
	  let ref = destEvalRef x in
          (try
	    redrec (red_elim_const env sigma ref stack)
           with Redelimination ->
             match reference_opt_value sigma env ref with
	       | Some c ->
		   (match kind_of_term ((strip_lam c)) with
                     | CoFix _ | Fix _ -> s
		     | _ -> redrec (c, stack))
	       | None -> s)
      | _ -> s
  in app_stack (redrec (c, empty_stack))
*)

(* Same as [whd_simpl] but also reduces constants that do not hide a
   reducible fix, but does this reduction of constants only until it
   it immediately hides a non reducible fix or a cofix *)

let whd_simpl_orelse_delta_but_fix env sigma c =
  let rec redrec s =
    let (constr, stack as s') = whd_simpl_state env sigma s in
    if isEvalRef env constr then
      match reference_opt_value sigma env (destEvalRef constr) with
	| Some c ->
	    (match kind_of_term ((strip_lam c)) with
              | CoFix _ | Fix _ -> s'
	      | _ -> redrec (c, stack))
	| None -> s'
    else s'
  in app_stack (redrec (c, empty_stack))

let hnf_constr = whd_simpl_orelse_delta_but_fix

(* The "simpl" reduction tactic *)

let whd_simpl env sigma c =
  app_stack (whd_simpl_state env sigma (c, empty_stack))

let simpl env sigma c = strong whd_simpl env sigma c

(* Reduction at specific subterms *)

let matches_head c t =
  match kind_of_term t with
    | App (f,_) -> matches c f
    | _ -> raise PatternMatchingFailure

let contextually byhead ((nowhere_except_in,locs),c) f env sigma t =
  let maxocc = List.fold_right max locs 0 in
  let pos = ref 1 in
  let rec traverse (env,c as envc) t =
    if nowhere_except_in & (!pos > maxocc) then t
    else
    try
      let subst = if byhead then matches_head c t else matches c t in
      let ok =
	if nowhere_except_in then List.mem !pos locs
	else not (List.mem !pos locs) in
      incr pos;
      if ok then
	f subst env sigma t
      else if byhead then
	(* find other occurrences of c in t; TODO: ensure left-to-right *)
        let (f,l) = destApp t in
	mkApp (f, array_map_left (traverse envc) l)
      else
	t
    with PatternMatchingFailure ->
      map_constr_with_binders_left_to_right
	(fun d (env,c) -> (push_rel d env,lift_pattern 1 c))
        traverse envc t
  in
  let t' = traverse (env,c) t in
  if List.exists (fun o -> o >= !pos) locs then error_invalid_occurrence locs;
  t'

(* linear bindings (following pretty-printer) of the value of name in c.
 * n is the number of the next occurence of name.
 * ol is the occurence list to find. *)

let substlin env evalref n (nowhere_except_in,locs) c =
  let maxocc = List.fold_right max locs 0 in
  let pos = ref n in
  assert (List.for_all (fun x -> x >= 0) locs);
  let value = value_of_evaluable_ref env evalref in
  let term = constr_of_evaluable_ref evalref in
  let rec substrec () c =
    if nowhere_except_in & !pos > maxocc then c
    else if c = term then
      let ok =
	if nowhere_except_in then List.mem !pos locs
	else not (List.mem !pos locs) in
      incr pos;
      if ok then value else c
    else
      map_constr_with_binders_left_to_right
	(fun _ () -> ())
        substrec () c
  in
  let t' = substrec () c in
  (!pos, t')

let string_of_evaluable_ref env = function
  | EvalVarRef id -> string_of_id id
  | EvalConstRef kn ->
      string_of_qualid
        (Nametab.shortest_qualid_of_global (vars_of_env env) (ConstRef kn))

let unfold env sigma name =
  if is_evaluable env name then
    clos_norm_flags (unfold_red name) env sigma
  else
    error (string_of_evaluable_ref env name^" is opaque.")

(* [unfoldoccs : (readable_constraints -> (int list * full_path) -> constr -> constr)]
 * Unfolds the constant name in a term c following a list of occurrences occl.
 * at the occurrences of occ_list. If occ_list is empty, unfold all occurences.
 * Performs a betaiota reduction after unfolding. *)
let unfoldoccs env sigma ((nowhere_except_in,locs as plocs),name) c =
  if locs = [] then if nowhere_except_in then c else unfold env sigma name c
  else
    let (nbocc,uc) = substlin env name 1 plocs c in
    if nbocc = 1 then
      error ((string_of_evaluable_ref env name)^" does not occur.");
    let rest = List.filter (fun o -> o >= nbocc) locs in
    if rest <> [] then error_invalid_occurrence rest;
    nf_betaiota sigma uc

(* Unfold reduction tactic: *)
let unfoldn loccname env sigma c =
  List.fold_left (fun c occname -> unfoldoccs env sigma occname c) c loccname

(* Re-folding constants tactics: refold com in term c *)
let fold_one_com com env sigma c =
  let rcom =
    try red_product env sigma com
    with Redelimination -> error "Not reducible." in
  (* Reason first on the beta-iota-zeta normal form of the constant as
     unfold produces it, so that the "unfold f; fold f" configuration works
     to refold fix expressions *)
  let a = subst_term (clos_norm_flags unfold_side_red env sigma rcom) c in
  if not (eq_constr a c) then
    subst1 com a
  else
    (* Then reason on the non beta-iota-zeta form for compatibility -
       even if it is probably a useless configuration *)
    let a = subst_term rcom c in
    subst1 com a

let fold_commands cl env sigma c =
  List.fold_right (fun com -> fold_one_com com env sigma) (List.rev cl) c


(* call by value reduction functions *)
let cbv_norm_flags flags env sigma t =
  cbv_norm (create_cbv_infos flags env sigma) t

let cbv_beta = cbv_norm_flags beta empty_env
let cbv_betaiota = cbv_norm_flags betaiota empty_env
let cbv_betadeltaiota env sigma =  cbv_norm_flags betadeltaiota env sigma

let compute = cbv_betadeltaiota

(* Pattern *)

(* gives [na:ta]c' such that c converts to ([na:ta]c' a), abstracting only
 * the specified occurrences. *)

let abstract_scheme env sigma (locc,a) c =
  let ta = Retyping.get_type_of env sigma a in
  let na = named_hd env ta Anonymous in
  if occur_meta ta then error "Cannot find a type for the generalisation.";
  if occur_meta a then
    mkLambda (na,ta,c)
  else
    mkLambda (na,ta,subst_term_occ locc a c)

let pattern_occs loccs_trm env sigma c =
  let abstr_trm = List.fold_right (abstract_scheme env sigma) loccs_trm c in
  try
    let _ = Typing.type_of env sigma abstr_trm in
    applist(abstr_trm, List.map snd loccs_trm)
  with Type_errors.TypeError (env',t) ->
    raise (ReductionTacticError (InvalidAbstraction (env,abstr_trm,(env',t))))

(* Used in several tactics. *)

(* put t as t'=(x1:A1)..(xn:An)B with B an inductive definition of name name
   return name, B and t' *)

let reduce_to_ind_gen allow_product env sigma t =
  let rec elimrec env t l =
    let t = hnf_constr env sigma t in
    match kind_of_term (fst (decompose_app t)) with
      | Ind ind-> (ind, it_mkProd_or_LetIn t l)
      | Prod (n,ty,t') ->
	  if allow_product then
	    elimrec (push_rel (n,None,ty) env) t' ((n,None,ty)::l)
	  else
	    errorlabstrm "" (str"Not an inductive definition.")
      | _ ->
	  (* Last chance: we allow to bypass the Opaque flag (as it
	     was partially the case between V5.10 and V8.1 *)
	  let t' = whd_betadeltaiota env sigma t in
	  match kind_of_term (fst (decompose_app t')) with
	    | Ind ind-> (ind, it_mkProd_or_LetIn t' l)
	    | _ -> errorlabstrm "" (str"Not an inductive product.")
  in
  elimrec env t []

let reduce_to_quantified_ind x = reduce_to_ind_gen true x
let reduce_to_atomic_ind x = reduce_to_ind_gen false x

(* Reduce the weak-head redex [beta,iota/fix/cofix[all],cast,zeta,simpl/delta]
   or raise [NotStepReducible] if not a weak-head redex *)

exception NotStepReducible

let one_step_reduce env sigma c =
  let rec redrec (x, stack) =
    match kind_of_term x with
      | Lambda (n,t,c)  ->
          (match decomp_stack stack with
             | None      -> raise NotStepReducible
             | Some (a,rest) -> (subst1 a c, rest))
      | App (f,cl) -> redrec (f, append_stack cl stack)
      | LetIn (_,f,_,cl) -> (subst1 f cl,stack)
      | Cast (c,_,_) -> redrec (c,stack)
      | Case (ci,p,c,lf) ->
          (try
	     (special_red_case env sigma (whd_simpl_state env sigma)
	       (ci,p,c,lf), stack)
           with Redelimination -> raise NotStepReducible)
      | Fix fix ->
	  (match reduce_fix (whd_construct_state env) sigma fix stack with
             | Reduced s' -> s'
	     | NotReducible -> raise NotStepReducible)
      | _ when isEvalRef env x ->
	  let ref = destEvalRef x in
          (try
            red_elim_const env sigma ref stack
           with Redelimination ->
	     match reference_opt_value sigma env ref with
	       | Some d -> d, stack
	       | None -> raise NotStepReducible)

      | _ -> raise NotStepReducible
  in
  app_stack (redrec (c, empty_stack))

let isIndRef = function IndRef _ -> true | _ -> false

let reduce_to_ref_gen allow_product env sigma ref t =
  if isIndRef ref then
    let (mind,t) = reduce_to_ind_gen allow_product env sigma t in
    if IndRef mind <> ref then
      errorlabstrm "" (str "Cannot recognize a statement based on " ++
        Nametab.pr_global_env Idset.empty ref ++ str".")
    else
      t
  else
  (* lazily reduces to match the head of [t] with the expected [ref] *)
  let rec elimrec env t l =
    let c, _ = Reductionops.whd_stack sigma t in
    match kind_of_term c with
      | Prod (n,ty,t') ->
	  if allow_product then
	    elimrec (push_rel (n,None,t) env) t' ((n,None,ty)::l)
	  else
	     errorlabstrm ""
	       (str "Cannot recognize an atomic statement based on " ++
	        Nametab.pr_global_env Idset.empty ref ++ str".")
      | _ ->
	  try
	    if global_of_constr c = ref
	    then it_mkProd_or_LetIn t l
	    else raise Not_found
	  with Not_found ->
          try
	    let t' = nf_betaiota sigma (one_step_reduce env sigma t) in
	    elimrec env t' l
          with NotStepReducible ->
	    errorlabstrm ""
	      (str "Cannot recognize a statement based on " ++
	       Nametab.pr_global_env Idset.empty ref ++ str".")
  in
  elimrec env t []

let reduce_to_quantified_ref = reduce_to_ref_gen true
let reduce_to_atomic_ref = reduce_to_ref_gen false
