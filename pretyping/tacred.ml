
(* $Id$ *)

open Pp
open Util
open Names
(* open Generic *)
open Term
open Inductive
open Environ
open Reduction
open Instantiate
open Redinfo

exception Elimconst
exception Redelimination

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

let make_elim_fun f lv n largs =
  let (sp,args) = destConst f in
  let labs,_ = list_chop n (list_of_stack largs) in
  let p = List.length lv in
  let ylv = List.map fst lv in
  let la' = list_map_i 
	      (fun q aq ->
		 try (Rel (p+1-(list_index (n-q) ylv))) 
		 with Not_found -> aq) 0
              (List.map (lift p) labs) 
  in 
  fun id -> 
    let fi = mkConst (make_path (dirpath sp) id (kind_of_path sp),args) in
    list_fold_left_i 
      (fun i c (k,a) -> 
	 mkLambda (Name(id_of_string"x"),
		   substl (rev_firstn_liftn (n-k) (-i) la') a,
		   c))
      0 (applistc fi la') lv

(* [f] is convertible to [Fix(recindices,bodynum),bodyvect)] make 
   the reduction using this extra information *)

let contract_fix_use_function f
  ((recindices,bodynum),(types,names,bodies as typedbodies)) =
  let nbodies = Array.length recindices in
  let make_Fi j =
    match List.nth names j with Name id -> f id | _ -> assert false in
  let lbodies = list_tabulate make_Fi nbodies in
  substl (List.rev lbodies) bodies.(bodynum)

let reduce_fix_use_function f whfun fix stack =
  match fix_recarg fix stack with
    | None -> NotReducible
    | Some (recargnum,recarg) ->
        let (recarg'hd,_ as recarg')= whfun (recarg, empty_stack) in
        let stack' = stack_assign stack recargnum (app_stack recarg') in
	(match kind_of_term recarg'hd with
           | IsMutConstruct _ ->
	       Reduced (contract_fix_use_function f fix,stack')
	   | _ -> NotReducible)

let contract_cofix_use_function f (bodynum,(_,names,bodies as typedbodies)) =
  let nbodies = Array.length bodies in
  let make_Fi j =
    match List.nth names j with Name id -> f id | _ -> assert false in
  let subbodies = list_tabulate make_Fi nbodies in
  substl subbodies bodies.(bodynum)

let reduce_mind_case_use_function env f mia =
  match kind_of_term mia.mconstr with 
    | IsMutConstruct(ind_sp,i as cstr_sp, args) ->
	let ncargs = (fst mia.mci).(i-1) in
	let real_cargs = list_lastn ncargs mia.mcargs in
	applist (mia.mlf.(i-1), real_cargs)
    | IsCoFix cofix ->
	let cofix_def = contract_cofix_use_function f cofix in
	mkMutCase (mia.mci, mia.mP, applist(cofix_def,mia.mcargs), mia.mlf)
    | _ -> assert false
	  
let special_red_case env whfun p c ci lf  =
  let rec redrec s = 
    let (constr, cargs) = whfun s in 
    match kind_of_term constr with 
      | IsConst (sp,args) -> 
          if evaluable_constant env constr then
            let gvalue = constant_value env constr in
            if reducible_mind_case gvalue then
	      let build_fix_name id =
		mkConst (make_path (dirpath sp) id (kind_of_path sp),args)
	      in reduce_mind_case_use_function env build_fix_name
                   {mP=p; mconstr=gvalue; mcargs=list_of_stack cargs;
		    mci=ci; mlf=lf}
            else 
	      redrec (gvalue, cargs)
          else 
	    raise Redelimination
      | _ ->
          if reducible_mind_case constr then
            reduce_mind_case
	      {mP=p; mconstr=constr; mcargs=list_of_stack cargs;
	       mci=ci; mlf=lf}
          else 
	    raise Redelimination
  in 
  redrec (c, empty_stack)

let rec red_elim_const env sigma k largs =
  if not (evaluable_constant env k) then raise Redelimination;
  let (sp, args) = destConst k in
  let elim_style = constant_eval sp in
  match elim_style with
    | EliminationCases n when stack_args_size largs >= n -> begin
	let c = constant_value env k in
	let c', lrest = whd_betadeltaeta_state env sigma (c,largs) in
	match kind_of_term c' with
	  | IsMutCase (ci,p,c,lf) ->
              (special_red_case env (construct_const env sigma) p c ci lf,
	       lrest)
	  | _ -> assert false
      end
    | EliminationFix (lv,n) when stack_args_size largs >= n -> begin
	let c = constant_value env k in
	let d, lrest = whd_betadeltaeta_state env sigma (c, largs) in
	match kind_of_term d with
	  | IsFix fix -> 
	      let f id = make_elim_fun k lv n largs id in
	      let co = construct_const env sigma in
	      (match reduce_fix_use_function f co fix lrest with
		| NotReducible -> raise Redelimination
		| Reduced (c,rest) -> (nf_beta env sigma c, rest))
	  | _ -> assert false
      end
    | _ -> raise Redelimination

and construct_const env sigma = 
  let rec hnfstack (x, stack as s) =
    match kind_of_term x with
      | IsConst _  ->
          (try
	     hnfstack (red_elim_const env sigma x stack)
           with Redelimination ->
             if evaluable_constant env x then 
	       let cval = constant_value env x in
	       (match kind_of_term cval with
                  | IsCoFix _ -> s
                  | _ -> hnfstack (cval, stack))
             else 
	       raise Redelimination)
      | IsCast (c,_) -> hnfstack (c, stack)
      | IsAppL (f,cl) -> hnfstack (f, append_stack cl stack)
      | IsLambda (_,_,c) ->
          (match decomp_stack stack with 
             | None -> assert false
             | Some (c',rest) -> stacklam hnfstack [c'] c rest)
      | IsMutCase (ci,p,c,lf) ->
          hnfstack 
	    (special_red_case env (construct_const env sigma) p c ci lf, stack)
      | IsMutConstruct _ -> s
      | IsCoFix _ -> s
      | IsFix fix -> 
	  (match reduce_fix hnfstack fix stack with
             | Reduced s' -> hnfstack s'
	     | NotReducible -> raise Redelimination)
      | _ -> raise Redelimination
  in 
  hnfstack

(* Hnf reduction tactic: *)

let hnf_constr env sigma c = 
  let rec redrec (x, largs as s) =
    match kind_of_term x with
      | IsLambda (n,t,c) ->
          (match decomp_stack largs with
             | None      -> app_stack s
             | Some (a,rest) -> stacklam redrec [a] c rest)
      | IsAppL (f,cl)   -> redrec (f, append_stack cl largs)
      | IsConst _ ->
          (try
             let (c',lrest) = red_elim_const env sigma x largs in 
	     redrec (c', lrest)
           with Redelimination ->
             if evaluable_constant env x then
               let c = constant_value env x in
	       (match kind_of_term c with 
                  | IsCoFix _ -> app_stack (x,largs)
		  | _ ->  redrec (c, largs))
             else 
	       app_stack s)
      | IsCast (c,_) -> redrec (c, largs)
      | IsMutCase (ci,p,c,lf) ->
          (try
             redrec 
	       (special_red_case env (whd_betadeltaiota_state env sigma) 
		  p c ci lf, largs)
           with Redelimination -> 
	     app_stack s)
      | IsFix fix ->
	  (match reduce_fix (whd_betadeltaiota_state env sigma) fix largs with
             | Reduced s' -> redrec s'
	     | NotReducible -> app_stack s)
      | _ -> app_stack s
  in 
  redrec (c, empty_stack)

(* Simpl reduction tactic: same as simplify, but also reduces
   elimination constants *)

let whd_nf env sigma c = 
  let rec nf_app (c, stack as s) =
    match kind_of_term c with
      | IsLambda (name,c1,c2)    ->
          (match decomp_stack stack with
             | None -> (c,empty_stack)
             | Some (a1,rest) -> stacklam nf_app [a1] c2 rest)
      | IsAppL (f,cl) -> nf_app (f, append_stack cl stack)
      | IsCast (c,_) -> nf_app (c, stack)
      | IsConst _ ->
          (try
	     nf_app (red_elim_const env sigma c stack)
           with Redelimination -> 
	     s)
      | IsMutCase (ci,p,d,lf) ->
          (try
             nf_app (special_red_case env nf_app p d ci lf, stack)
           with Redelimination -> 
	     s)
      | IsFix fix ->
	  (match reduce_fix nf_app fix stack with
             | Reduced s' -> nf_app s'
	     | NotReducible -> s)
      | _ -> s
  in 
  app_stack (nf_app (c, empty_stack))

let nf env sigma c = strong whd_nf env sigma c

(* Generic reduction: reduction functions used in reduction tactics *)

type red_expr =
  | Red
  | Hnf
  | Simpl
  | Cbv of Closure.flags
  | Lazy of Closure.flags
  | Unfold of (int list * section_path) list
  | Fold of constr list
  | Pattern of (int list * constr * constr) list

let reduction_of_redexp = function
  | Red -> red_product
  | Hnf -> hnf_constr
  | Simpl -> nf
  | Cbv f -> cbv_norm_flags f
  | Lazy f -> clos_norm_flags f
  | Unfold ubinds -> unfoldn ubinds
  | Fold cl -> fold_commands cl
  | Pattern lp -> pattern_occs lp

(* Used in several tactics. *)

let one_step_reduce env sigma c = 
  let rec redrec (x, largs as s) =
    match kind_of_term x with
      | IsLambda (n,t,c)  ->
          (match decomp_stack largs with
             | None      -> error "Not reducible 1"
             | Some (a,rest) -> (subst1 a c, rest))
      | IsAppL (f,cl) -> redrec (f, append_stack cl largs)
      | IsConst _ ->
          (try
             red_elim_const env sigma x largs
           with Redelimination ->
             if evaluable_constant env x then
               constant_value env x, largs
             else error "Not reductible 1")

      | IsMutCase (ci,p,c,lf) ->
          (try
	     (special_red_case env (whd_betadeltaiota_state env sigma)
	       p c ci lf, largs)
           with Redelimination -> error "Not reducible 2")
      | IsFix fix ->
	  (match reduce_fix (whd_betadeltaiota_state env sigma) fix largs with
             | Reduced s' -> s'
	     | NotReducible -> error "Not reducible 3")
      | IsCast (c,_) -> redrec (c,largs)
      | _ -> error "Not reducible 3"
  in 
  app_stack (redrec (c, empty_stack))

(* put t as t'=(x1:A1)..(xn:An)B with B an inductive definition of name name
   return name, B and t' *)

let reduce_to_mind env sigma t = 
  let rec elimrec t l = 
    let c, _ = whd_castapp_stack t [] in
    match kind_of_term c with
      | IsMutInd (mind,args) -> ((mind,args),t,it_mkProd_or_LetIn t l)
      | IsConst _ | IsMutCase _ ->
          (try 
	     let t' = nf_betaiota env sigma (one_step_reduce env sigma t) in 
	     elimrec t' l
           with UserError _ -> errorlabstrm "tactics__reduce_to_mind"
               [< 'sTR"Not an inductive product." >])
      | IsProd (n,ty,t') ->
	let ty' = Retyping.get_assumption_of (Global.env()) Evd.empty ty in
	elimrec t' ((n,None,ty')::l)
      | IsLetIn (n,b,ty,t') ->
	  let ty' = Retyping.get_assumption_of (Global.env()) Evd.empty ty in
	  elimrec t' ((n,Some b,ty')::l)
      | _ -> error "Not an inductive product"
 in
 elimrec t []

let reduce_to_ind env sigma t =
  let ((ind_sp,_),redt,c) = reduce_to_mind env sigma t in 
  (Declare.path_of_inductive_path ind_sp, redt, c)
