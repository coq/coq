
(* $Id$ *)

open Pp
open Util
open Names
open Term
open Inductive
open Environ
open Reduction
open Instantiate

(************************************************************************)
(* Reduction of constant hiding fixpoints (e.g. for Simpl). The trick   *)
(* is to reuse the name of the function after reduction of the fixpoint *)

exception Elimconst
exception Redelimination

type constant_evaluation = 
  | EliminationFix of int * (constant * int * (int * constr) list * int)
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
      Summary.init_function = init }


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

let check_fix_reversibility cst labs args ((lv,i),(tys,_,bds)) =
  let n = List.length labs in
  let nargs = List.length args in
  if nargs > n then raise Elimconst;
  let nbfix = Array.length bds in
  let li =
    List.map
      (function d -> match kind_of_term d with
         | IsRel k ->
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
    EliminationFix (n-nargs+lv.(i)+1,(cst,nbfix,li,n))
  else 
    raise Elimconst

(* [compute_consteval_direct] expand all constant in a whole, but
   [compute_consteval] only one by one, until finding the one which is
   reversible (in case of a unary Fix) or the last one before the Fix
   if the latter is mutually defined *)

let compute_consteval_direct cst c =
  let rec srec n labs c =
    let c',l = whd_betadeltaeta_stack (Global.env()) Evd.empty c in
    match kind_of_term c' with
      | IsLambda (_,t,g) when l=[] -> srec (n+1) (t::labs) g
      | IsFix fix -> check_fix_reversibility cst labs l fix
      | IsMutCase (_,_,d,_) when isRel d -> EliminationCases n
      | _ -> NotAnElimination
  in srec 0 [] c

let rec compute_consteval cst c = 
  let rec srec n labs c =
    let c',l = whd_betaetalet_stack c in
    let nargs = List.length l in
    match kind_of_term c' with
      | IsConst cst2 ->
	  (match descend_consteval cst2 with
	     | NotAnElimination -> NotAnElimination
	     | EliminationFix (minarg,(_,nbfix,_,_ as info)) ->
		 (* We know that the underlying Fix must be fold by oldcst *)
		 (* We now try to fold it as cst only if nbfix=1 and n=0 *)
		 let new_minarg = max (minarg+n-nargs) minarg in
		 if nbfix=1 then
		   try
		     (* We try to name the Fix by cst *)
		     (* Complexité en n^2, bof, peut mieux faire *)
		     compute_consteval_direct cst c
		   with
		       Elimconst -> EliminationFix (new_minarg,info)
		 else
		   EliminationFix (new_minarg,info)
	     | EliminationCases minarg ->
		 let new_minarg = max (minarg+n-nargs) minarg in
		 EliminationCases new_minarg)
      | IsLambda (_,t,g) when l=[] -> srec (n+1) (t::labs) g
      | IsFix fix -> check_fix_reversibility cst labs l fix
      | IsMutCase (_,_,d,_) when isRel d -> EliminationCases n
      | _ -> raise Elimconst
  in
  try srec 0 [] c
  with Elimconst -> NotAnElimination

and descend_consteval cst =
  match constant_opt_value (Global.env ()) cst with
    | None -> NotAnElimination
    | Some c -> compute_consteval cst c

let constant_eval (sp,_ as cst) =
  try
    Cstmap.find cst !eval_table
  with Not_found -> begin
    let v = descend_consteval cst in
    eval_table := Cstmap.add cst v !eval_table;
    v
  end


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

let make_elim_fun ((sp,args as cst),nbfix,lv,n) largs =
  let labs,_ = list_chop n (list_of_stack largs) in
  let p = List.length lv in
  let ylv = List.map fst lv in
  let la' = list_map_i 
	      (fun q aq ->
		 try (mkRel (p+1-(list_index (n-q) ylv))) 
		 with Not_found -> aq) 0
              (List.map (lift p) labs) 
  in 
  fun id -> 
    let fi = 
      if nbfix = 1 then
	mkConst cst
      else
	mkConst (make_path (dirpath sp) id (kind_of_path sp),args)
    in
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

let special_red_case env whfun (ci, p, c, lf)  =
  let rec redrec s = 
    let (constr, cargs) = whfun s in 
    match kind_of_term constr with 
      | IsConst (sp,args as cst) -> 
	  (match constant_opt_value env cst with
	     | Some gvalue ->
		 if reducible_mind_case gvalue then
		   let build_fix_name id =
		     mkConst (make_path (dirpath sp) id (kind_of_path sp),args)
		   in reduce_mind_case_use_function env build_fix_name
			{mP=p; mconstr=gvalue; mcargs=list_of_stack cargs;
			 mci=ci; mlf=lf}
		 else
		   redrec (gvalue, cargs)
             | None -> raise Redelimination)
      | _ ->
          if reducible_mind_case constr then
            reduce_mind_case
	      {mP=p; mconstr=constr; mcargs=list_of_stack cargs;
	       mci=ci; mlf=lf}
          else 
	    raise Redelimination
  in 
  redrec (c, empty_stack)

let rec red_elim_const env sigma cst largs =
  if not (evaluable_constant env cst) then raise Redelimination;
  match constant_eval cst with
    | EliminationCases n when stack_args_size largs >= n ->
	let c = constant_value env cst in
	let c', lrest = whd_betadeltaeta_state env sigma (c,largs) in
        (special_red_case env (construct_const env sigma) (destCase c'),
	 lrest)
    | EliminationFix (min,(cstgoal,_,_,_ as infos))
	when stack_args_size largs >=min ->
	let rec descend cst args =
	  let c = constant_value env cst in
	  if cst = cstgoal then
	    (c,args)
	  else
	    let c', lrest = whd_betaetalet_state (c,args) in
	    descend (destConst c') lrest in
	let (_, midargs as s) = descend cst largs in
	let d, lrest = whd_betadeltaeta_state env sigma s in
	let f = make_elim_fun infos midargs in
	let co = construct_const env sigma in
	(match reduce_fix_use_function f co (destFix d) lrest with
	   | NotReducible -> raise Redelimination
	   | Reduced (c,rest) -> (nf_beta env sigma c, rest))
    | _ -> raise Redelimination

and construct_const env sigma = 
  let rec hnfstack (x, stack as s) =
    match kind_of_term x with
      | IsConst cst  ->
          (try
	     hnfstack (red_elim_const env sigma cst stack)
           with Redelimination ->
	     (match constant_opt_value env cst with
		| Some cval ->
		    (match kind_of_term cval with
                       | IsCoFix _ -> s
                       | _ -> hnfstack (cval, stack))
		| None ->
		    raise Redelimination))
      | IsCast (c,_) -> hnfstack (c, stack)
      | IsApp (f,cl) -> hnfstack (f, append_stack cl stack)
      | IsLambda (_,_,c) ->
          (match decomp_stack stack with 
             | None -> assert false
             | Some (c',rest) -> stacklam hnfstack [c'] c rest)
      | IsMutCase (ci,p,c,lf) ->
          hnfstack 
	    (special_red_case env (construct_const env sigma) (ci,p,c,lf), stack)
      | IsMutConstruct _ -> s
      | IsCoFix _ -> s
      | IsFix fix -> 
	  (match reduce_fix hnfstack fix stack with
             | Reduced s' -> hnfstack s'
	     | NotReducible -> raise Redelimination)
      | _ -> raise Redelimination
  in 
  hnfstack

(***********************************************************************)
(*            Special Purpose Reduction Strategies                     *)

(* Red reduction tactic: reduction to a product *)

let internal_red_product env sigma c = 
  let rec redrec x =
    match kind_of_term x with
      | IsApp (f,l) -> appvect (redrec f, l)
      | IsConst cst -> constant_value env cst
      | IsEvar ev -> existential_value sigma ev
      | IsCast (c,_) -> redrec c
      | IsProd (x,a,b) -> mkProd (x, a, redrec b)
      | _ -> raise Redelimination
  in
  let c' =
    try redrec c with NotEvaluableConst _ | NotInstantiatedEvar ->
					      raise Redelimination
  in nf_betaiota env sigma (redrec c)

let red_product env sigma c = 
  try internal_red_product env sigma c
  with Redelimination -> error "Not reducible"

(* Hnf reduction tactic: *)

let hnf_constr env sigma c = 
  let rec redrec (x, largs as s) =
    match kind_of_term x with
      | IsLambda (n,t,c) ->
          (match decomp_stack largs with
             | None      -> app_stack s
             | Some (a,rest) -> stacklam redrec [a] c rest)
      | IsLetIn (n,b,_,c) -> stacklam redrec [b] c largs
      | IsApp (f,cl)   -> redrec (f, append_stack cl largs)
      | IsConst cst ->
          (try
             let (c',lrest) = red_elim_const env sigma cst largs in 
	     redrec (c', lrest)
           with Redelimination ->
             match constant_opt_value env cst with
	       | Some c ->
		   (match kind_of_term c with 
                      | IsCoFix _ -> app_stack (x,largs)
		      | _ ->  redrec (c, largs))
	       | None -> app_stack s)
      | IsCast (c,_) -> redrec (c, largs)
      | IsMutCase (ci,p,c,lf) ->
          (try
             redrec 
	       (special_red_case env (whd_betadeltaiota_state env sigma) 
		  (ci, p, c, lf), largs)
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
      | IsLetIn (n,b,_,c) -> stacklam nf_app [b] c stack
      | IsApp (f,cl) -> nf_app (f, append_stack cl stack)
      | IsCast (c,_) -> nf_app (c, stack)
      | IsConst cst ->
          (try
	     nf_app (red_elim_const env sigma cst stack)
           with Redelimination -> 
	     s)
      | IsMutCase (ci,p,d,lf) ->
          (try
             nf_app (special_red_case env nf_app (ci,p,d,lf), stack)
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


(* linear substitution (following pretty-printer) of the value of name in c.
 * n is the number of the next occurence of name.
 * ol is the occurence list to find. *)
let rec substlin env name n ol c =
  match kind_of_term c with
    | IsConst (sp,_ as const) when sp = name ->
        if List.hd ol = n then
          try 
	    (n+1, List.tl ol, constant_value env const)
          with
	      NotEvaluableConst _ ->
		errorlabstrm "substlin"
		  [< pr_sp sp; 'sTR " is not a defined constant" >]
        else 
	  ((n+1),ol,c)

    (* INEFFICIENT: OPTIMIZE *)
    | IsApp (c1,cl) ->
        Array.fold_left 
	  (fun (n1,ol1,c1') c2 ->
	     (match ol1 with 
                | [] -> (n1,[],applist(c1',[c2]))
                | _  ->
                    let (n2,ol2,c2') = substlin env name n1 ol1 c2 in
                    (n2,ol2,applist(c1',[c2']))))
          (substlin env name n ol c1) cl

    | IsLambda (na,c1,c2) ->
        let (n1,ol1,c1') = substlin env name n ol c1 in
        (match ol1 with 
           | [] -> (n1,[],mkLambda (na,c1',c2))
           | _  ->
               let (n2,ol2,c2') = substlin env name n1 ol1 c2 in
               (n2,ol2,mkLambda (na,c1',c2')))

    | IsLetIn (na,c1,t,c2) ->
        let (n1,ol1,c1') = substlin env name n ol c1 in
        (match ol1 with 
           | [] -> (n1,[],mkLambda (na,c1',c2))
           | _  ->
               let (n2,ol2,c2') = substlin env name n1 ol1 c2 in
               (n2,ol2,mkLambda (na,c1',c2')))

    | IsProd (na,c1,c2) ->
        let (n1,ol1,c1') = substlin env name n ol c1 in
        (match ol1 with 
           | [] -> (n1,[],mkProd (na,c1',c2))
           | _  ->
               let (n2,ol2,c2') = substlin env name n1 ol1 c2 in
               (n2,ol2,mkProd (na,c1',c2')))
	
    | IsMutCase (ci,p,d,llf) -> 
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
           | [] -> (n1,[],mkMutCase (ci, p', d, llf))
           | _  ->
               let (n2,ol2,d') = substlin env name n1 ol1 d in
               (match ol2 with
		  | [] -> (n2,[],mkMutCase (ci, p', d', llf))
		  | _  -> 
	              let (n3,ol3,lf') = substlist n2 ol2 (Array.to_list llf)
                      in (n3,ol3,mkMutCaseL (ci, p', d', lf'))))
        
    | IsCast (c1,c2)   ->
        let (n1,ol1,c1') = substlin env name n ol c1 in
        (match ol1 with 
           | [] -> (n1,[],mkCast (c1',c2))
           | _  ->
               let (n2,ol2,c2') = substlin env name n1 ol1 c2 in
               (n2,ol2,mkCast (c1',c2')))

    | IsFix _ -> 
        (warning "do not consider occurrences inside fixpoints"; (n,ol,c))
	
    | IsCoFix _ -> 
        (warning "do not consider occurrences inside cofixpoints"; (n,ol,c))

    | (IsRel _|IsMeta _|IsVar _|IsXtra _|IsSort _
      |IsEvar _|IsConst _|IsMutInd _|IsMutConstruct _) -> (n,ol,c)
	
open Closure
	  
let unfold env sigma name =
  clos_norm_flags (unfold_flags name) env sigma


(* unfoldoccs : (readable_constraints -> (int list * section_path) -> constr -> constr)
 * Unfolds the constant name in a term c following a list of occurrences occl.
 * at the occurrences of occ_list. If occ_list is empty, unfold all occurences.
 * Performs a betaiota reduction after unfolding. *)
let unfoldoccs env sigma (occl,name) c =
  match occl with
    | []  -> unfold env sigma name c
    | l -> 
        match substlin env name 1 (Sort.list (<) l) c with
          | (_,[],uc) -> nf_betaiota env sigma uc
          | (1,_,_) -> error ((string_of_path name)^" does not occur")
          | _ -> error ("bad occurrence numbers of "^(string_of_path name))

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
  cbv_norm (create_cbv_infos flags env sigma) t

let cbv_beta env = cbv_norm_flags beta env
let cbv_betaiota env = cbv_norm_flags betaiota env
let cbv_betadeltaiota env =  cbv_norm_flags betadeltaiota env

let compute = cbv_betadeltaiota

(* Pattern *)

(* gives [na:ta]c' such that c converts to ([na:ta]c' a), abstracting only
 * the specified occurrences. *)

let abstract_scheme env (locc,a,ta) t =
  let na = named_hd env ta Anonymous in
  if occur_meta ta then error "cannot find a type for the generalisation";
  if occur_meta a then 
    mkLambda (na,ta,t)
  else 
    mkLambda (na, ta,subst_term_occ locc a t)


let pattern_occs loccs_trm_typ env sigma c =
  let abstr_trm = List.fold_right (abstract_scheme env) loccs_trm_typ c in
  applist(abstr_trm, List.map (fun (_,t,_) -> t) loccs_trm_typ)

(* Generic reduction: reduction functions used in reduction tactics *)

type red_expr =
  | Red of bool
  | Hnf
  | Simpl
  | Cbv of Closure.flags
  | Lazy of Closure.flags
  | Unfold of (int list * section_path) list
  | Fold of constr list
  | Pattern of (int list * constr * constr) list

let reduction_of_redexp = function
  | Red internal -> if internal then internal_red_product else red_product
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
      | IsApp (f,cl) -> redrec (f, append_stack cl largs)
      | IsConst cst ->
          (try
             red_elim_const env sigma cst largs
           with Redelimination ->
	     try
               constant_value env cst, largs
             with NotEvaluableConst _ -> error "Not reductible 1")

      | IsMutCase (ci,p,c,lf) ->
          (try
	     (special_red_case env (whd_betadeltaiota_state env sigma)
	       (ci,p,c,lf), largs)
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
    let c, _ = whd_stack t in
    match kind_of_term c with
      | IsMutInd (mind,args) -> ((mind,args),t,it_mkProd_or_LetIn t l)
      | IsConst _ | IsMutCase _ ->
          (try 
	     let t' = nf_betaiota env sigma (one_step_reduce env sigma t) in 
	     elimrec t' l
           with UserError _ -> errorlabstrm "tactics__reduce_to_mind"
               [< 'sTR"Not an inductive product." >])
      | IsProd (n,ty,t') -> elimrec t' ((n,None,ty)::l)
      | IsLetIn (n,b,ty,t') -> elimrec t' ((n,Some b,ty)::l)
      | _ -> error "Not an inductive product"
 in
 elimrec t []

let reduce_to_ind env sigma t =
  let ((ind_sp,_),redt,c) = reduce_to_mind env sigma t in 
  (Declare.path_of_inductive_path ind_sp, redt, c)
