
(* $Id$ *)

open Pp
open Util
open Names
(*i open Generic i*)
open Term
open Univ
open Evd
open Declarations
open Environ
open Instantiate
open Closure

exception Redelimination
exception Elimconst

type 'a contextual_reduction_function = env -> 'a evar_map -> constr -> constr
type 'a reduction_function = 'a contextual_reduction_function
type local_reduction_function = constr -> constr

type 'a contextual_stack_reduction_function = 
    env -> 'a evar_map -> constr -> constr list -> constr * constr list
type 'a stack_reduction_function = 'a contextual_stack_reduction_function
type local_stack_reduction_function = 
    constr -> constr list -> constr * constr list
(*
type stack =
  | EmptyStack
  | ConsStack of constr array * int * stack

let decomp_stack = function
  | EmptyStack -> None
  | ConsStack (v, n, s) ->
      Some (v.(n), (if n+1 = Array.length v then s else ConsStack (v, n+1, s)))

let append_stack v s = if Array.length v = 0 then s else ConsStack (v,0,s)
*)

type stack = constr list

let decomp_stack = function
  | [] -> None
  | v :: s -> Some (v,s)

let append_stack v s = v@s

(*************************************)
(*** Reduction Functions Operators ***)
(*************************************)

let rec under_casts f env sigma = function
  | DOP2(Cast,c,t) -> DOP2(Cast,under_casts f env sigma c, t)
  | c              -> f env sigma c

let rec local_under_casts f = function
  | DOP2(Cast,c,t) -> DOP2(Cast,local_under_casts f c, t)
  | c              -> f c

let rec whd_stack x stack =
  match x with
    | DOPN(AppL,cl)  -> whd_stack cl.(0) (array_app_tl cl stack)
    | DOP2(Cast,c,_) -> whd_stack c stack
    | _              -> (x,stack)
	  
let stack_reduction_of_reduction red_fun env sigma x stack =
  let t = red_fun env sigma (applistc x stack) in
  whd_stack t []

let strong whdfun env sigma = 
  let rec strongrec env t = match whdfun env sigma t with
    | DOP0 _ as t -> t
    | DOP1(oper,c) -> DOP1(oper,strongrec env c)
    | DOP2(oper,c1,c2) -> DOP2(oper,strongrec env c1,strongrec env c2)
    (* Cas ad hoc *)
    | DOPN(Fix _ as oper,cl) ->
	let cl' = Array.copy cl in
	let l = Array.length cl -1 in
	for i=0 to l-1 do cl'.(i) <- strongrec env cl.(i) done;
	cl'.(l) <- strongrec_lam env cl.(l);
	DOPN(oper, cl')	
    | DOPN(oper,cl) -> DOPN(oper,Array.map (strongrec env) cl)
    | CLam (n,t,c)   ->
	CLam (n, typed_app (strongrec env) t, strongrec (push_rel_decl (n,t) env) c)  
    | CPrd (n,t,c)   ->
	CPrd (n, typed_app (strongrec env) t, strongrec (push_rel_decl (n,t) env) c)
    | CLet (n,b,t,c) ->
	CLet (n, strongrec env b, typed_app (strongrec env) t,
	      strongrec (push_rel_def (n,b,t) env) c)
    | VAR _ as t -> t
    | Rel _ as t -> t
    | DLAM _ | DLAMV _ -> assert false
  and strongrec_lam env = function (* Gestion incorrecte de l'env des Fix *)
    | DLAM(na,c) -> DLAM(na,strongrec_lam env c)
    | DLAMV(na,c) -> DLAMV(na,Array.map (strongrec env) c)
    | _ -> assert false
  in
  strongrec env

let local_strong whdfun = 
  let rec strongrec t = match whdfun t with
    | DOP0 _ as t -> t
    | DOP1(oper,c) -> DOP1(oper,strongrec c)
    | DOP2(oper,c1,c2) -> DOP2(oper,strongrec c1,strongrec c2)
    (* Cas ad hoc *)
    | DOPN(Fix _ as oper,cl) ->
	let cl' = Array.copy cl in
	let l = Array.length cl -1 in
	for i=0 to l-1 do cl'.(i) <- strongrec cl.(i) done;
	cl'.(l) <- strongrec_lam cl.(l);
	DOPN(oper, cl')	
    | DOPN(oper,cl) -> DOPN(oper,Array.map strongrec cl)
    | CLam(n,t,c)   -> CLam (n, typed_app strongrec t, strongrec c)  
    | CPrd(n,t,c)   -> CPrd (n, typed_app strongrec t, strongrec c)
    | CLet(n,b,t,c) -> CLet (n, strongrec b,typed_app strongrec t, strongrec c)
    | VAR _ as t -> t
    | Rel _ as t -> t
    | DLAM _ | DLAMV _ -> assert false
  and strongrec_lam = function
    | DLAM(na,c) -> DLAM(na,strongrec_lam c)
    | DLAMV(na,c) -> DLAMV(na,Array.map strongrec c)
    | _ -> assert false
  in
  strongrec

let rec strong_prodspine redfun c = 
  let x = redfun c in
  match kind_of_term x with
    | IsProd (na,a,b) -> mkProd (na,a,strong_prodspine redfun b)
    | _ -> x

(****************************************************************************)
(*                   Reduction Functions                                    *)
(****************************************************************************)


(* call by value reduction functions *)
let cbv_norm_flags flags env sigma t =
  cbv_norm (create_cbv_infos flags env sigma) t

let cbv_beta env = cbv_norm_flags beta env
let cbv_betaiota env = cbv_norm_flags betaiota env
let cbv_betadeltaiota env =  cbv_norm_flags betadeltaiota env

let compute = cbv_betadeltaiota


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


(* Red reduction tactic: reduction to a product *)
let red_product env sigma c = 
  let rec redrec x =
    match kind_of_term x with
      | IsAppL (f,l) -> applist (redrec f, l)
      | IsConst (_,_) when evaluable_constant env x -> constant_value env x
      | IsEvar (ev,args) when Evd.is_defined sigma ev -> 
	  existential_value sigma (ev,args)
      | IsCast (c,_) -> redrec c
      | IsProd (x,a,b) -> mkProd (x, a, redrec b)
      | _ -> error "Term not reducible"
  in 
  nf_betaiota env sigma (redrec c)

(* linear substitution (following pretty-printer) of the value of name in c.
 * n is the number of the next occurence of name.
 * ol is the occurence list to find. *)
let rec substlin env name n ol c =
  match kind_of_term c with
    | IsConst (sp,_) when sp = name ->
        if List.hd ol = n then
          if evaluable_constant env c then 
	    (n+1, List.tl ol, constant_value env c)
          else
            errorlabstrm "substlin"
              [< print_sp sp; 'sTR " is not a defined constant" >]
        else 
	  ((n+1),ol,c)

    (* INEFFICIENT: OPTIMIZE *)
    | IsAppL (c1,cl) ->
        List.fold_left 
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
	
	  
let unfold env sigma name =
  let flag = 
    (UNIFORM,{ r_beta = true;
               r_delta = (fun op -> op=(Const name));
               r_iota = true })
  in 
  clos_norm_flags flag env sigma


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
  let rcom = red_product env sigma com in
  subst1 com (subst_term rcom c)

let fold_commands cl env sigma c =
  List.fold_right (fun com -> fold_one_com com env sigma) (List.rev cl) c


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


(*************************************)
(*** Reduction using substitutions ***)
(*************************************)

(* 1. Beta Reduction *)

let rec stacklam recfun env t stack =
  match (stack,t) with
    | h::stacktl, CLam (_,_,c) -> stacklam recfun (h::env) c stacktl
    | _ -> recfun (substl env t, stack)


let beta_applist (c,l) = stacklam applist [] c l


let whd_beta_stack x stack = 
  let rec whrec (x, stack as s) = match x with
    | CLam (name,c1,c2) ->
	(match decomp_stack stack with
           | None -> (x,[])
	   | Some (a1,rest) -> stacklam whrec [a1] c2 rest)
	
    | DOPN(AppL,cl) -> whrec (array_hd cl, array_app_tl cl stack)
    | DOP2(Cast,c,_) -> whrec (c, stack)
    | x -> s
  in 
  whrec (x, stack)

let whd_beta x = applist (whd_beta_stack x [])

(* 2. Delta Reduction *)
		   
let whd_const_stack namelist env sigma = 
  let rec whrec x l =
    match x with
      | DOPN(Const sp,_) as c ->
	  if List.mem sp namelist then
            if evaluable_constant env c then
              whrec (constant_value env c) l
            else 
	      error "whd_const_stack"
	  else 
	    x,l

      | DOP2(Cast,c,_) -> whrec c l
      | DOPN(AppL,cl) -> whrec (array_hd cl) (array_app_tl cl l)
      | x -> x,l
  in 
  whrec

let whd_const namelist env sigma c = 
  applist(whd_const_stack namelist env sigma c [])

let whd_delta_stack env sigma = 
  let rec whrec x l =
    match x with
      | DOPN(Const _,_) as c ->
	  if evaluable_constant env c then
            whrec (constant_value env c) l
	  else 
	    x,l
      | DOPN(Evar ev,args) ->
	  if Evd.is_defined sigma ev then
            whrec (existential_value sigma (ev,args)) l
	  else 
	    x,l
      | DOP2(Cast,c,_) -> whrec c l
      | DOPN(AppL,cl) -> whrec (array_hd cl) (array_app_tl cl l)
      | x -> x,l
  in 
  whrec

let whd_delta env sigma c = applist(whd_delta_stack env sigma c [])


let whd_betadelta_stack env sigma x l = 
  let rec whrec (x, l as s) =
    match kind_of_term x with
      | IsConst _ ->
          if evaluable_constant env x then 
	    whrec (constant_value env x, l)
          else 
	    s
      | IsEvar (ev,args) ->
          if Evd.is_defined sigma ev then 
	    whrec (existential_value sigma (ev,args), l)
          else 
	    s
      | IsCast (c,_) -> whrec (c, l)
      | IsAppL (f,cl)  -> whrec (f, append_stack cl l)
      | IsLambda (_,_,c) ->
          (match decomp_stack l with
             | None -> s
             | Some (a,m) -> stacklam whrec [a] c m)
      | x -> s
  in 
  whrec (x, l)

let whd_betadelta env sigma c = applist(whd_betadelta_stack env sigma c [])


let whd_betaevar_stack env sigma x l = 
  let rec whrec (x, l as s) =
    match kind_of_term x with
      | IsEvar (ev,args) ->
          if Evd.is_defined sigma ev then 
	    whrec (existential_value sigma (ev,args), l)
          else 
	    s
      | IsCast (c,_) -> whrec (c, l)
      | IsAppL (f,cl)  -> whrec (f, append_stack cl l)
      | IsLambda (_,_,c) ->
          (match decomp_stack l with
             | None -> s
             | Some (a,m) -> stacklam whrec [a] c m)
      | x -> s
  in 
  whrec (x, l)
       
let whd_betaevar env sigma c = applist(whd_betaevar_stack env sigma c [])

let whd_betadeltaeta_stack env sigma x l = 
  let rec whrec (x, l as s) =
    match kind_of_term x with
      | IsConst _ ->
          if evaluable_constant env x then 
	    whrec (constant_value env x, l)
          else 
	    s
      | IsEvar (ev,args) ->
          if Evd.is_defined sigma ev then 
	    whrec (existential_value sigma (ev,args), l)
          else 
	    s
      | IsCast (c,_) -> whrec (c, l)
      | IsAppL (f,cl)  -> whrec (f, append_stack cl l)
      | IsLambda (_,_,c) ->
          (match decomp_stack l with
             | None ->
                 (match applist (whrec (c, [])) with 
                    | DOPN(AppL,cl) ->
			let napp = (Array.length cl) -1 in
                        (match whrec (array_last cl, []) with 
                           | (Rel 1,[]) when napp > 0 ->
                               let lc = Array.sub cl 0 napp in
                               let u = if napp=1 then lc.(0) else DOPN(AppL,lc)
                               in if noccurn 1 u then (pop u,[]) else s
                           | _ -> s)
                    | _ -> s)
             | Some (a,m) -> stacklam whrec [a] c m)
      | x -> s
  in 
  whrec (x, l)

let whd_betadeltaeta env sigma x = 
  applist(whd_betadeltaeta_stack env sigma x [])

(* 3. Iota reduction *)

type 'a miota_args = {
  mP      : constr;     (* the result type *)
  mconstr : constr;     (* the constructor *)
  mci     : case_info;  (* special info to re-build pattern *)
  mcargs  : 'a list;    (* the constructor's arguments *)
  mlf     : 'a array }  (* the branch code vector *)
		       
let reducible_mind_case = function
  | DOPN(MutConstruct _,_) | DOPN(CoFix _,_) -> true
  | _  -> false

(*
let contract_cofix = function
  | DOPN(CoFix(bodynum),bodyvect) ->
      let nbodies = (Array.length bodyvect) -1 in
      let make_Fi j = DOPN(CoFix(j),bodyvect) in
      sAPPViList bodynum (array_last bodyvect) (list_tabulate make_Fi nbodies)
  | _ -> assert false
*)

let contract_cofix (bodynum,(types,names,bodies as typedbodies)) =
  let nbodies = Array.length bodies in
  let make_Fi j = mkCoFix (nbodies-j-1,typedbodies) in
  substl (list_tabulate make_Fi nbodies) bodies.(bodynum)

let reduce_mind_case mia =
  match mia.mconstr with
    | DOPN(MutConstruct (ind_sp,i as cstr_sp),args) ->
	let ncargs = (fst mia.mci).(i-1) in
	let real_cargs = list_lastn ncargs mia.mcargs in
        applist (mia.mlf.(i-1),real_cargs)
    | DOPN(CoFix _,_) as cofix ->
	let cofix_def = contract_cofix (destCoFix cofix) in
	mkMutCase (mia.mci, mia.mP, applist(cofix_def,mia.mcargs), mia.mlf)
    | _ -> assert false

(* contracts fix==FIX[nl;i](A1...Ak;[F1...Fk]{B1....Bk}) to produce
   Bi[Fj --> FIX[nl;j](A1...Ak;[F1...Fk]{B1...Bk})] *)

(*
let contract_fix = function 
  | DOPN(Fix(recindices,bodynum),bodyvect) -> 
      let nbodies = Array.length recindices in
      let make_Fi j = DOPN(Fix(recindices,j),bodyvect) in
      sAPPViList bodynum (array_last bodyvect) (list_tabulate make_Fi nbodies)
  | _ -> assert false
*)
let contract_fix ((recindices,bodynum),(types,names,bodies as typedbodies)) =
  let nbodies = Array.length recindices in
  let make_Fi j = mkFix ((recindices,nbodies-j-1),typedbodies) in
  substl (list_tabulate make_Fi nbodies) bodies.(bodynum)

let fix_recarg ((recindices,bodynum),_) stack =
  if 0 <= bodynum & bodynum < Array.length recindices then
    let recargnum = Array.get recindices bodynum in
    (try 
       Some (recargnum, List.nth stack recargnum)
     with Failure "nth" | Invalid_argument "List.nth" -> 
       None)
  else 
    None

type fix_reduction_result = NotReducible | Reduced of (constr * constr list)

let reduce_fix whfun fix stack =
  match fix_recarg fix stack with
    | None -> NotReducible
    | Some (recargnum,recarg) ->
        let (recarg'hd,_ as recarg') = whfun (recarg, []) in
        let stack' = list_assign stack recargnum (applist recarg') in
	(match recarg'hd with
           | DOPN(MutConstruct _,_) -> Reduced (contract_fix fix, stack')
	   | _ -> NotReducible)

(* NB : Cette fonction alloue peu c'est l'appel 
     ``let (recarg'hd,_ as recarg') = whfun recarg [] in''
                                     --------------------
qui coute cher dans whd_betadeltaiota *)

let whd_betaiota_stack x l = 
  let rec whrec (x,stack as s) =
    match kind_of_term x with
      | IsCast (c,_)     -> whrec (c, stack)
      | IsAppL (f,cl)    -> whrec (f, append_stack cl stack)
      | IsLambda (_,_,c) ->
          (match decomp_stack stack with
             | None -> s
             | Some (a,m) -> stacklam whrec [a] c m)
      | IsMutCase (ci,p,d,lf) ->
          let (c,cargs) = whrec (d, []) in
          if reducible_mind_case c then
            whrec (reduce_mind_case
                     {mP=p; mconstr=c; mcargs=cargs; mci=ci; mlf=lf}, stack)
          else 
	    (mkMutCase (ci, p, applist(c,cargs), lf), stack)
            
      | IsFix fix ->
	  (match reduce_fix whrec fix stack with
             | Reduced s' -> whrec s'
	     | NotReducible -> s)
      | _ -> s
  in 
  whrec (x, l)

let whd_betaiota x = applist (whd_betaiota_stack x [])

let whd_betaiotaevar_stack env sigma x l = 
  let rec whrec (x, stack as s) =
    match kind_of_term x with
      | IsEvar (ev,args) ->
          if Evd.is_defined sigma ev then 
	    whrec (existential_value sigma (ev,args), stack)
          else 
	    s
      | IsCast (c,_) -> whrec (c, stack)
      | IsAppL (f,cl)    -> whrec (f, append_stack cl stack)
      | IsLambda (_,_,c) ->
          (match decomp_stack stack with
             | None -> s
             | Some (a,m) -> stacklam whrec [a] c m)
      | IsMutCase (ci,p,d,lf) ->
          let (c,cargs) = whrec (d, []) in
          if reducible_mind_case c then
	    whrec (reduce_mind_case
                     {mP=p; mconstr=c; mcargs=cargs; mci=ci; mlf=lf}, stack)
          else 
	    (mkMutCase (ci, p, applist(c,cargs), lf), stack)
      | IsFix fix ->
	  (match reduce_fix whrec fix stack with
             | Reduced s' -> whrec s'
	     | NotReducible -> s)
      | _ -> s
 in 
  whrec (x, l) 

let whd_betaiotaevar env sigma x = 
  applist(whd_betaiotaevar_stack env sigma x [])

let whd_betadeltaiota_stack env sigma x l =
  let rec whrec (x, stack as s) =
    match kind_of_term x with
      | IsConst _ ->
          if evaluable_constant env x then
	    whrec (constant_value env x, stack)
          else 
	    s
      | IsEvar (ev,args) ->
          if Evd.is_defined sigma ev then 
	    whrec (existential_value sigma (ev,args), stack)
          else 
	    s
      | IsCast (c,_) -> whrec (c, stack)
      | IsAppL (f,cl)    -> whrec (f, append_stack cl stack)
      | IsLambda (_,_,c) ->
          (match decomp_stack stack with
             | None -> s
             | Some (a,m) -> stacklam whrec [a] c m)
      | IsMutCase (ci,p,d,lf) ->
          let (c,cargs) = whrec (d, []) in
          if reducible_mind_case c then
	    whrec (reduce_mind_case
                     {mP=p; mconstr=c; mcargs=cargs; mci=ci; mlf=lf}, stack)
          else 
	    (mkMutCase (ci, p, applist(c,cargs), lf), stack)
      | IsFix fix ->
	  (match reduce_fix whrec fix stack with
             | Reduced s' -> whrec s'
	     | NotReducible -> s)
      | _ -> s
  in
  whrec (x, l)

let whd_betadeltaiota env sigma x = 
  applist(whd_betadeltaiota_stack env sigma x [])
				
				
let whd_betadeltaiotaeta_stack env sigma x l = 
  let rec whrec (x, stack as s) =
    match kind_of_term x with
      | IsConst _ ->
          if evaluable_constant env x then
	    whrec (constant_value env x, stack)
          else 
	    s
      | IsEvar (ev,args) ->
          if Evd.is_defined sigma ev then 
	    whrec (existential_value sigma (ev,args), stack)
          else 
	    s
      | IsCast (c,_) -> whrec (c, stack)
      | IsAppL (f,cl)    -> whrec (f, append_stack cl stack)
      | IsLambda (_,_,c) ->
          (match decomp_stack stack with
             | None ->
                 (match applist (whrec (c, [])) with 
                    | DOPN(AppL,cl) ->
			let napp = (Array.length cl) -1 in
                        (match whrec (array_last cl, []) with 
                           | (Rel 1,[]) when napp > 0 ->
                               let lc = Array.sub cl 0 napp in
                               let u = if napp=1 then lc.(0) else DOPN(AppL,lc)
                               in if noccurn 1 u then (pop u,[]) else s
                           | _ -> s)
                    | _ -> s)
             | Some (a,m) -> stacklam whrec [a] c m)

      | IsMutCase (ci,p,d,lf) ->
          let (c,cargs) = whrec (d, []) in
          if reducible_mind_case c then
	    whrec (reduce_mind_case
                     {mP=p; mconstr=c; mcargs=cargs; mci=ci; mlf=lf}, stack)
          else 
	    (mkMutCase (ci, p, applist(c,cargs), lf), stack)
      | IsFix fix ->
	  (match reduce_fix whrec fix stack with
             | Reduced s' -> whrec s'
	     | NotReducible -> s)
      | _ -> s
  in 
  whrec (x, l)

let whd_betadeltaiotaeta env sigma x = 
  applist(whd_betadeltaiotaeta_stack env sigma x [])

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

let bool_and_convert b f = 
  if b then f else fun _ -> raise NotConvertible

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
    | (FOP0(Sort s1), FOP0(Sort s2)) -> 
	bool_and_convert
	  (Array.length v1 = 0 && Array.length v2 = 0)
	  (sort_cmp cv_pb s1 s2)
	  
    | (FVAR x1, FVAR x2) ->
	bool_and_convert (x1=x2)
	  (convert_forall2 (ccnv (pb_equal cv_pb) infos lft1 lft2) v1 v2)

    | (FRel n, FRel m) ->
        bool_and_convert 
	  (reloc_rel n el1 = reloc_rel m el2)
          (convert_forall2 (ccnv (pb_equal cv_pb) infos lft1 lft2) v1 v2)

    | (FOP0(Meta n), FOP0(Meta m)) ->
        bool_and_convert (n=m) 
	  (convert_forall2 (ccnv (pb_equal cv_pb) infos lft1 lft2) v1 v2)

    (* 2 constants, 2 existentials or 2 abstractions *)
    | (FOPN(Const sp1,al1), FOPN(Const sp2,al2)) ->
	convert_or
	  (* try first intensional equality *)
	  (bool_and_convert (sp1 == sp2 or sp1 = sp2)
	     (convert_and
		(convert_forall2 (ccnv (pb_equal cv_pb) infos el1 el2) al1 al2)
		(convert_forall2 (ccnv (pb_equal cv_pb) infos lft1 lft2)
		   v1 v2)))
          (* else expand the second occurrence (arbitrary heuristic) *)
          (match search_frozen_cst infos (Const sp2) al2 with
             | Some def2 -> 
		 eqappr cv_pb infos appr1 (lft2, fhnf_apply infos n2 def2 v2)
             | None -> (match search_frozen_cst infos (Const sp1) al1 with
                          | Some def1 -> eqappr cv_pb infos
				(lft1, fhnf_apply infos n1 def1 v1) appr2
			  | None -> fun _ -> raise NotConvertible))

    | (FOPN(Evar ev1,al1), FOPN(Evar ev2,al2)) ->
	convert_or
	  (* try first intensional equality *)
	  (bool_and_convert (ev1 == ev2)
	     (convert_and
		(convert_forall2 (ccnv (pb_equal cv_pb) infos el1 el2) al1 al2)
		(convert_forall2 (ccnv (pb_equal cv_pb) infos lft1 lft2)
		   v1 v2)))
          (* else expand the second occurrence (arbitrary heuristic) *)
          (match search_frozen_cst infos (Evar ev2) al2 with
             | Some def2 -> 
		 eqappr cv_pb infos appr1 (lft2, fhnf_apply infos n2 def2 v2)
             | None -> (match search_frozen_cst infos (Evar ev1) al1 with
                          | Some def1 -> eqappr cv_pb infos
				(lft1, fhnf_apply infos n1 def1 v1) appr2
			  | None -> fun _ -> raise NotConvertible))

    (* only one constant, existential or abstraction *)
    | (FOPN((Const _ | Evar _) as op,al1), _)      ->
        (match search_frozen_cst infos op al1 with
           | Some def1 -> 
	       eqappr cv_pb infos (lft1, fhnf_apply infos n1 def1 v1) appr2
           | None -> fun _ -> raise NotConvertible)

    | (_, FOPN((Const _ | Evar _) as op,al2))      ->
        (match search_frozen_cst infos op al2 with
           | Some def2 -> 
	       eqappr cv_pb infos appr1 (lft2, fhnf_apply infos n2 def2 v2)
           | None -> fun _ -> raise NotConvertible)
	
    (* other constructors *)
    | (FLam (_,c1,c2,_,_), FLam (_,c'1,c'2,_,_)) ->
        bool_and_convert
	  (Array.length v1 = 0 && Array.length v2 = 0)
          (convert_and
	     (ccnv (pb_equal cv_pb) infos el1 el2 c1 c'1)
             (ccnv (pb_equal cv_pb) infos (el_lift el1) (el_lift el2) c2 c'2))

    | (FLet _, _) | (_, FLet _) -> anomaly "Normally removed by fhnf"

    | (FPrd (_,c1,c2,_,_), FPrd (_,c'1,c'2,_,_)) ->
	bool_and_convert
          (Array.length v1 = 0 && Array.length v2 = 0)
	  (convert_and
             (ccnv (pb_equal cv_pb) infos el1 el2 c1 c'1) (* Luo's system *)
             (ccnv cv_pb infos (el_lift el1) (el_lift el2) c2 c'2))

    (* Inductive types:  MutInd MutConstruct MutCase Fix Cofix *)

         (* Le cas MutCase doit venir avant le cas general DOPN car, a
            priori, 2 termes a base de MutCase peuvent etre convertibles
            sans que les annotations des MutCase le soient *)

    | (FOPN(MutCase _,cl1), FOPN(MutCase _,cl2)) ->
        convert_and
	  (convert_forall2 (ccnv (pb_equal cv_pb) infos el1 el2) cl1 cl2)
          (convert_forall2 (ccnv (pb_equal cv_pb) infos lft1 lft2) v1 v2)

     | (FOPN(op1,cl1), FOPN(op2,cl2)) ->
	 bool_and_convert (op1 = op2)
	   (convert_and
              (convert_forall2 (ccnv (pb_equal cv_pb) infos el1 el2) cl1 cl2)
              (convert_forall2 (ccnv (pb_equal cv_pb) infos lft1 lft2) v1 v2))

     (* binders *)
     | (FLAM(_,c1,_,_), FLAM(_,c2,_,_)) ->
	 bool_and_convert
           (Array.length v1 = 0 && Array.length v2 = 0)
           (ccnv cv_pb infos (el_lift el1) (el_lift el2) c1 c2)

     | (FLAMV(_,vc1,_,_), FLAMV(_,vc2,_,_)) ->
	 bool_and_convert
           (Array.length v1 = 0 & Array.length v2 = 0)
           (convert_forall2 
	      (ccnv cv_pb infos (el_lift el1) (el_lift el2)) vc1 vc2)

     | _ -> (fun _ -> raise NotConvertible)


let fconv cv_pb env sigma t1 t2 =
  let t1 = local_strong strip_outer_cast t1
  and t2 = local_strong strip_outer_cast t2 in
  if eq_constr t1 t2 then 
    Constraint.empty
  else
    let infos = create_clos_infos hnf_flags env sigma in
    ccnv cv_pb infos ELID ELID (inject t1) (inject t2) Constraint.empty

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

let whd_meta metamap = function
  | DOP0(Meta p) as u -> (try List.assoc p metamap with Not_found -> u)
  | x -> x
	
(* Try to replace all metas. Does not replace metas in the metas' values
 * Differs from (strong whd_meta). *)
let plain_instance s c = 
  let rec irec = function
    | DOP0(Meta p) as u -> (try List.assoc p s with Not_found -> u)
    | DOP1(oper,c)      -> DOP1(oper, irec c)
    | DOP2(oper,c1,c2)  -> DOP2(oper, irec c1, irec c2)
    | DOPN(oper,cl)     -> DOPN(oper, Array.map irec cl)
    | DLAM(x,c)         -> DLAM(x, irec c)
    | DLAMV(x,v)        -> DLAMV(x, Array.map irec v)
    | CLam (n,t,c)      -> CLam (n, typed_app irec t, irec c)  
    | CPrd (n,t,c)      -> CPrd (n, typed_app irec t, irec c)
    | CLet (n,b,t,c)    -> CLet (n, irec b, typed_app irec t, irec c)
    | u                 -> u
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
  match whd_betadeltaiota env sigma t with
    | CPrd (_,_,b) -> subst1 n b
    | _ -> anomaly "hnf_prod_app: Need a product"

let hnf_prod_appvect env sigma t nl = 
  Array.fold_left (hnf_prod_app env sigma) t nl

let hnf_prod_applist env sigma t nl = 
  List.fold_left (hnf_prod_app env sigma) t nl
				    
let hnf_lam_app env sigma t n =
  match whd_betadeltaiota env sigma t with
    | CLam (_,_,b) -> subst1 n b
    | _ -> anomaly "hnf_lam_app: Need an abstraction"

let hnf_lam_appvect env sigma t nl = 
  Array.fold_left (hnf_lam_app env sigma) t nl

let hnf_lam_applist env sigma t nl = 
  List.fold_left (hnf_lam_app env sigma) t nl

let splay_prod env sigma = 
  let rec decrec m c =
    match whd_betadeltaiota env sigma c with
      | CPrd (n,a,c0) -> decrec ((n,body_of_type a)::m) c0
      | t -> m,t
  in 
  decrec []

let splay_arity env sigma c =
  match splay_prod env sigma c with
   | l, DOP0 (Sort s) -> l,s
   | _, _ -> error "not an arity"

let sort_of_arity env c = snd (splay_arity env Evd.empty c)
  
let decomp_n_prod env sigma n = 
  let rec decrec m ln c = if m = 0 then (ln,c) else 
    match whd_betadeltaiota env sigma c with
      | CPrd (n,a,c0) ->
	  decrec (m-1) (Sign.add_rel_decl (n,a) ln) c0
      | _                      -> error "decomp_n_prod: Not enough products"
  in 
  decrec n Sign.empty_rel_context



(* Check that c is an "elimination constant"
    [xn:An]..[x1:A1](<P>MutCase (Rel i) of f1..fk end g1 ..gp)
or  [xn:An]..[x1:A1](Fix(f|t) (Rel i1) ..(Rel ip)) 
    with i1..ip distinct variables not occuring in t 
keep relevenant information ([i1,Ai1;..;ip,Aip],n,b)
with b = true in case of a fixpoint in order to compute 
an equivalent of Fix(f|t)[xi<-ai] as 
[yip:Bip]..[yi1:Bi1](F bn..b1) 
    == [yip:Bip]..[yi1:Bi1](Fix(f|t)[xi<-ai] (Rel 1)..(Rel p))
with bj=aj if j<>ik and bj=(Rel c) and Bic=Aic[xn..xic-1 <- an..aic-1]
   *)

let compute_consteval env sigma c = 
  let rec srec n labs c =
    match whd_betadeltaeta_stack env sigma c [] with 
      | CLam (_,t,g), []  -> srec (n+1) (t::labs) g
      | (DOPN(Fix((nv,i)),bodies),l)   -> 
          if List.length l > n then 
	    raise Elimconst 
          else
            let li = 
              List.map (function
                          | Rel k ->
                              if array_for_all (noccurn k) bodies then
				(k, List.nth labs (k-1)) 
			      else 
				raise Elimconst
                          | _ -> raise Elimconst) 
		l
            in 
	    if (list_distinct (List.map fst li)) then 
	      (li,n,true) 
            else 
	      raise Elimconst
      | (DOPN(MutCase _,_) as mc,lapp) -> 
          (match destCase mc with
             | (_,_,Rel _,_) -> ([],n,false)
             | _    -> raise Elimconst)
      | _ -> raise Elimconst
  in
  try Some (srec 0 [] c) with Elimconst -> None

(* One step of approximation *)

let rec apprec env sigma c stack =
  let (t, stack as s) = whd_betaiota_stack c stack in
  match kind_of_term t with
    | IsMutCase (ci,p,d,lf) ->
        let (cr,crargs) = whd_betadeltaiota_stack env sigma d [] in
        let rslt = mkMutCase (ci, p, applist(cr,crargs), lf) in
        if reducible_mind_case cr then 
	  apprec env sigma rslt stack
        else 
	  s
    | IsFix fix ->
	  (match reduce_fix 
	     (fun (c,l) -> whd_betadeltaiota_stack env sigma c l)
	     fix stack
	   with
             | Reduced (c,stack) -> apprec env sigma c stack
	     | NotReducible -> s)
    | _ -> s

let hnf env sigma c = apprec env sigma c []

(* A reduction function like whd_betaiota but which keeps casts
 * and does not reduce redexes containing meta-variables.
 * ASSUMES THAT APPLICATIONS ARE BINARY ONES.
 * Used in Programs.
 * Added by JCF, 29/1/98. *)

let whd_programs_stack env sigma x l = 
  let rec whrec (x, stack as s) =
    match kind_of_term x with
      | IsAppL (f,[c]) -> if occur_meta c then s else whrec (f, c::stack)
      | IsLambda (_,_,c) ->
          (match decomp_stack stack with
             | None -> s
             | Some (a,m) -> stacklam whrec [a] c m)
      | IsMutCase (ci,p,d,lf) ->
	  if occur_meta d then
	    s
	  else
            let (c,cargs) = whrec (d, []) in
            if reducible_mind_case c then
	      whrec (reduce_mind_case
		       {mP=p; mconstr=c; mcargs=cargs; mci=ci; mlf=lf}, stack)
	    else
	      (mkMutCase (ci, p, applist(c,cargs), lf), stack)
      | IsFix fix ->
	  (match reduce_fix whrec fix stack with
             | Reduced s' -> whrec s'
	     | NotReducible -> s)
      | _ -> s
  in 
  whrec (x, l)

let whd_programs env sigma x = applist (whd_programs_stack env sigma x [])

exception IsType

let is_arity env sigma = 
  let rec srec c = 
    match kind_of_term (whd_betadeltaiota env sigma c) with 
      | IsSort _ -> true
      | IsProd (_,_,c') -> srec c' 
      | IsLambda (_,_,c') -> srec c' 
      | _ -> false
  in 
  srec 
 
let info_arity env sigma = 
  let rec srec c = 
    match kind_of_term (whd_betadeltaiota env sigma c) with 
      | IsSort (Prop Null) -> false 
      | IsSort (Prop Pos) -> true 
      | IsProd (_,_,c') -> srec c' 
      | IsLambda (_,_,c') -> srec c' 
      | _ -> raise IsType
  in 
  srec 
    
let is_info_arity env sigma c =
  try (info_arity env sigma c) with IsType -> true
  
let is_type_arity env sigma = 
  let rec srec c = 
    match kind_of_term (whd_betadeltaiota env sigma c) with 
      | IsSort (Type _) -> true
      | IsProd (_,_,c') -> srec c' 
      | IsLambda (_,_,c') -> srec c' 
      | _ -> false
  in 
  srec 

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
  let rec frec depth acc = function
    | Rel n -> 
	if (n < bound+depth) & (n >= depth) then
	  Intset.add (bound+depth-n) acc
	else
	  acc
    | DOPN(_,cl)    -> Array.fold_left (frec depth) acc cl
    | DOP2(_,c1,c2) -> frec depth (frec depth acc c1) c2
    | DOP1(_,c)     -> frec depth acc c
    | DLAM(_,c)     -> frec (depth+1) acc c
    | DLAMV(_,cl)   -> Array.fold_left (frec (depth+1)) acc cl
    | CLam (_,t,c)   -> frec (depth+1) (frec depth acc (body_of_type t)) c
    | CPrd (_,t,c)   -> frec (depth+1) (frec depth acc (body_of_type t)) c
    | CLet (_,b,t,c) -> frec (depth+1) (frec depth (frec depth acc b) (body_of_type t)) c
    | VAR _         -> acc
    | DOP0 _        -> acc
  in 
  frec 1 acc m 

(* calcule la liste des arguments implicites *)

let poly_args env sigma t =
  let rec aux n t = match kind_of_term (whd_betadeltaiota env sigma t) with
    | IsProd (_,a,b) -> add_free_rels_until n a (aux (n+1) b)
    | IsCast (t',_) -> aux n t'
    | _ -> Intset.empty
  in 
  match kind_of_term (strip_outer_cast (whd_betadeltaiota env sigma t)) with 
    | IsProd (_,a,b) -> Intset.elements (aux 1 b)
    | _ -> []


(* Expanding existential variables (trad.ml, progmach.ml) *)
(* 1- whd_ise fails if an existential is undefined *)

exception Uninstantiated_evar of int

let rec whd_ise sigma = function
  | DOPN(Evar ev,args) when Evd.in_dom sigma ev ->
      if Evd.is_defined sigma ev then
        whd_ise sigma (existential_value sigma (ev,args))
      else raise (Uninstantiated_evar ev)
  | DOP2(Cast,c,_) -> whd_ise sigma c
  | DOP0(Sort(Type _)) -> DOP0(Sort(Type dummy_univ))
  | c -> c


(* 2- undefined existentials are left unchanged *)
let rec whd_ise1 sigma = function
  | DOPN(Evar ev,args) when Evd.in_dom sigma ev & Evd.is_defined sigma ev ->
      whd_ise1 sigma (existential_value sigma (ev,args))
  | DOP2(Cast,c,_) -> whd_ise1 sigma c
  (* A quoi servait cette ligne ???
  | DOP0(Sort(Type _)) -> DOP0(Sort(Type dummy_univ))
 *)
  | c -> c

let nf_ise1 sigma = strong (fun _ -> whd_ise1) empty_env sigma

(* A form of [whd_ise1] with type "reduction_function" *)
let whd_evar env = whd_ise1

(* Same as whd_ise1, but replaces the remaining ISEVAR by Metavariables
 * Similarly we have is_fmachine1_metas and is_resolve1_metas *)

let rec whd_ise1_metas sigma t = 
  let t' = strip_outer_cast t in
  match kind_of_term t' with
  | IsEvar (ev,args as k) when Evd.in_dom sigma ev ->
      if Evd.is_defined sigma ev then
      	whd_ise1_metas sigma (existential_value sigma k)
      else 
      	let m = DOP0(Meta (new_meta())) in
	DOP2(Cast,m,existential_type sigma k)
  | _ -> t'

