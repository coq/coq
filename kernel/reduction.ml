
(* $Id$ *)

open Pp
open Util
open Names
open Generic
open Term
open Univ
open Evd
open Constant
open Inductive
open Environ
open Instantiate
open Closure

let mt_evd = Evd.mt_evd

exception Redelimination
exception Induc
exception Elimconst

type 'a reduction_function = 'a unsafe_env -> constr -> constr
type 'a stack_reduction_function = 'a unsafe_env -> constr -> constr list 
  -> constr * constr list

(*************************************)
(*** Reduction Functions Operators ***)
(*************************************)

let rec under_casts f env = function
  | DOP2(Cast,c,t) -> DOP2(Cast,under_casts f env c, t)
  | c              -> f env c

let rec whd_stack env x stack =
  match x with
    | DOPN(AppL,cl)  -> whd_stack env cl.(0) (array_app_tl cl stack)
    | DOP2(Cast,c,_) -> whd_stack env c stack
    | _              -> (x,stack)
	  
let stack_reduction_of_reduction red_fun env x stack =
  let t = red_fun env (applistc x stack) in
  whd_stack env t []

let strong whdfun env = 
  let rec strongrec = function
    | DOP0 _ as t -> t
    (* Cas ad hoc *)
    | DOP1(oper,c) -> DOP1(oper,strongrec c)
    | DOP2(oper,c1,c2) -> DOP2(oper,strongrec c1,strongrec c2)
    | DOPN(oper,cl) -> DOPN(oper,Array.map strongrec cl)
    | DOPL(oper,cl) -> DOPL(oper,List.map strongrec cl)
    | DLAM(na,c) -> DLAM(na,strongrec c)
    | DLAMV(na,c) -> DLAMV(na,Array.map strongrec c)
    | VAR _ as t -> t
    | Rel _ as t -> t
  in
  strongrec

let rec strong_prodspine redfun env c = 
  match redfun env c with
    | DOP2(Prod,a,DLAM(na,b)) ->
        DOP2(Prod,a,DLAM(na,strong_prodspine redfun env b))
    | x -> x


(****************************************************************************)
(*                   Reduction Functions                                    *)
(****************************************************************************)


(* call by value reduction functions *)
let cbv_norm_flags flags env t =
  cbv_norm (create_cbv_infos flags env) t

let cbv_beta env = cbv_norm_flags beta env
let cbv_betaiota env = cbv_norm_flags betaiota env
let cbv_betadeltaiota env =  cbv_norm_flags betadeltaiota env

let compute = cbv_betadeltaiota


(* lazy reduction functions. The infos must be created for each term *)
let clos_norm_flags flgs env t =
  norm_val (create_clos_infos flgs env) (inject t)

let nf_beta env = clos_norm_flags beta env
let nf_betaiota env = clos_norm_flags betaiota env
let nf_betadeltaiota env =  clos_norm_flags betadeltaiota env


(* lazy weak head reduction functions *)
(* Pb: whd_val parcourt tout le terme, meme si aucune reduction n'a lieu *)
let whd_flags flgs env t =
  whd_val (create_clos_infos flgs env) (inject t)


(* Red reduction tactic: reduction to a product *)
let red_product env c = 
  let rec redrec x =
    match x with
      | DOPN(AppL,cl) -> 
	  DOPN(AppL,Array.append [|redrec (array_hd cl)|] (array_tl cl))
      | DOPN(Const _,_) when evaluable_const env x -> const_or_ex_value env x
      | DOPN(Abst _,_) when evaluable_abst env x -> abst_value env x 
      | DOP2(Cast,c,_) -> redrec c
      | DOP2(Prod,a,DLAM(x,b)) -> DOP2(Prod, a, DLAM(x, redrec b))  
      | _ -> error "Term not reducible"
  in 
  nf_betaiota env (redrec c)


(* Substitute only a list of locations locs, the empty list is interpreted
   as substitute all, if 0 is in the list then no substitution is done 
   the list may contain only negative occurrences that will not be substituted *)
(* Aurait sa place dans term.ml mais term.ml ne connait pas printer.ml *)
let subst_term_occ locs c t = 
  let rec substcheck except k occ c t =
    if except or List.exists (function u -> u>=occ) locs then
      substrec except k occ c t
    else 
      (occ,t)
  and substrec except k occ c t =
    if eq_constr t c then
      if except then 
	if List.mem (-occ) locs then (occ+1,t) else (occ+1,Rel(k))
      else 
	if List.mem occ locs then (occ+1,Rel(k)) else  (occ+1,t)
    else 
      match t with
	| DOPN(Const sp,tl) -> occ,t
	|  DOPN(MutConstruct _,tl) -> occ,t
	|  DOPN(MutInd _,tl) -> occ,t
	|  DOPN(i,cl) -> 
	     let (occ',cl') =   
               Array.fold_left 
		 (fun (nocc',lfd) f ->
		    let (nocc'',f') = substcheck except k nocc' c f in
                    (nocc'',f'::lfd)) 
		 (occ,[]) cl
             in 
	     (occ',DOPN(i,Array.of_list (List.rev cl')))
	|  DOP2(i,t1,t2) -> 
	     let (nocc1,t1')=substrec except k occ c t1 in
             let (nocc2,t2')=substcheck except k nocc1 c t2 in
             nocc2,DOP2(i,t1',t2')
	|  DOP1(i,t) -> 
	     let (nocc,t')= substrec except k occ c t in
	     nocc,DOP1(i,t')
	|  DLAM(n,t) -> 
	     let (occ',t') = substcheck except (k+1) occ (lift 1 c) t in
             (occ',DLAM(n,t'))
	|  DLAMV(n,cl) -> 
	     let (occ',cl') =   
               Array.fold_left 
		 (fun (nocc',lfd) f ->
		    let (nocc'',f') = 
		      substcheck except (k+1) nocc' (lift 1 c) f
                    in (nocc'',f'::lfd)) 
		 (occ,[]) cl
             in 
	     (occ',DLAMV(n,Array.of_list (List.rev cl') ))
	|  _ -> occ,t
  in 
  if locs = [] then 
    subst_term c t
  else if List.mem 0 locs then 
    t
  else 
    let except = List.for_all (fun n -> n<0) locs in
    let (nbocc,t') = substcheck except 1 1 c t in
    if List.exists (fun o -> o >= nbocc or o <= -nbocc) locs then
      failwith "subst_term_occ: too few occurences" 
    else 
      t'

(* linear substitution (following pretty-printer) of the value of name in c.
 * n is the number of the next occurence of name.
 * ol is the occurence list to find. *)
let rec substlin env name n ol c =
  match c with
    | DOPN(Const sp,_) ->
        if (path_of_const c)=name then
          if (List.hd ol)=n then
            if evaluable_const env c then 
	      ((n+1),(List.tl ol), const_or_ex_value env c)
            else
              errorlabstrm "substlin"
                [< 'sTR(string_of_path sp);
                   'sTR " is not a defined constant" >]
          else 
	    ((n+1),ol,c)
        else 
	  (n,ol,c)

    | DOPN(Abst _,_) ->
        if (path_of_abst c)=name then
          if (List.hd ol)=n then 
	    ((n+1),(List.tl ol), abst_value env c)
          else 
	    ((n+1),ol,c)
        else 
	  (n,ol,c)

(* INEFFICIENT: OPTIMIZE *)
    | DOPN(AppL,tl) ->
        let c1 = array_hd tl and cl = array_tl tl in
        Array.fold_left 
	  (fun (n1,ol1,c1') c2 ->
	     (match ol1 with 
                | [] -> (n1,[],applist(c1',[c2]))
                | _  ->
                    let (n2,ol2,c2') = substlin env name n1 ol1 c2 in
                    (n2,ol2,applist(c1',[c2']))))
          (substlin env name n ol c1) cl

    | DOP2(Lambda,c1,DLAM(na,c2)) ->
        let (n1,ol1,c1') = substlin env name n ol c1 in
        (match ol1 with 
           | [] -> (n1,[],DOP2(Lambda,c1',DLAM(na,c2)))
           | _  ->
               let (n2,ol2,c2') = substlin env name n1 ol1 c2 in
               (n2,ol2,DOP2(Lambda,c1',DLAM(na,c2'))))

    | DOP2(Prod,c1,DLAM(na,c2)) ->
        let (n1,ol1,c1') = substlin env name n ol c1 in
        (match ol1 with 
           | [] -> (n1,[],DOP2(Prod,c1',DLAM(na,c2)))
           | _  ->
               let (n2,ol2,c2') = substlin env name n1 ol1 c2 in
               (n2,ol2,DOP2(Prod,c1',DLAM(na,c2'))))
	
    | DOPN(MutCase _,_) -> 
	let (ci,p,d,llf) = destCase c in
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
           | [] -> (n1,[],mkMutCaseA ci p' d llf)
           | _  ->
               let (n2,ol2,d') = substlin env name n1 ol1 d in
               (match ol2 with
		  | [] -> (n2,[],mkMutCaseA ci p' d' llf)
		  | _  -> 
	              let (n3,ol3,lf') = substlist n2 ol2 (Array.to_list llf)
                      in (n3,ol3,mkMutCase ci p' d' lf')))
        
    | DOP2(Cast,c1,c2)   ->
        let (n1,ol1,c1') = substlin env name n ol c1 in
        (match ol1 with 
           | [] -> (n1,[],DOP2(Cast,c1',c2))
           | _  ->
               let (n2,ol2,c2') = substlin env name n1 ol1 c2 in
               (n2,ol2,DOP2(Cast,c1',c2')))

    | DOPN(Fix _,_) -> 
        (warning "do not consider occurrences inside fixpoints"; (n,ol,c))
	
    | DOPN(CoFix _,_) -> 
        (warning "do not consider occurrences inside cofixpoints"; (n,ol,c))
	
    | _ -> (n,ol,c)
	  
let unfold env name =
  let flag = 
    (UNIFORM,{ r_beta = true;
               r_delta = (fun op -> op=(Const name) or op=(Abst name));
               r_iota = true })
  in 
  clos_norm_flags flag env


(* unfoldoccs : (readable_constraints -> (int list * section_path) -> constr -> constr)
 * Unfolds the constant name in a term c following a list of occurrences occl.
 * at the occurrences of occ_list. If occ_list is empty, unfold all occurences.
 * Performs a betaiota reduction after unfolding. *)
let unfoldoccs env (occl,name) c =
  match occl with
    | []  -> unfold env name c
    | l -> 
        match substlin env name 1 (Sort.list (<) l) c with
          | (_,[],uc) -> nf_betaiota env uc
          | (1,_,_) -> error ((string_of_path name)^" does not occur")
          | _ -> error ("bad occurrence numbers of "^(string_of_path name))

(* Unfold reduction tactic: *)
let unfoldn loccname env c = 
  List.fold_left (fun c occname -> unfoldoccs env occname c) c loccname

(* Re-folding constants tactics: refold com in term c *)
let fold_one_com com env c =
  let rcom = red_product env com in
  subst1 com (subst_term rcom c)

let fold_commands cl env c =
  List.fold_right (fun com -> fold_one_com com env) (List.rev cl) c


(* Pattern *)

(* gives [na:ta]c' such that c converts to ([na:ta]c' a), abstracting only
 * the specified occurrences. *)

let abstract_scheme env (locc,a,ta) t =
  let na = named_hd env ta Anonymous in
  if occur_meta ta then
    error "cannot find a type for the generalisation"
  else if occur_meta a then 
    DOP2(Lambda,ta,DLAM(na,t))
  else 
    DOP2(Lambda, ta, DLAM(na,subst_term_occ locc a t))


let pattern_occs loccs_trm_typ env c =
  let abstr_trm = List.fold_right (abstract_scheme env) loccs_trm_typ c in
  applist(abstr_trm, List.map (fun (_,t,_) -> t) loccs_trm_typ)


(*************************************)
(*** Reduction using substitutions ***)
(*************************************)

(* 1. Beta Reduction *)

let rec stacklam recfun env t stack =
  match (stack,t) with
    | (h::stacktl, DOP2(Lambda,_,DLAM(_,c))) ->
        stacklam recfun (h::env) c stacktl
    | _ -> recfun (substl env t) stack


let beta_applist (c,l) = stacklam (fun c l -> applist(c,l)) [] c l


let whd_beta_stack env = 
  let rec whrec x stack = match x with
    | DOP2(Lambda,c1,DLAM(name,c2)) ->
	(match stack with
           | [] -> (x,[])
	   | a1::rest -> stacklam whrec [a1] c2 rest)
	
    | DOPN(AppL,cl) -> whrec (array_hd cl) (array_app_tl cl stack)
    | DOP2(Cast,c,_) -> whrec c stack
    | x -> (x,stack)
  in 
  whrec

let whd_beta env x = applist (whd_beta_stack env x [])


(* 2. Delta Reduction *)
		   
let whd_const_stack namelist env = 
  let rec whrec x l =
    match x with
      | DOPN(Const sp,_) as c ->
	  if List.mem sp namelist then
            if evaluable_const env c then
              whrec (const_or_ex_value env c) l
            else 
	      error "whd_const_stack"
	  else 
	    x,l

      | (DOPN(Abst sp,_)) as c ->
	  if List.mem sp namelist then
            if evaluable_abst env c then
              whrec (abst_value env c) l
            else 
	      error "whd_const_stack"
	  else 
	    x,l
	      
      | DOP2(Cast,c,_) -> whrec c l
      | DOPN(AppL,cl) -> whrec (array_hd cl) (array_app_tl cl l)
      | x -> x,l
  in 
  whrec

let whd_const namelist env c = applist(whd_const_stack namelist env c [])

let whd_delta_stack env = 
  let rec whrec x l =
    match x with
      | DOPN(Const _,_) as c ->
	  if evaluable_const env c then
            whrec (const_or_ex_value env c) l
	  else 
	    x,l
      | (DOPN(Abst _,_)) as c ->
	  if evaluable_abst env c then
            whrec (abst_value env c) l
	  else 
	    x,l
  | DOP2(Cast,c,_) -> whrec c l
  | DOPN(AppL,cl) -> whrec (array_hd cl) (array_app_tl cl l)
  | x -> x,l
  in 
  whrec

let whd_delta env c = applist(whd_delta_stack env c [])


let whd_betadelta_stack env = 
  let rec whrec x l =
    match x with
      | DOPN(Const _,_) ->
          if evaluable_const env x then 
	    whrec (const_or_ex_value env x) l
          else 
	    (x,l)
      | DOPN(Abst _,_) ->
          if evaluable_abst env x then 
	    whrec (abst_value env x) l
          else 
	    (x,l)
      | DOP2(Cast,c,_) -> whrec c l
      | DOPN(AppL,cl)  -> whrec (array_hd cl) (array_app_tl cl l)
      | DOP2(Lambda,_,DLAM(_,c)) ->
          (match l with
             | [] -> (x,l)
             | (a::m) -> stacklam whrec [a] c m)
      | x -> (x,l)
  in 
  whrec

let whd_betadelta env c = applist(whd_betadelta_stack env c [])


let whd_betadeltat_stack env = 
  let rec whrec x l =
    match x with
      | DOPN(Const _,_) ->
          if translucent_const env x then 
	    whrec (const_or_ex_value env x) l
          else 
	    (x,l)
      | DOPN(Abst _,_) ->
          if translucent_abst env x then 
	    whrec (abst_value env x) l
          else 
	    (x,l)
      | DOP2(Cast,c,_) -> whrec c l
      | DOPN(AppL,cl) -> whrec (array_hd cl) (array_app_tl cl l)
      | DOP2(Lambda,_,DLAM(_,c)) ->
          (match l with
             | [] -> (x,l)
             | (a::m) -> stacklam whrec [a] c m)
      | x -> (x,l)
  in 
  whrec
       
let whd_betadeltat env c = applist(whd_betadeltat_stack env c [])

let whd_betadeltaeta_stack env = 
  let rec whrec x stack =
    match x with
      | DOPN(Const _,_) ->
          if evaluable_const env x then
	    whrec (const_or_ex_value env x) stack
          else 
	    (x,stack)
      | DOPN(Abst _,_) ->
          if evaluable_abst env x then
	    whrec (abst_value env x) stack
          else 
	    (x,stack)
      | DOP2(Cast,c,_) -> whrec c stack
      | DOPN(AppL,cl)    -> whrec (array_hd cl) (array_app_tl cl stack)
      | DOP2(Lambda,_,DLAM(_,c)) ->
          (match stack with
             | [] -> 
		 (match applist (whrec c []) with 
                    | DOPN(AppL,cl) -> 
                        (match whrec (array_last cl) [] with 
                           | (Rel 1,[]) -> 
			       let napp = (Array.length cl) -1 in
                               if napp = 0 then (x,stack) else
                                 let lc = Array.sub cl 0 napp in
                                 let u = 
				   if napp = 1 then lc.(0) else DOPN(AppL,lc) 
                                 in 
				 if noccurn 1 u then (pop u,[]) else (x,stack)
                           | _ -> (x,stack))
                    | _ -> (x,stack))
             | (a::m) -> stacklam whrec [a] c m)
      | x -> (x,stack)
  in 
  whrec

let whd_betadeltaeta env x = applist(whd_betadeltaeta_stack env x [])

(* 3. Iota reduction *)

type 'a miota_args = {
  mP      : constr;     (* the result type *)
  mconstr : constr;     (* the constructor *)
  mci     : case_info;  (* special info to re-build pattern *)
  mcargs  : 'a list;    (* the constructor's arguments *)
  mlf     : 'a array }  (* the branch code vector *)
		       
let reducible_mind_case c =
  match c with 
    | DOPN(MutConstruct _,_) | DOPN(CoFix _,_) -> true
    | _  -> false

let contract_cofix = function
  | DOPN(CoFix(bodynum),bodyvect) ->
      let nbodies = (Array.length bodyvect) -1 in
      let make_Fi j = DOPN(CoFix(j),bodyvect) in
      sAPPViList bodynum (array_last bodyvect) (list_tabulate make_Fi nbodies)
  | _ -> assert false

let mind_nparams env i =
  let mis = lookup_mind_specif i env in mis.mis_mib.mind_nparams

let reduce_mind_case env mia =
  match mia.mconstr with 
    | DOPN(MutConstruct((indsp,tyindx),i),_) ->
	let ind = DOPN(MutInd(indsp,tyindx),args_of_mconstr mia.mconstr) in
	let nparams = mind_nparams env ind in
	let real_cargs = snd (list_chop nparams mia.mcargs) in
        applist (mia.mlf.(i-1),real_cargs)
    | DOPN(CoFix _,_) as cofix ->
	let cofix_def = contract_cofix cofix in
	mkMutCaseA mia.mci mia.mP (applist(cofix_def,mia.mcargs)) mia.mlf
    | _ -> assert false

(* contracts fix==FIX[nl;i](A1...Ak;[F1...Fk]{B1....Bk}) to produce

   Bi[Fj --> FIX[nl;j](A1...Ak;[F1...Fk]{B1...Bk})]

 *)
let contract_fix = function 
  | DOPN(Fix(recindices,bodynum),bodyvect) -> 
      let nbodies = Array.length recindices in
      let make_Fi j = DOPN(Fix(recindices,j),bodyvect) in
      sAPPViList bodynum (array_last bodyvect) (list_tabulate make_Fi nbodies)
  | _ -> assert false

let fix_recarg fix stack =
  match fix with 
    | DOPN(Fix(recindices,bodynum),_) ->
    	if 0 <= bodynum & bodynum < Array.length recindices then
	  let recargnum = Array.get recindices bodynum in
          (try Some(recargnum, List.nth stack recargnum)
           with Failure "nth" | Invalid_argument "List.nth" -> None)
    	else None
    | _ -> assert false

let reduce_fix whfun fix stack =
  match fix with 
    | DOPN(Fix(recindices,bodynum),bodyvect) ->
    	(match fix_recarg fix stack with
           | None -> (false,(fix,stack))
	   | Some (recargnum,recarg) ->
               let (recarg'hd,_ as recarg') = whfun recarg [] in
               let stack' = list_assign stack recargnum (applist recarg') in
	       (match recarg'hd with
                  | DOPN(MutConstruct _,_) -> 
		      (true,(contract_fix fix,stack'))
		  | _ -> (false,(fix,stack'))))
    | _ -> assert false

(* NB : Cette fonction alloue peu c'est l'appel 
     ``let (recarg'hd,_ as recarg') = whfun recarg [] in''
                                     --------------------
qui coute cher dans whd_betadeltaiota *)

let whd_betaiota_stack env = 
  let rec whrec x stack =
    match x with
      | DOP2(Cast,c,_) -> whrec c stack
      | DOPN(AppL,cl)    -> whrec (array_hd cl) (array_app_tl cl stack)
      | DOP2(Lambda,_,DLAM(_,c)) ->
          (match stack with
             | [] -> (x,stack)
             | (a::m) -> stacklam whrec [a] c m)
      | DOPN(MutCase _,_) ->
          let (ci,p,d,lf) = destCase x in
          let (c,cargs) = whrec d [] in
          if reducible_mind_case c then
            whrec (reduce_mind_case env
                     {mP=p; mconstr=c; mcargs=cargs; mci=ci; mlf=lf}) stack
          else 
	    (mkMutCaseA ci p (applist(c,cargs)) lf, stack)
            
      | DOPN(Fix _,_) ->
          let (reduced,(fix,stack)) = reduce_fix whrec x stack in
          if reduced then whrec fix stack else (fix,stack)
      | x -> (x,stack)
  in 
  whrec    

let whd_betaiota env x = applist (whd_betaiota_stack env x [])


let whd_betadeltatiota_stack env = 
  let rec whrec x stack =
    match x with
      | DOPN(Const _,_) ->
          if translucent_const env x then
            whrec (const_or_ex_value env x) stack
          else 
	    (x,stack)
      | DOPN(Abst _,_) ->
          if translucent_abst env x then
	    whrec (abst_value env x) stack
          else
	    (x,stack)
      | DOP2(Cast,c,_) -> whrec c stack
      | DOPN(AppL,cl)    -> whrec (array_hd cl) (array_app_tl cl stack)
      | DOP2(Lambda,_,DLAM(_,c)) ->
          (match stack with
             | [] -> (x,stack)
             | (a::m) -> stacklam whrec [a] c m)
      | DOPN(MutCase _,_) ->
          let (ci,p,d,lf) = destCase x in
          let (c,cargs) = whrec d [] in
          if reducible_mind_case c then
	    whrec (reduce_mind_case env
                     {mP=p; mconstr=c; mcargs=cargs; mci=ci; mlf=lf}) stack
          else 
	    (mkMutCaseA ci p (applist(c,cargs)) lf,stack)
      | DOPN(Fix _,_) ->
          let (reduced,(fix,stack)) = reduce_fix whrec x stack in
          if reduced then whrec fix stack else (fix,stack)
      | x -> (x,stack)
 in 
  whrec   

let whd_betadeltatiota env x = applist(whd_betadeltatiota_stack env x [])

let whd_betadeltaiota_stack env =
  let rec bdi_rec x stack =
    match x with
      | DOPN(Const _,_) ->
          if evaluable_const env x then
	    bdi_rec (const_or_ex_value env x) stack
          else 
	    (x,stack)
      | DOPN(Abst _,_) ->
          if evaluable_abst env x then 
	    bdi_rec (abst_value env x) stack 
	  else 
	    (x,stack)
      | DOP2(Cast,c,_) -> bdi_rec c stack
      | DOPN(AppL,cl) ->  bdi_rec (array_hd cl)  (array_app_tl cl stack)
      | DOP2(Lambda,_,DLAM(_,c)) ->
          (match stack with
             | [] -> (x,stack)
             | (a::m) -> stacklam bdi_rec [a] c m)
      | DOPN(MutCase _,_) ->
          let (ci,p,d,lf) = destCase x in
          let (c,cargs) = bdi_rec d [] in
          if reducible_mind_case c then
            bdi_rec (reduce_mind_case env
		       {mP=p; mconstr=c; mcargs=cargs; mci=ci; mlf=lf}) stack
          else 
	    (mkMutCaseA ci p (applist(c,cargs)) lf,stack)
      | DOPN(Fix _,_) -> 
          let (reduced,(fix,stack)) = reduce_fix bdi_rec x stack in
          if reduced then bdi_rec fix stack else (fix,stack)
      | x -> (x,stack)
  in
  bdi_rec

let whd_betadeltaiota env x = applist(whd_betadeltaiota_stack env x [])
				
				
let whd_betadeltaiotaeta_stack env = 
  let rec whrec x stack =
    match x with
      | DOPN(Const _,_) ->
          if evaluable_const env x then 
	    whrec (const_or_ex_value env x) stack
          else 
	    (x,stack)
      | DOPN(Abst _,_) ->
          if evaluable_abst env x then
	    whrec (abst_value env x) stack
          else 
	    (x,stack)
      | DOP2(Cast,c,_) -> whrec c stack
      | DOPN(AppL,cl) -> whrec (array_hd cl) (array_app_tl cl stack)
      | DOP2(Lambda,_,DLAM(_,c)) ->
          (match stack with
             | [] ->
                 (match applist (whrec c []) with 
                    | DOPN(AppL,cl) -> 
                        (match whrec (array_last cl) [] with 
                           | (Rel 1,[]) ->
                               let napp = (Array.length cl) -1 in
                               if napp = 0 then 
				 (x,stack) 
			       else
                                 let lc = Array.sub cl 0 napp in
                                 let u = 
				   if napp = 1 then lc.(0) else DOPN(AppL,lc) 
                                 in 
				 if noccurn 1 u then (pop u,[]) else (x,stack)
                           | _ -> (x,stack))
                    | _ -> (x,stack))
             | (a::m) -> stacklam whrec [a] c m)

      | DOPN(MutCase _,_) ->
          let (ci,p,d,lf) = destCase x in
          let (c,cargs) = whrec d [] in
          if reducible_mind_case c then
	    whrec (reduce_mind_case env
                     {mP=p; mconstr=c; mcargs=cargs; mci=ci; mlf=lf}) stack
          else 
	    (mkMutCaseA ci p (applist(c,cargs)) lf,stack)
      | DOPN(Fix _,_) ->
          let (reduced,(fix,stack)) = reduce_fix whrec x stack in
          if reduced then whrec fix stack else (fix,stack)
      | x -> (x,stack)
  in 
  whrec  

let whd_betadeltaiotaeta env x = applist(whd_betadeltaiotaeta_stack env x [])

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

type 'a conversion_function = 'a unsafe_env -> constr -> constr -> constraints

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
  array_fold_left2 (fun c x y -> f x y c) c v1 v2

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

    | (FOP0(Meta(n)), FOP0(Meta(m))) ->
        bool_and_convert (n=m) 
	  (convert_forall2 (ccnv (pb_equal cv_pb) infos lft1 lft2) v1 v2)

    (* 2 constants or 2 abstractions *)
    | (FOPN(Const sp1,al1), FOPN(Const sp2,al2)) ->
	convert_or
	  (* try first intensional equality *)
	  (bool_and_convert (sp1 == sp2 or sp1 = sp2)
	     (convert_and
		(convert_forall2 (ccnv (pb_equal cv_pb) infos el1 el2) al1 al2)
		(convert_forall2 (ccnv (pb_equal cv_pb) infos lft1 lft2) v1 v2)))
          (* else expand the second occurrence (arbitrary heuristic) *)
          (match search_frozen_cst infos (Const sp2) al2 with
             | Some def2 -> 
		 eqappr cv_pb infos appr1 (lft2, fhnf_apply infos n2 def2 v2)
             | None -> (match search_frozen_cst infos (Const sp1) al1 with
                          | Some def1 -> eqappr cv_pb infos
				(lft1, fhnf_apply infos n1 def1 v1) appr2
			  | None -> fun _ -> raise NotConvertible))

    | (FOPN(Abst sp1,al1), FOPN(Abst sp2,al2)) ->
	convert_or
	  (* try first intensional equality *)
          (bool_and_convert  (sp1 = sp2)
	     (convert_and
		(convert_forall2 (ccnv (pb_equal cv_pb) infos el1 el2) al1 al2)
		(convert_forall2 (ccnv (pb_equal cv_pb) infos lft1 lft2) v1 v2)))
          (* else expand the second occurrence (arbitrary heuristic) *)
          (match search_frozen_cst infos (Abst sp2) al2 with
             | Some def2 -> 
		 eqappr cv_pb infos appr1 (lft2, fhnf_apply infos n2 def2 v2)
             | None -> (match search_frozen_cst infos (Abst sp1) al2 with
                          | Some def1 -> eqappr cv_pb infos
				(lft1, fhnf_apply infos n1 def1 v1) appr2
			  | None -> fun _ -> raise NotConvertible))

    (* only one constant or abstraction *)
    | (FOPN((Const _ | Abst _) as op,al1), _)      ->
        (match search_frozen_cst infos op al1 with
           | Some def1 -> 
	       eqappr cv_pb infos (lft1, fhnf_apply infos n1 def1 v1) appr2
           | None -> fun _ -> raise NotConvertible)

    | (_, FOPN((Const _ | Abst _) as op,al2))      ->
        (match search_frozen_cst infos op al2 with
           | Some def2 -> 
	       eqappr cv_pb infos appr1 (lft2, fhnf_apply infos n2 def2 v2)
           | None -> fun _ -> raise NotConvertible)
	
    (* other constructors *)
    | (FOP2(Lambda,c1,c2), FOP2(Lambda,c'1,c'2)) ->
        bool_and_convert
	  (Array.length v1 = 0 && Array.length v2 = 0)
          (convert_and
	     (ccnv (pb_equal cv_pb) infos el1 el2 c1 c'1)
             (ccnv (pb_equal cv_pb) infos el1 el2 c2 c'2))

    | (FOP2(Prod,c1,c2), FOP2(Prod,c'1,c'2)) ->
	bool_and_convert
          (Array.length v1 = 0 && Array.length v2 = 0)
	  (convert_and
             (ccnv (pb_equal cv_pb) infos el1 el2 c1 c'1) (* Luo's system *)
             (ccnv cv_pb infos el1 el2 c2 c'2))

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


let fconv cv_pb env t1 t2 =
  let t1 = strong (fun _ -> strip_outer_cast) env t1
  and t2 = strong (fun _ -> strip_outer_cast) env t2 in
  if eq_constr t1 t2 then 
    Constraint.empty
  else
    let infos = create_clos_infos hnf_flags env in
    ccnv cv_pb infos ELID ELID (inject t1) (inject t2) Constraint.empty

let conv env = fconv CONV env
let conv_leq env = fconv CONV_LEQ env 

let conv_forall2 f env v1 v2 =
  array_fold_left2 
    (fun c x y -> let c' = f env x y in Constraint.union c c')
    Constraint.empty
    v1 v2

let conv_forall2_i f env v1 v2 =
  array_fold_left2_i 
    (fun i c x y -> let c' = f i env x y in Constraint.union c c')
    Constraint.empty
    v1 v2

let test_conversion f env x y =
  try let _ = f env x y in true with NotConvertible -> false

let is_conv env = test_conversion conv env
let is_conv_leq env = test_conversion conv_leq env


(********************************************************************)
(*             Special-Purpose Reduction                            *)
(********************************************************************)

let whd_meta env = function
  | DOP0(Meta p) as u -> (try List.assoc p (metamap env) with Not_found -> u)
  | x -> x
	
(* Try to replace all metas. Does not replace metas in the metas' values
 * Differs from (strong whd_meta). *)
let plain_instance env c = 
  let s = metamap env in
  let rec irec = function
    | DOP0(Meta p) as u -> (try List.assoc p s with Not_found -> u)
    | DOP1(oper,c)      -> DOP1(oper, irec c)
    | DOP2(oper,c1,c2)  -> DOP2(oper, irec c1, irec c2)
    | DOPN(oper,cl)     -> DOPN(oper, Array.map irec cl)
    | DOPL(oper,cl)     -> DOPL(oper, List.map irec cl)
    | DLAM(x,c)         -> DLAM(x, irec c)
    | DLAMV(x,v)        -> DLAMV(x, Array.map irec v)
    | u                 -> u
  in 
  if s = [] then c else irec c
    
(* Pourquoi ne fait-on pas nf_betaiota si s=[] ? *)
let instance env c = 
  let s = metamap env in
  if s = [] then c else nf_betaiota env (plain_instance env c)


(* pseudo-reduction rule:
 * [hnf_prod_app env s (Prod(_,B)) N --> B[N]
 * with an HNF on the first argument to produce a product.
 * if this does not work, then we use the string S as part of our
 * error message.
 *)
let hnf_prod_app env s t n =
  match whd_betadeltaiota env t with
    | DOP2(Prod,_,b) -> sAPP b n
    | _ ->
	errorlabstrm s [< 'sTR"Needed a product, but didn't find one in " ;
			  'sTR s ; 'fNL >]

let hnf_prod_appvect env s t nL = Array.fold_left (hnf_prod_app env s) t nL
let hnf_prod_applist env s t nL = List.fold_left (hnf_prod_app env s) t nL
				    
let hnf_lam_app env s t n =
  match whd_betadeltaiota env t with
    | DOP2(Lambda,_,b) -> sAPP b n
    | _ ->
	errorlabstrm s [< 'sTR"Needed a product, but didn't find one in " ;
			  'sTR s ; 'fNL >]

let hnf_lam_appvect env s t nL = Array.fold_left (hnf_lam_app env s) t nL
let hnf_lam_applist env s t nL = List.fold_left (hnf_lam_app env s) t nL

let splay_prod env = 
  let rec decrec m c =
    match whd_betadeltaiota env c with
      | DOP2(Prod,a,DLAM(n,c_0))            -> decrec ((n,a)::m) c_0
      | t -> m,t
  in 
  decrec []
  
let decomp_prod env = 
  let rec decrec m c =
    match whd_betadeltaiota env c with
      | DOP0(Sort _) as x -> m,x
      | DOP2(Prod,a,DLAM(n,c_0))            -> decrec (m+1) c_0
      | _                      -> error "decomp_prod: Not a product"
  in 
  decrec 0
    
let decomp_n_prod env n = 
  let rec decrec m ln c = if m = 0 then (ln,c) else 
    match whd_betadeltaiota env c with
      | DOP2(Prod,a,DLAM(n,c_0)) -> decrec (m-1) ((n,a)::ln) c_0
      | _                      -> error "decomp_n_prod: Not enough products"
  in 
  decrec n []

(* Special iota reduction... *)

let contract_cofix_use_function f cofix =
  match cofix with 
    | DOPN(CoFix(bodynum),bodyvect) ->
  	let nbodies =  (Array.length bodyvect) -1 in
  	let make_Fi j = DOPN(CoFix(j),bodyvect) in
  	let lbodies = list_assign (list_tabulate make_Fi nbodies) bodynum f in
  	sAPPViList bodynum (array_last bodyvect) lbodies
    | _ -> assert false

let reduce_mind_case_use_function env f mia =
  match mia.mconstr with 
    | DOPN(MutConstruct((indsp,tyindx),i),_) ->
	let ind = DOPN(MutInd(indsp,tyindx),args_of_mconstr mia.mconstr) in
	let nparams = mind_nparams env ind in
	let real_cargs = snd(list_chop nparams mia.mcargs) in
	applist (mia.mlf.(i-1),real_cargs)
    | DOPN(CoFix _,_) as cofix ->
	let cofix_def = contract_cofix_use_function f cofix in
	mkMutCaseA mia.mci mia.mP (applist(cofix_def,mia.mcargs)) mia.mlf
    | _ -> assert false
	  
let special_red_case env whfun p c ci lf  =
  let rec redrec c l = 
    let (constr,cargs) = whfun c l in 
    match constr with 
      | DOPN(Const _,_) as g -> 
          if (evaluable_const env g) then
            let gvalue = (const_or_ex_value env g) in
            if reducible_mind_case  gvalue then
              reduce_mind_case_use_function env g
                {mP=p; mconstr=gvalue; mcargs=cargs; mci=ci; mlf=lf}
            else 
	      redrec gvalue cargs
          else 
	    raise Redelimination
      | _ ->
          if reducible_mind_case constr then
            reduce_mind_case env
              {mP=p; mconstr=constr; mcargs=cargs; mci=ci; mlf=lf}
          else 
	    raise Redelimination
  in 
  redrec c []


(* F is convertible to DOPN(Fix(recindices,bodynum),bodyvect) make 
the reduction using this extra information *)

let contract_fix_use_function f fix =
  match fix with 
    | DOPN(Fix(recindices,bodynum),bodyvect) ->
  	let nbodies = Array.length recindices in
  	let make_Fi j = DOPN(Fix(recindices,j),bodyvect) in
  	let lbodies = list_assign (list_tabulate make_Fi nbodies) bodynum f in
	  sAPPViList bodynum (array_last bodyvect) lbodies
    | _ -> assert false


let reduce_fix_use_function f whfun fix stack =
  match fix with 
    | DOPN (Fix(recindices,bodynum),bodyvect) ->
	(match fix_recarg fix stack with
           | None -> (false,(fix,stack))
	   | Some (recargnum,recarg) ->
               let (recarg'hd,_ as recarg')= whfun recarg [] in
               let stack' = list_assign stack recargnum (applist recarg') in
	       (match recarg'hd with
                  | DOPN(MutConstruct _,_) ->
		      (true,(contract_fix_use_function f fix,stack'))
		  | _ -> (false,(fix,stack'))))
    | _ -> assert false


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

let compute_consteval env c = 
  let rec srec n labs c =
    match whd_betadeltaeta_stack env c [] with 
      | (DOP2(Lambda,t,DLAM(_,g)),[])  -> srec (n+1) (t::labs) g
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

let rec apprec env c stack =
  let (t,stack) = whd_betaiota_stack env c stack in
  match t with
    | DOPN(MutCase _,_) ->
        let (ci,p,d,lf) = destCase t in
        let (cr,crargs) = whd_betadeltaiota_stack env d [] in
        let rslt = mkMutCaseA ci p (applist(cr,crargs)) lf in
        if reducible_mind_case cr then 
	  apprec env rslt stack
        else 
	  (t,stack)
    | DOPN(Fix _,_) ->
        let (reduced,(fix,stack)) = 
	  reduce_fix (whd_betadeltaiota_stack env) t stack 
	in
        if reduced then apprec env fix stack else (fix,stack)
    | _ -> (t,stack)

let hnf env c = apprec env c []

(* A reduction function like whd_betaiota but which keeps casts
 * and does not reduce redexes containing meta-variables.
 * ASSUMES THAT APPLICATIONS ARE BINARY ONES.
 * Used in Programs.
 * Added by JCF, 29/1/98. *)

let whd_programs_stack env = 
  let rec whrec x stack =
    match x with
      | DOPN(AppL,cl)    ->
	  if occur_meta cl.(1) then
	    (x,stack)
	  else
	    whrec (array_hd cl) (array_app_tl cl stack)
      | DOP2(Lambda,_,DLAM(_,c)) ->
          (match stack with
             | [] -> (x,stack)
             | (a::m) -> stacklam whrec [a] c m)
      | DOPN(MutCase _,_) ->
          let (ci,p,d,lf) = destCase x in
	  if occur_meta d then
	    (x,stack)
	  else
            let (c,cargs) = whrec d [] in
            if reducible_mind_case c then
	      whrec (reduce_mind_case env
		       {mP=p; mconstr=c; mcargs=cargs; mci=ci; mlf=lf})
		    stack
	    else
	      (mkMutCaseA ci p (applist(c,cargs)) lf, stack)
      | DOPN(Fix _,_) ->
          let (reduced,(fix,stack)) = reduce_fix whrec x stack in
          if reduced then whrec fix stack else (fix,stack)
      | x -> (x,stack)
  in 
  whrec    

let whd_programs env x = applist (whd_programs_stack env x [])

let find_mrectype env c =
  let (t,l) = whd_betadeltaiota_stack env c [] in
  match t with
    | DOPN(MutInd (sp,i),_) ->  (t,l)
    | _ -> raise Induc

let find_minductype env c =
  let (t,l) = whd_betadeltaiota_stack env c [] in
  match t with
    | DOPN(MutInd (sp,i),_)
        when mind_type_finite (lookup_mind sp env) i -> (t,l)
    | _ -> raise Induc

let find_mcoinductype env c =
  let (t,l) = whd_betadeltaiota_stack env c [] in
  match t with
    | DOPN(MutInd (sp,i),_)
        when not (mind_type_finite (lookup_mind sp env) i) -> (t,l)
    | _ -> raise Induc

let minductype_spec env c = 
  try 
    let (x,l) = find_minductype env c in
    if l<>[] then anomaly "minductype_spec: Not a recursive type 1" else x
  with Induc -> 
    anomaly "minductype_spec: Not a recursive type 2"
      
let mrectype_spec env c = 
  try 
    let (x,l) = find_mrectype env c in
    if l<>[] then anomaly "mrectype_spec: Not a recursive type 1" else x
  with Induc -> 
    anomaly "mrectype_spec: Not a recursive type 2"

let check_mrectype_spec env c =
  try 
    let (x,l) = find_mrectype env c in
    if l<>[] then error "check_mrectype: Not a recursive type 1" else x
  with Induc -> 
    error "check_mrectype: Not a recursive type 2"


exception IsType

let is_arity env = 
  let rec srec c = 
    match whd_betadeltaiota env c with 
      | DOP0(Sort _) -> true
      | DOP2(Prod,_,DLAM(_,c')) -> srec c' 
      | DOP2(Lambda,_,DLAM(_,c')) -> srec c' 
      | _ -> false
  in 
  srec 
 
let info_arity env = 
  let rec srec c = 
    match whd_betadeltaiota env c with 
      | DOP0(Sort(Prop Null)) -> false 
      | DOP0(Sort(Prop Pos)) -> true 
      | DOP2(Prod,_,DLAM(_,c')) -> srec c' 
      | DOP2(Lambda,_,DLAM(_,c')) -> srec c' 
      | _ -> raise IsType
  in 
  srec 
    
let is_logic_arity env c = 
  try (not (info_arity env c)) with IsType -> false

let is_info_arity env c = 
  try (info_arity env c) with IsType -> true
   
let is_type_arity env = 
  let rec srec c = 
    match whd_betadeltaiota env c with 
      | DOP0(Sort(Type _)) -> true
      | DOP2(Prod,_,DLAM(_,c')) -> srec c' 
      | DOP2(Lambda,_,DLAM(_,c')) -> srec c' 
      | _ -> false
  in 
  srec 

let is_info_type env t =
  let s = t.typ in
  (s = Prop Pos) ||
  (s <> Prop Null && 
   try info_arity env t.body with IsType -> true)

let is_info_cast_type env c = 
  match c with  
    | DOP2(Cast,c,t) -> 
	(try info_arity env t 
         with IsType -> try info_arity env c with IsType -> true)
    |  _ -> try info_arity env c with IsType -> true
	   
let contents_of_cast_type env c = 
  if is_info_cast_type env c then Pos else Null

let is_info_sort = is_info_arity

(* calcul des arguments implicites *)

(* la seconde liste est ordonne'e *)

let ord_add x l =
  let rec aux l = match l with 
    | []    -> [x]
    | y::l' -> if y > x then x::l else if x = y then l else y::(aux l')
  in 
  aux l
    
let add_free_rels_until depth m acc =
  let rec frec depth loc acc = function
    | Rel n -> 
	if (n <= depth) & (n > loc) then (ord_add (depth-n+1) acc) else acc
    | DOPN(_,cl)    -> Array.fold_left (frec depth loc) acc cl
    | DOPL(_,cl)    -> List.fold_left (frec depth loc) acc cl
    | DOP2(_,c1,c2) -> frec depth loc (frec depth loc acc c1) c2
    | DOP1(_,c)     -> frec depth loc acc c
    | DLAM(_,c)     -> frec (depth+1) (loc+1) acc c
    | DLAMV(_,cl)   -> Array.fold_left (frec (depth+1) (loc+1)) acc cl
    | VAR _         -> acc
    | DOP0 _        -> acc
  in 
  frec depth 0 acc m 

(* calcule la liste des arguments implicites *)

let poly_args env t =
  let rec aux n t = match (whd_betadeltaiota env t) with
    | DOP2(Prod,a,DLAM(_,b)) -> add_free_rels_until n a (aux (n+1) b)
    | DOP2(Cast,t',_) -> aux n t'
    | _ -> []
  in 
  match (strip_outer_cast (whd_betadeltaiota env t)) with 
    | DOP2(Prod,a,DLAM(_,b)) -> aux 1 b
    | _ -> []

(* Expanding existential variables (trad.ml, progmach.ml) *)
(* 1- whd_ise fails if an existential is undefined *)
let rec whd_ise env = function
  | DOPN(Const sp,_) as k ->
      if Evd.in_dom (evar_map env) sp then
        if defined_const env k then
          whd_ise env (const_or_ex_value env k)
        else
          errorlabstrm "whd_ise"
            [< 'sTR"There is an unknown subterm I cannot solve" >]
      else 
	k
  | DOP2(Cast,c,_) -> whd_ise env c
  | DOP0(Sort(Type(_))) -> DOP0(Sort(Type(dummy_univ)))
  | c -> c


(* 2- undefined existentials are left unchanged *)
let rec whd_ise1 env = function
  | (DOPN(Const sp,_) as k) ->
      if Evd.in_dom (evar_map env) sp & defined_const env k then
        whd_ise1 env (const_or_ex_value env k)
      else 
	k
  | DOP2(Cast,c,_) -> whd_ise1 env c
  | DOP0(Sort(Type(_))) -> DOP0(Sort(Type(dummy_univ)))
  | c -> c

let nf_ise1 env = strong (whd_ise1 env) env

(* Same as whd_ise1, but replaces the remaining ISEVAR by Metavariables
 * Similarly we have is_fmachine1_metas and is_resolve1_metas *)

let rec whd_ise1_metas env = function
  | (DOPN(Const sp,_) as k) ->
      if Evd.in_dom (evar_map env) sp then
	if defined_const env k then
      	  whd_ise1_metas env (const_or_ex_value env k)
	else 
      	  let m = DOP0(Meta (new_meta())) in
	  DOP2(Cast,m,const_or_ex_type env k)
      else
	k
  | DOP2(Cast,c,_) -> whd_ise1_metas env c
  | c -> c

(* Fonction spéciale qui laisse les cast clés sous les Fix ou les MutCase *)

let under_outer_cast f = function
  | DOP2 (Cast,b,t) -> DOP2 (Cast,f b,f t)
  | c -> f c

let rec strip_all_casts t = 
  match t with
    | DOP2 (Cast, b, _) -> strip_all_casts b
    | DOP0 _ as t -> t
    (* Cas ad hoc *)
    | DOPN(Fix _ as f,v) -> 
	let n = Array.length v in
	let ts = Array.sub v 0 (n-1) in
	let b = v.(n-1) in 
	DOPN(f, Array.append 
	       (Array.map strip_all_casts ts)
	       [|under_outer_cast strip_all_casts b|])
    | DOPN(CoFix _ as f,v) -> 
	let n = Array.length v in
	let ts = Array.sub v 0 (n-1) in
	let b = v.(n-1) in 
	DOPN(f, Array.append 
	       (Array.map strip_all_casts ts)
	       [|under_outer_cast strip_all_casts b|])
    | DOP1(oper,c) -> DOP1(oper,strip_all_casts c)
    | DOP2(oper,c1,c2) -> DOP2(oper,strip_all_casts c1,strip_all_casts c2)
    | DOPN(oper,cl) -> DOPN(oper,Array.map strip_all_casts cl)
    | DOPL(oper,cl) -> DOPL(oper,List.map strip_all_casts cl)
    | DLAM(na,c) -> DLAM(na,strip_all_casts c)
    | DLAMV(na,c) -> DLAMV(na,Array.map (under_outer_cast strip_all_casts) c)
    | VAR _ as t -> t
    | Rel _ as t -> t
