(****************************************************************************)
(*                 The Calculus of Inductive Constructions                  *)
(*                                                                          *)
(*                                Projet Coq                                *)
(*                                                                          *)
(*                     INRIA        LRI-CNRS        ENS-CNRS                *)
(*              Rocquencourt         Orsay          Lyon                    *)
(*                                                                          *)
(*                                 Coq V6.3                                 *)
(*                               July 1st 1999                              *)
(*                                                                          *)
(****************************************************************************)
(*                                multcase.ml                               *)
(****************************************************************************)

(* This file is linked to the system through  trad.ml in order to be able
 * to type during macro expansion. The functions here receive the closure
 * of pretype and some other functions from trad.ml.
 *)

open Std;;
open More_util;;
open Himsg;;
open Pp;;
open Vectops;;
open Generic;;
open Term;;
open Termenv;;
open Reduction;;
open Typing;;
open Names;;
open Multcase_astterm;; 
open Astterm;;
open Indrec;;
open Tradevar;;
open Rawterm;;


(* == General purpose functions == *)

(* J'ai remplace strip_outer_cast par whd_castapp. A revoir. PAPAGENO 01/1999
let whd_cast = strip_outer_cast;;
***********)

let mtevd = Evd.mt_evd ();;

let whd_cast = whd_castapp;;

let starts_with_underscore id = 
 let s=string_of_id id in (String.get s 0)='_';;


let makelist n elem =
 let rec makerec n  =
   if n=0 then []
    else elem::(makerec (n-1)) 
 in makerec n 
;;
 
let rec map_append_vect f v = 
  let length = Array.length v in 
  let rec map_rec i =
    if i>=length then [] 
    else (f v.(i))@ map_rec (i+1) 

  in map_rec 0  
;;


(* behaves as lam_and_popl but receives an environment instead of a 
 *  dbenvironment
 *)
let elam_and_popl n env body l =
  let ENVIRON(sign,dbenv)=env  in
  let ndbenv,a,l = lam_and_popl n dbenv body l
  in ENVIRON(sign,ndbenv),a,l
;;


(* behaves as lam_and_popl_named but receives an environment instead of a 
 *  dbenvironment
 *)
let elam_and_popl_named n env body l  =
  let ENVIRON(sign,dbenv)=env  in
  let ndbenv,a,l = lam_and_popl_named n dbenv body l
  in ENVIRON(sign,ndbenv),a,l
;;
 

(* General functions on inductive types *)

(* yields the number of indexes of the inductive type ty *)
let nb_localargs {nparams=nparams;arity=arity} =
  (fst (decomp_prod mtevd arity)) - nparams
;; 

let ctxt_of_ids ids =
  Array.of_list (List.map (function id -> VAR id) ids)

let mutconstruct_of_constructor (((sp,i),j),args) = 
  mkMutConstruct sp i j (ctxt_of_ids args)
let mutind_of_constructor (((sp,i),_),args) = mkMutInd sp i (ctxt_of_ids args)
let mutind_of_ind (sp,i,args) = mkMutInd sp i args

let ith_constructor i {mind=(sp, tyi, cl)} = mkMutConstruct sp tyi i cl
;;

(* determines whether is a predicate or not *)
let is_predicate ind_data = (nb_localargs ind_data > 0);;

(* === Closures imported from trad.ml to perform typing === *)

type 'a trad_functions  = 
  { pretype : trad_constraint -> environment -> rawconstr -> judgement;
    isevars :     'a Evd.evar_map ref
    };;

let mssg_hd_is_not_constructor cstr ind =
  let pi = pTERM (mutind_of_ind ind) in
  let pc = pTERM (mutconstruct_of_constructor cstr) in
  let pt = pTERM (mutind_of_constructor cstr) in
    [< 'sTR "Expecting a constructor of type "; pi; 'bRK(1,1) ;
       'sTR " but found the constructor " ; pc; 'bRK(1,1) ;
       'sTR " of type "; pt >]
;;

let mssg_tomatch_of_unexpected_type cstr ty =
  let pi = pTERM ty in
  let pc = pTERM (mutconstruct_of_constructor cstr) in
  let pt = pTERM (mutind_of_constructor cstr) in
    [< 'sTR "The term to match is of type "; pi; 'bRK(1,1) ;
       'sTR " but it is matched against the constructor " ; pc; 'bRK(1,1) ;
       'sTR " of type "; pt >]
;;

let mssg_wrong_num_arg_in_constr cstr n =
  let pc = pTERM (mutconstruct_of_constructor cstr) in
  [<'sTR "The constructor "; pc;
    'sTR " expects " ; 'iNT n ; 'sTR " arguments. ">]
;;


(* The type of patterns.
 * Makes pattern-matching safer than on a constr, and we can do a few
 * checks we won't have to do afterwards.
 *)

type 'a lifted = int * 'a

type lfconstr = constr lifted

let lift_lfconstr n (s,c) = (s+n,c)

(* For pretty-printing. We keep the aliases. The ouput is not a well typed
 * term: in patterns, constructors are not applied to their args.
 *)
(*
let rec pconstr_of_pat = function
    PatVar (_,Name id) -> VAR id
  | PatVar _,Anonymous -> VAR (id_of_string "_")
  | PatCstr (_,c,args) -> applist(c, List.map pconstr_of_pat args)
  | PatAs (_,id,p) -> DOPN(XTRA("AS",[]),[|VAR id; pconstr_of_pat p|])
;;
*)

(* Partial check on patterns *)
let rec check_pat_arity c =
  match c with
    PatCstr (loc, ((_,i),_ as c), args) ->
      let ity = mutind_of_constructor c in
      let nparams = mis_nparams (mind_specif_of_mind ity) in
      let tyconstr = type_mconstruct mtevd i ity in
      let nb_args_constr = (nb_prod tyconstr) - nparams in
	if List.length args <> nb_args_constr
        then errorlabstrm "check_pat_arity"
          (mssg_wrong_num_arg_in_constr c nb_args_constr)
  | PatAs (_,_,p) -> check_pat_arity p
  | PatVar (_,_) -> ()
;;

(* renaming different occurrences of _ in pattern (before checking linearity!)
 *)
(*
let rec rename_patt acc patt =
  match patt with
    PatVar x ->
      if starts_with_underscore x
      then let nid = next_ident_away x acc in (nid::acc, PatVar nid)
      else (acc, patt)
  | PatCstr(c,args) ->
      let (nacc,nargs) = rename_lpatt acc args in
      (nacc,PatCstr(c,nargs))
  | PatAs(id,p) ->
      let (nacc,np) = rename_patt acc p in
      (nacc,PatAs(id,np))

and rename_lpatt vl lp =
  List.fold_right
    (fun patt (acc,nlpatt) ->
      let (nacc,np) = rename_patt acc patt in (nacc, np::nlpatt))
    lp
    (vl,[])
;;
*)

(* Usage of this function should be avoided, because it requires that the
 * params are infered.
 *)
let rec constr_of_pat = function
    PatVar (_,Name id) -> VAR id
  | PatVar (_,Anonymous) -> invalid_arg "constr_of_pat"
  | PatCstr(_,c,args) ->
      let ity = mutind_of_constructor c in
      let mispec = mind_specif_of_mind ity in 
      let nparams = mis_nparams mispec in
      let c = mutconstruct_of_constructor c in
      applist(c, makelist nparams mkExistential @ List.map constr_of_pat args)
  | PatAs(_,id,p) -> constr_of_pat p
;;


(* == Error messages == *)

let mssg_ill_typed_branch (innermsg) =
 errorlabstrm "compile_multcase" 
   [<'sTR "Expansion strategy failed to build a well typed case expression.";
     'cUT; 'sTR "There is a branch that mistmatches the expected type."; 'fNL;
     hOV 1 [<'sTR "The risen type error on the result of expansion was:";
             'sPC; innermsg >]
   >];;

let mssg_wrong_predicate_arity env pred nondep_arity dep_arity=
  let pp = pTERMINENV(env,pred) in
    [<'sTR "The elimination predicate " ; pp; 'cUT;
      'sTR "should be of arity " ; 'iNT nondep_arity ; 
      'sTR " (for non dependent case)  or " ;
      'iNT dep_arity ; 'sTR " (for dependent case).">]
;;


let warning_needs_dep_elim() =
  warning
"This pattern matching may need dependent elimination to be compiled.
I will try, but if fails try again giving dependent elimination predicate."
;;

let mssg_needs_inversion x t env =
  let px = pTERMINENV(env,x) in
  let pt = pTERMINENV(env,t) in
    [< 'sTR "Sorry, I need inversion to compile pattern matching of term ";
       px ; 'sTR " of type: "; pt>]
;;

let mssg_may_need_inversion () =
  [< 'sTR "This pattern-matching is not exhaustive.">]
;;

let mssg_mistmatch_type patt ity env =
  let pi = pTERMINENV(env,ity) in
  let pp = pTERMINENV(env,patt) in
    [< 'sTR "Constructor pattern: "; pp; 'bRK(1,1); 
       'sTR " cannot match values of type "; pi >]
;;


(* == Errors concerning mlcase == *)

let mssg_mlcase_infer_failure c env  =
  let pc = pTERMINENV(env,c) in
    (hOV 3 [<'sTR "Cannot infer type of expression :";'wS 1; pc>])
;;

let mssg_mlcase_not_inductive c env =
  let pc = pTERMINENV(env,c) in
    (hOV 3 [<'sTR "ML Case on a non inductive type :";'wS 1; pc>])
;;


(* eta-expands the term t *)

let rec eta_expand0 sigma n c t =
  match whd_betadeltaiota sigma t with
      DOP2(Prod,a,DLAM(na,b)) ->
	DOP2(Lambda,a,DLAM(na,eta_expand0 sigma (n+1) c b))
   | _ -> applist (lift n c, rel_list 0 n)
;;

let rec eta_expand sigma c t =
  match whd_betadeltaiota sigma c, whd_betadeltaiota sigma t with
   | (DOP2(Lambda,ta,DLAM(na,cb)), DOP2(Prod,_,DLAM(_,tb))) ->
       DOP2(Lambda,ta,DLAM(na,eta_expand sigma cb tb))
   | (c, t) -> eta_expand0 sigma 0 c t
;;

let eta_reduce_if_rel c =
  match eta_reduce_head c with
      Rel n -> Rel n
    | _ -> c;;

(* ===================================== *)
(*        DATA STRUCTURES                *)
(* ===================================== *)
let push a s = a::s;;
let push_lifted a s = (insert_lifted a)::s;;
let pop = function (a::s) -> (a,s) | _ -> error "pop";;
let empty = function [] -> true | _ -> false;;
let top = function (a::s) -> a | _ -> error "pop";;

(* Check *)
type 'a check = {past:'a list; 
                 future:'a list};;


let empty_ck: 'a check = {past=[]; future=[]};;

let to_past {past=p;future=f} = 
  if not (empty f) 
   then let (a,r)=pop f in  {past=push a p; future=r}
   else   error "move_left:right is empty"
;;


(* dependencies: terms on which the type of patterns depends
   patterns: list of patterns to analyse
   rhs: right hand side of equations
   Current pattern to analyse is placed in the top of patterns.future 
*)

type rhs =
    {private_ids:identifier list;
     user_ids:identifier list;
     subst:(identifier * constr) list;
     rhs_lift:int;
     it:rawconstr}

type row = {dependencies : constr lifted list; 
            patterns     : pattern check; 
            rhs          : rhs};;


let row_current r = top r.patterns.future;;
let pop_row_current ck = {past= ck.past; future= snd (pop ck.future)};;


(*---------------------------------------------------------------*
 *          Code for expansion of Cases macros                   *
 *---------------------------------------------------------------*)


(* == functions for replacing variables except in patterns == *)
(* (replace_var id t c) replaces for t all those occurrences of (VAR id) in c
 * that are not in patterns. It lifts t across binders.
 * The restriction is to avoid restoring parameters in patterns while treating
 * rhs.
 *)
(* PB: (replace_var_nolhs (VAR x) T <<Cases y of (C x) => x end>>)
 * will return <<Cases y of (C x) => T end>>, which is wrong!
 *)
(*
let replace_var_nolhs var t x = 
 let rec substrec n = function
     (VAR(x)  as c)    -> if c=var then lift n t else c
   | DOPN(XTRA("EQN",cl),v) -> DOPN(XTRA("EQN",cl),Array.concat 
                                  [[|substrec n v.(0)|]; tl_vect v]) 
   | DOPN(oper,cl)    -> DOPN(oper,Array.map (substrec n) cl)
   | DOPL(oper,cl)    -> DOPL(oper,List.map (substrec n) cl)
   | DOP1(oper,c)     -> DOP1(oper,substrec n c)
   | DOP2(oper,c1,c2) -> DOP2(oper,substrec n c1,substrec n c2)
   | DLAM(na,c)       -> DLAM(na,substrec (n+1) c)
   | DLAMV(na,v)      -> DLAMV(na,Array.map (substrec (n+1)) v)
   | x                -> x in
 if eq_constr var t then x
 else substrec 0 x
;;
*)
(* Version sur les pseudo-termes... comprendre d'abord s'il y a encore
besoin d'absolutize... *)
let lift_rawconstr n =
  let rec lift k = function
    | RRef (loc,RRel i) as x -> if i>k then RRef(loc,RRel(i+n)) else x
    | RApp (loc,f,args) -> RApp (loc,lift k f,List.map (lift k) args)
    | RBinder (loc,bk,na,ty,c) -> RBinder (loc,bk,na,lift k ty, lift (k+1) c)
    | RCases (loc,tyopt,tml,pl) -> 
	RCases (loc,lift_option k tyopt,List.map (lift k) tml,
		List.map (lift_pattern k) pl)
    | ROldCase (loc,b,tyopt,tm,bv) -> 
	ROldCase (loc,b,lift_option k tyopt,lift k tm,Array.map (lift k) bv)
    | RRec (loc,fk,idl,tyl,bv) ->
	let m = Array.length idl in
	RRec (loc,fk,idl,Array.map (lift k) tyl, Array.map (lift (k+m)) bv)
    | (RSort _ | RHole _ | RRef _ ) as x -> x

  and lift_pattern k = function (idl,p,c) -> (idl,p,lift k c)

  and lift_option k = function None -> None | Some p -> Some (lift k p)

  in lift 0
;;
(* *)
let replace_var_nolhs var t =
  let rec reprec k = function
    | RRef (loc,Var id) as c -> if id=var then lift_rawconstr k t else c
    | RApp (loc,f,args) -> RApp (loc,reprec k f,List.map (reprec k) args)
    | RBinder (loc,bk,n,ty,c) -> RBinder (loc,bk,n,reprec k ty, reprec (k+1) c)
    | RCases (loc,tyopt,tml,pl) -> 
	RCases (loc,reprec_option k tyopt,List.map (reprec k) tml,
		List.map (reprec_pattern k) pl)
    | ROldCase (loc,b,tyopt,tm,bv) -> 
	ROldCase (loc,b,reprec_option k tyopt, reprec k tm,
		  Array.map (reprec k) bv)
    | RRec (loc,fk,idl,tyl,bv) ->
	let m = Array.length idl in
	RRec (loc,fk,idl,Array.map (reprec k) tyl, Array.map (reprec (k+m)) bv)
    | (RSort _ | RHole _ | RRef _ ) as x -> x

  and reprec_pattern k = function (idl,p,c) -> (idl,p,reprec k c)

  and reprec_option k = function None -> None | Some p -> Some (reprec k p)

  in reprec 0
;;

let subst_in_subst id t (id2,c) =
   (id2,replace_vars [(id,make_substituend t)] c)

let replace_var_nolhs id t rhs =
  if List.mem id rhs.private_ids then
    {rhs with
	 subst = List.map (subst_in_subst id t) rhs.subst;
         private_ids = except id rhs.private_ids}
  else if List.mem id rhs.user_ids then
  {rhs with 
       subst = (id,t)::List.map (subst_in_subst id t) rhs.subst;
       user_ids = except id rhs.user_ids}
  else anomaly "Found a pattern variables neither private nor user supplied"
;;



  


(* replaces occurrences of [(VAR id1)..(VAR idn)] respectively by t  in c *)
let replace_lvar_nolhs lid t c =
  List.fold_right (fun var c -> replace_var_nolhs var t c) lid c
;;

let global_vars_rawconstr =
  let rec global lid = function
    | RRef (loc,Var id) -> id::lid
    | RApp (loc,f,args) -> List.fold_left global (global lid f) args
    | RBinder (loc,bk,na,ty,c) -> global (global lid ty) c
    | RCases (loc,tyopt,tml,pl) -> 
	global_option (List.fold_left global
			 (List.fold_left global_pattern lid pl) tml) tyopt
    | ROldCase (loc,b,tyopt,tm,bv) ->
	global_option (global (it_vect global lid bv) tm) tyopt
    | RRec (loc,fk,_,tyl,bv) ->
	it_vect global (it_vect global lid tyl) bv
    | (RSort _ | RHole _ | RRef _ ) -> []

  and global_pattern lid = function (idl,p,c) -> global lid c

  and global_option lid = function None -> [] | Some p -> global lid p

  in global []
;;

let rec global_vars_rawconstr env rhs =
  rhs.user_ids@(ids_of_sign (get_globals env))

(* ====================================================== *)
(* Functions to absolutize alias names of as-patterns in  *)
(*  a term                                                *)
(* ====================================================== *)
let rec whd_as = function
   PatAs(_,_,p) -> whd_as p
 | x -> x
;;

(* Rem: avant, lid étant dans l'autre sens, et replace_lvar_nolhs
   utilise un fold_right. Comme je ne vois aucune dépendance entre des
   différentes vars dans le terme value à substituer, l'ordre devrait
   être indifférent [HH] *)

let rec replace_alias and_hdname lid value rhs = function
    PatVar (_,Name id) ->
      let lid' = if and_hdname then id::lid else lid in
      replace_lvar_nolhs lid' value rhs
  | PatVar (_,Anonymous) -> replace_lvar_nolhs lid value rhs
  | PatAs (_,id,p) as patt -> replace_alias and_hdname (id::lid) value rhs p
 |  _ -> anomalylabstrm "absolutize_alias"
                  [<'sTR "pattern should be a variable or an as-pattern">]
;;

(* (expand_alias_and_hdname t rhs patt =
 *   if patt=(VAR id)  then  rhs[(VAR id) <- t]
 *   if patt = (p as id) then  (expand p t rhs)[(VAR id)<-t]
 *)  
let absolutize_alias_and_hdname = replace_alias true [];;

(* (absolutize_alias t rhs patt =
 *   if patt = (p as id) then  (expand p t rhs)[(VAR id)<-t] else rhs
 *)
let absolutize_alias = replace_alias false [];;
 
let pop_and_prepend_future lpatt chk =
  let (_,fut) = pop chk.future in {past=chk.past; future= lpatt @ fut}
;;

type matrix = row list ;;

(* info_flow allos to tag "tomatch-patterns" during expansion:
 * INH means that tomatch-pattern is given by the user
 * SYNT means that tomatch-pattern arises from destructuring a constructor
 *      (i.e. comes during top-down analysis of patterns)
 * INH_FIRST is used ONLY during dependent-Cases compilation. it tags the 
 *           first tomatch-pattern
 *)
type info_flow = INH | SYNT | INH_FIRST;;



(* If the case is non-dependent, the algorithm of compilation generates 
   the predicate P of the analysis using la 0eme definition. When 
   the case is dependent it should use the same strategy than rec.
   For that terms to match are tagged with INH or SYNT so decide 
   if pred should be inherited to branches or synthetised. 
   While left to right analysis
   of patterns the predicate is inherited, while top-down analysis of
   patterns predicate is synthetised, by doing anonymous abstractions when
   the non-dependent case is applied to an object of dependent type.
*)

type tomatch = IsInd of constr * mutind | MayBeNotInd of constr * constr

let to_mutind c sigma t =
  try IsInd (c,try_mutind_of sigma t)
  with Induc -> MayBeNotInd (c,t)

let term_tomatch = function
    IsInd (c,_) -> c
  | MayBeNotInd (c,_) -> c;;

type general_data =
    {case_dep : bool;
     pred     : constr lifted;
     deptm    : constr lifted list; 
     tomatch  : (tomatch * info_flow) list;
     mat      : matrix };;

type compilation_state = environment * general_data * constr list

let gd_current gd = top gd.tomatch;;
let pop_current gd = snd (pop gd.tomatch);;

let replace_gd_current cur gd =
let tm = pop_current gd 
in  {case_dep = gd.case_dep; pred=gd.pred; deptm=gd.deptm;
    tomatch = cur:: tm; mat = gd.mat}
;;

let replace_gd_pred pred gd = 
 {case_dep = gd.case_dep; 
  pred     = insert_lifted pred; 
  deptm    = gd.deptm;
  tomatch  = gd.tomatch;
  mat      = gd.mat}
;;


let prepend_tomatch ltm gd =
 {case_dep = gd.case_dep; pred=gd.pred; deptm=gd.deptm;
  tomatch = ltm@ gd.tomatch; mat = gd.mat}
;;

let pop_and_prepend_tomatch ltm gd =
let _,tm= pop  gd.tomatch  
in {case_dep= gd.case_dep; pred= gd.pred;   deptm = gd.deptm;
    tomatch = ltm@tm;
    mat = gd.mat}
;;


(* ========================================== *)
(*    Lifiting operations for general data    *) 
(* ========================================== *)

(* == lifting db-indexes greater equal a base index in gd == *)
(*  Ops. lifting indexes under b bindings (i.e. we lift only db-indexes
 *  that are >=  b
 *)

(* lifts n the the indexes >= b of  row *)
let lift_row n r = 
 {dependencies = List.map (lift_lfconstr n) r.dependencies;
  patterns     = r.patterns; (* No Rel in patterns *)
  rhs          = {r.rhs with rhs_lift = r.rhs.rhs_lift + n}}
;;

let lift_ind_data n md =
  {fullmind=lift n md.fullmind;
   mind=md.mind;
   nparams=md.nparams;
   nconstr=md.nconstr;
   params=List.map (lift n) md.params;
   realargs=List.map (lift n) md.realargs;
   arity=md.arity}
;;

let lift_tomatch n = function
    IsInd(c,ind_data) -> IsInd (lift n c, lift_ind_data n ind_data)
  | MayBeNotInd (c,t) -> MayBeNotInd (lift n c,lift n t)
;;

let lift_gd n {case_dep=b; pred=p; deptm=l; tomatch=tm; mat=m} =
  {case_dep=b;
   pred    = lift_lfconstr n p;
   deptm   = List.map (lift_lfconstr n) l;
   tomatch = List.map (fun (tm,i) -> (lift_tomatch n tm,i)) tm;
   mat = List.map (lift_row n) m}
;;

(* == Ops lifting all db-indexes == *)

(* pushes (na,t) to dbenv (that is a stack of (name,constr)  and lifts
 * tomach's dependencies, tomatch, pred and rhs in matrix 
 *)

let push_and_liftn_gd n vl (env, gd) =
  (List.fold_right (Mach.push_rel mtevd) vl env,  lift_gd n gd)
;;

let push_and_lift_gd       v   = push_and_liftn_gd 1 [v]

(* if t not (x1:A1)(x2:A2)....(xn:An)t' then (push_and_lift_gdn n t (env,gd,l)
 * raises an error else it gives ([x1,A1 ; x2,A2 ; ... ; xn,An]@env,t',gd')
 * where gd' is gd lifted n steps and l' is l lifted n steps
 *)

let get_n_prod n t = 
  let rec pushrec l = function
      (0, t)                       -> (l,t)
    | (n, DOP2(Prod,t,DLAM(na,b))) -> pushrec ((na,t)::l) (n-1, b)
    | (n, DOP2(Cast,t,_))          -> pushrec l (n, t)
    | (_, _) -> error "get_n_prod: Not enough products"
 in pushrec [] (n,t)
;;

let push_and_lift_gdn n t envgd =
  let (vl,_) = get_n_prod n t in
  let (nenv,ngd) = push_and_liftn_gd n vl envgd in
    (nenv,ngd)
;;

let push_env_and_lift_gdn n dbenv_base dbenv gd a =
  let rec pushrec base gd dbenv n = 
    if n=0 then  base,gd
    else 
      try (match dbenv with 
	     (na, t):: x  ->
               let ndbenv,ngd = pushrec base gd x (n-1) in
		 push_and_lift_gd  (na,t) (ndbenv, ngd)
	     | _ -> assert false)
      with UserError _ -> error "push_env_and_lift_gd"
  in 
  let (nbase,ngd) = pushrec dbenv_base gd (get_rels dbenv)  n in
  (ngd,lift_lfconstr n a)
;;

(* == Ops. pushing  patterns to tomatch and lifting == *)

(* if t=(x1:P1)..(xn:Pn)Q behaves as push_and_lift_gd but if gd.patterns=patt 
 * then the resutling gd'.patterns = (Rel n)..(Rel 1)patt
 *)

let push_lpatt_and_liftl n t info (env,gd,l) =
  let rec pushrec tl = function
      (0, t, envgd) -> (tl,t,envgd)
    | (n, DOP2(Prod,t,DLAM(na,b)), envgd)
    -> pushrec (t::tl) (n-1, b, push_and_lift_gd (na,t) envgd)
    | (n, DOP2(Cast,t,_), envgd) -> pushrec tl (n, t, envgd)
    | (_, _, _) -> error "push_lpatt_and_liftl"
  in let tl,body,(nenv,ngd) = pushrec [] (n,t,(env,gd)) in
   let ntomatch =
     map_i
       (fun i t -> (to_mutind (Rel i) mtevd (lift n t), info)) 1 tl
   in body, (nenv,
	     {ngd with tomatch=rev_append ntomatch ngd.tomatch},
             List.map (lift n) l)
;;

(* =============================================================== *)


(* if tomatch=[Rel i1;...Rel in] of type 
   [(Ti1 p1_bar u1_bar);..(Tij pj_bar uj_bar)] then it yields
   [u1_bar;...uj_bar] 
*)
let find_depargs env tomatch =
  let dep = function
      (IsInd(c,{realargs=args}),_) -> args
    | (MayBeNotInd (_,_),_) -> []
  in map_append dep tomatch
;;

(* == to treat  ml-case == *)

let make_pre_mlcase c lf = 
  (DOPN(XTRA("MLCASE",[Ast.str "REC"]), Array.append [|c|] lf))
;;

let dummy_mark =  (DOP0(XTRA ("SYNTH", [])));;

let rec hd_of_prodlam = function
   DOP2(Prod,_,DLAM(_,c))   -> hd_of_prodlam c
 | DOP2(Lambda,t,DLAM(_,c)) -> hd_of_prodlam c
 | DOP2(Cast,c,t)     -> hd_of_prodlam t
 | c   -> c
;;

let is_for_mlcase p =  (hd_of_prodlam p)=dummy_mark;; 

let has_synth t = dependent dummy_mark t;;

let rec dummy_lam n t = 
  if n=0 then t
    else (DOP2(Lambda,dummy_mark ,DLAM(Anonymous, dummy_lam (n-1) t)))
;;


(* == Special functions to deal with mlcase on objects of dependent types == *)

(* ================================================= *)
(*   Exceptions and functions for Error messages     *)
(* ================================================= *)


(* (CCError "function", env, gd, mssg) whre mssg=(string,Pp.std_ppcmds)
 * is the inner risen error_mssg
 *)
exception CCError of 
 string * type_judgement assumptions * general_data * (rawconstr option) 
        * (string * Pp.std_ppcmds);;

(*
let mssg_build_leaf  errenv errgd errrhs innermssg =
  let s,pstream= innermssg in
  let rhs = 
    (match errrhs with (Some rhs) -> rhs | 
       None -> invalid_arg "mssg_build_leaf") in
  let prhs = pTERMINENV(errenv,rhs) in
  let ermsg =
    [< 'sTR "The term "; prhs; 'sTR " is not well typed."; 'fNL; 
       hOV 1 [<'sTR "The risen type error on the result of expansion was:";
               'sPC; pstream >] 
    >]
in (errorlabstrm s ermsg)
;;
*) 
(* Cela ne se justifie plus d'avoir une encapsulation du message *)
let mssg_build_leaf  errenv errgd errrhs innermssg =
  let s,pstream= innermssg in
   errorlabstrm s [<'sTR "Error in Cases:"; 'sPC; pstream >] 

(* == functions for syntactic correctness test of patterns == *)


let patt_are_var =
  List.for_all
    (fun r -> match (whd_as (row_current r)) with
      PatVar _ -> true
    |_ -> false)
;;

let check_pattern ity row =
  let rec check_rec = function
      PatVar (_,id) -> ()
    | PatCstr (loc,c,args) ->
        if mutind_of_ind ity <> mutind_of_constructor c then
	  Ast.user_err_loc 
	    (loc,"check_pattern",(mssg_hd_is_not_constructor c ity))
    | PatAs(_,_,p') -> check_rec p' 

  in check_rec (row_current row) 

let check_patt_are_correct ity mat = List.iter (check_pattern ity) mat 

(*The only variables that patterns can share with the environment are 
  parameters of inducive definitions!. Thus patterns should also be 
  lifted when pushing inthe context. *)


(* == functions to deal with names in contexts == *)

(* If cur=(Rel j) then 
 * if env = ENVIRON(sign,[na_h:Th]...[na_j:Tj]...[na_1:T1])
 * then it yields ENVIRON(sign,[na_h:Th]...[Name id:Tj]...[na_1:T1])
 *)
let change_name_rel env current id=
 match current with 
  (Rel j) -> 
    if starts_with_underscore id 
    then env 
    else let  ENVIRON(sign,db) = env in
     ( match chop_list (j-1) db with
	   db1,((_,ty)::db2) -> (ENVIRON(sign,db1@(Name id,ty)::db2))
	 | _ -> assert false)
 |  _  -> env
;;
 

(* == Function dealing with constraints in compilation of dep case == *)

let xtra_tm = DOP0(XTRA("TMPATT",[]));;
let is_xtra_tm tm = match tm with DOP0(XTRA("TMPATT",[])) -> true |_ -> false;;

(* represents the constraint cur=ci *)
let build_constraint cur ci = DOP2(XTRA("CONSTRAINT",[]),cur,ci);;

let top_constraint gd =
 match (extract_lifted gd.pred) with 
  DOP2(Prod,(DOP2(XTRA("CONSTRAINT",[]),cur,ci)),_) -> true 
 |   _ -> false
;;

let destruct_constraint gd =
 match (extract_lifted gd.pred) with 
  DOP2(Prod,(DOP2(XTRA("CONSTRAINT",[]),cur,ci)),bd) -> cur,ci,(lift (-1) bd)
 |   _ ->  anomalylabstrm "destruct_constraint" [<>]
;;

let rec whd_constraint = function
     DOP2(Prod,(DOP2(XTRA("CONSTRAINT",[]),_,_)),(DLAM(_,bd))) 
          -> whd_constraint (lift (-1) bd)
   | DOP2(Lambda,(DOP2(XTRA("CONSTRAINT",[]),_,_)),(DLAM(_,bd))) 
           -> whd_constraint (lift (-1) bd)
   | VAR(x)           -> (VAR x)
   | DOPN(oper,cl)    -> DOPN(oper,Array.map whd_constraint  cl)
   | DOPL(oper,cl)    -> DOPL(oper,List.map whd_constraint  cl)
   | DOP1(oper,c)     -> DOP1(oper,whd_constraint  c)
   | DOP2(oper,c1,c2) -> DOP2(oper,whd_constraint c1,whd_constraint c2)
   | DLAM(na,c)       -> DLAM(na,whd_constraint  c)
   | DLAMV(na,v)      -> DLAMV(na,Array.map whd_constraint  v)
   | x                -> x
;;

(* if next_pred = [d_bar:D_bar][h:(I~d_bar)]Q 
 * and bty = (y_bar:S_bar)(I~dep_ci)
 * and ci_params = (ci p_bar)
 * then it builds the next predicate containing the constraints in the correct
 * environment:
 * (y_bar:S_bar)
 *   (XTRA cur=(ci_param y_bar))->(next_pred dep_ci (ci_param dep_ci))
 *) 

(* PRE: gd.pred is a product correspondent to dependent elimination preidcate
 * productized (i.e. (d_bar:D_bar)(y:(I d_bar))Q )
 * It returns a product of the form
 * (s_bar:S_bar)Constraint->(whd_beta ([d_bar:D_bar][y:(I d_bar)]Q  dep_ci ci))
 * if info=INH then any constraints are generated
 *)
let  insert_constraint next_env gd brty ((cur,info), ci_param) = 
  let k = nb_prod brty in
  let dbenv0,body = decompose_prod_n k brty in
  let cur0 = lift k cur in
  let cip0 = lift k ci_param in
  let npred0 = lift k (extract_lifted gd.pred) in
  let dep_ci = args_app body in
  let cip1 = applist (cip0,(rel_list 0 k)) in 

  let npred1 = to_lambda (Array.length dep_ci) npred0 in  

  let ndbenv,bodypred,nk =
    if Array.length dep_ci=1 (* type of cur is non-dependent *)  then 
      dbenv0, appvect (npred1, dep_ci),k 
    else   
      let app_pred = appvect (npred1, dep_ci) in
      if info = SYNT then  
       	let c = build_constraint cur0 cip1 in
       	(Anonymous,c)::dbenv0, (lift 1 app_pred), (k+1)

      else dbenv0,app_pred,k  (* we avoid generating the constraint*) in 
 
 (* we productize the constraint if some has been generated *)
  prodn nk ndbenv (whd_beta bodypred)
;;


(********************************)
(*  == compilation functions == *)
(********************************)

(* nbargs_iconstr is the number of arguments of the constructor i that are not
 * parameters. Current is the current value to substitute  "as" binders in
 * as-patterns 
 * About Expansion of as patterns: 
 * we absolutize alias names (x1..xn) in pattern in rhs by 
 * rhs [x1..xn <- gd.current]  if the type of current is not dep.
 * rhs [x1..xn <- (ci params lid)] otherwise
 * (in first case we share in second we rebuild the term)
 * Note: in the case of (VAR id) we use sharing whenver the type is non-dep
 * or we reconstruct the term when its dependent.
 * depcase tells if the current Case  to compile is dependent or not (this is
 * because during dependent compilation terms are always reconstructed and not
 * shared)
 * TODO: find a better criterion, or let the user choose...
 *)
let submat depcase sigma env i ind_data params current mat =
  let ity = mutind_of_ind ind_data.mind in
  let k = List.length params in
  let ci = ith_constructor i ind_data in
  let nbargs_iconstr = nb_prod (type_mconstruct sigma i ity) - k in

  let expand_row r =
    let build_new_row subpatts vars =
      let lid = global_vars_rawconstr env r.rhs in
      let new_ids = get_new_ids nbargs_iconstr (id_of_string "t") lid in
      let lpatt,largs = 
	match subpatts with
	  | None ->
	      List.map (fun id -> PatVar (Ast.dummy_loc,Name id)) new_ids,
	      List.map (fun id -> VAR id) new_ids
	  | Some patts ->
	      List.map2
		(fun id pat -> PatAs (Ast.dummy_loc,id,pat)) new_ids patts,
              List.map constr_of_pat patts in
      let value =
	if (is_predicate ind_data) or depcase
	then applist (ci, params@largs)
        else current in
      { dependencies=r.dependencies;
        patterns = pop_and_prepend_future lpatt r.patterns;
        rhs = replace_lvar_nolhs vars value r.rhs } in

    (* C'est idiot de permettre plusieurs alias pour un même motif *)
    let rec expandrec envopt aliasvar = function
      | PatVar (_,name) ->
	  let vars = match name with Name id -> id ::aliasvar |_ -> aliasvar in
	  (envopt, [build_new_row None vars])
      | PatCstr(_,c,largs) when mutconstruct_of_constructor c = ci ->
	(* Avant: il y aurait eu un problème si un des largs contenait
   	   un "_". Un problème aussi pour inférer les params des
   	   constructeurs sous-jacents, car on n'avait pas accès ici
   	   aux types des sous-patterns. Ai donc remplacé le
   	   "applist(c, params @ (List.map constr_of_pat largs))" par
   	   un "applist (ci, params@(List.map (fun id -> VAR id) new_ids))"
	   comme dans le cas PatVar, mais en créant des alias pour les
	   sous-patterns. Au passage, ça uniformise le traitement maintenant
	   fait par "build_new_row" *)
	    (envopt,[build_new_row (Some largs) aliasvar])
      | PatCstr _ -> (None,[])
      | PatAs(_,id1,patt) ->
	  let nenvopt = match envopt with 
	    | None -> Some (change_name_rel env current id1)
	    | Some _ -> envopt in
	  expandrec nenvopt (id1::aliasvar) patt in

    expandrec None [] (row_current r) in

  let lenv,llrows = List.split (List.map expand_row mat) in
  let lrows = List.concat llrows in
  let lsome= filter (fun op -> op <> None) lenv in
  let rnenv = 
    if lsome = [] then env 
    else outSOME (List.hd lsome)
  in  rnenv, lrows
;;


type status =
  | Match_Current of (constr * mutind * info_flow) (* "(", ")" needed... *)
  | Any_Tomatch | All_Variables
  | Any_Tomatch_Dep | All_Variables_Dep | Solve_Constraint ;;

let not_of_empty_type = function
  | IsInd (c,{nconstr=nconstr}),_ -> nconstr <> 0
  | MayBeNotInd (_,t),_ -> true  
  (* Ici, on pourrait tester si t=?n et si oui unifier avec False ?? *)
;;
  
let gdstatus env gd =
  if top_constraint gd  then Solve_Constraint
  else
    match gd.tomatch with
     [] -> if gd.case_dep then Any_Tomatch_Dep else Any_Tomatch
  | (cj,info)::tl_tm ->
   if gd.mat=[] then
     if (List.for_all not_of_empty_type gd.tomatch)
     then errorlabstrm "gdstatus" 
       [< 'sTR "One should match a term in an empty inductive type"; 'fNL;
	  'sTR "to get an empty list of pattern" >]
     else (* to treat empty types *)
       match cj with
	   IsInd (current,ind_data) -> Match_Current (current,ind_data,info)
	 | MayBeNotInd (current,t)  -> 
	     if gd.case_dep then  All_Variables_Dep else  All_Variables
   else
     if (patt_are_var gd.mat)
     then  if gd.case_dep then  All_Variables_Dep else  All_Variables
     else
       match cj with
	   IsInd (current,ind_data) -> 
	     if is_xtra_tm current then  Match_Current (current,ind_data,info)
	     else
	       (check_patt_are_correct ind_data.mind gd.mat;
		Match_Current (current,ind_data,info))
	 | MayBeNotInd (current,t) ->
	     errorlabstrm "gdstatus" (error_case_not_inductive CCI env current t)
;;


(* If S is the type of x and I that of y, then
 * solve_dep (x,S)(y,I) =
 * if S=(I u1..uj..un) and T=(I w1..wj..wn) where I has j parameters then
 *     u1=w1 &...& uj=wj & (solve u_j+1 w_j+1)& ..& (solve u_j+n w_j+n)
 *  else if S=(Rel i) and T=(Rel j) 
 *       else fail!
 * Note: this succeds only if uj+1...ur are all variables, otherwise 
 * inversion is needed.
 * WARNING!: here we compare using whd_cast is this enough or should we
 *  erase all cast before comparing??
 *)  
let  rec solve_dep sigma env (x,t) (y,s)  =
  let rec solve_args  = function
      [],[] -> []
    | (e1::l1), (e2::l2) ->
     	let e = whd_cast e1 in 
      	(match e with
          (Rel i) -> ((Rel i), e2)::(solve_args (l1,l2))
        | _ ->
	    if  e1= whd_cast e2 then (solve_args (l1,l2)) 
            else errorlabstrm "solve_dep" (mssg_needs_inversion  x t env))
    | _ -> anomaly  "solve_dep"  in
  try  
    let (ityt,argst)= find_mrectype sigma  t
    and (itys,argss)= find_mrectype sigma (hd_of_prod s)  in
    if whd_cast ityt= whd_cast itys & (List.length argst = List.length argss)
    then 
      let nparams = mind_nparams ityt in
      let (paramt,largst) = chop_list nparams argst
      and (params,largss) = chop_list nparams argss in
      if for_all2 eq_constr paramt params 
      then  solve_args  (largst,largss) 
      else anomalylabstrm "solve_dep" 
          [<'sTR "mistake in the code building the branch!!" >]
    else anomalylabstrm "solve_dep" 
        [<'sTR "mistake in the code building the branch (pb:parameters)!">]
  with Induc -> anomalylabstrm "solve_dep" 
      [<'sTR "mistake in the code building the branch (pb: constructor)!">]
;; 

let apply_subst subst dep =
  let rec subst_term subst c = 
    match subst with 
      [] -> c
    | (Rel i, t)::s -> 
        if dependent (Rel i) c then
          if i = 1 then subst1 t c  
          else
	    let lsubstituend =
	      (List.rev (Array.to_list (rel_vect 0 (i-1))))@[t]
            in  subst_term s (substl lsubstituend  c)
        else  subst_term s c 
    | _ -> assert false   in
  let extr_subst_ins c =  insert_lifted (subst_term subst (extract_lifted c)) 
  in   List.map extr_subst_ins dep 
;;


let solve_dependencies sigma env gd (current,ci)=
  if gd.deptm = [] then gd.deptm
  else
    let (curv,curt) = destCast current in
    let (civ,cit) = destCast current in
    try
      let subst= solve_dep sigma env (curv,curt) (civ,cit) 
      in apply_subst subst  gd.deptm
    with UserError(a,b)-> errorlabstrm "solve_dependencies" b
;;


let rec substitute_dependencies c = function 
    [], [] -> c
  | (t::x), (var::y) -> 
      (match (extract_lifted var) with
	   (VAR id) as v  ->
	     substitute_dependencies
	       (replace_vars [(id,make_substituend (extract_lifted t))] c)
	       (x,y)
  	 | _ -> anomalylabstrm "substitute_dependencies" [<>] )
  | _,_ -> anomalylabstrm "substitute_dependencies" 
        [< 'sTR "Dep. tomatch mistmatch dependencies of patterns" >]
;;


(* depends .. env cur tm = true if the the type of some element of tm
 * depends on cur and false otherwise
 *) 
(* I think that cur<>(Rel n) only during the first application of cc 
 * because later constructors in gd.tomatch are applied to variables
 *)
let depends env cur tm =
  let ENVIRON(sign,dbenv) = env  in
  match cur with
    (Rel n) ->
      let (gamma2,_)= chop_list (n-1) dbenv in
      let _,abs,_ = lam_and_popl (n-1) gamma2 mkImplicit []
      in dependent (Rel 1) abs 
  | _ -> false
;;


let lift_ctxt  k env =
  let ENVIRON(sign,dbenv) = env  in
  let delta,_ = decompose_prod (lift k (prod_it mkImplicit dbenv)) in
  ENVIRON(sign,delta)
;;


let split_ctxt j (ENVIRON(sign,db)) =
  let db1,db2= chop_list j db in
  (ENVIRON(sign,db1)), (ENVIRON(sign,db2))
;;

let prepend_db_ctxt (ENVIRON(sign1,db1)) (ENVIRON(sign2,db2)) =  
  ENVIRON(sign1, db1@db2)
;;


 
(* substitute_ctxt ci ENVIRON(sign, ([n1:U1]..[nj:Uj]))i = 
 *  substitutes ci by (Rel 1) in U1...Uj
 *)
let subst1_ctxt  ci env =
  let ENVIRON(sign,dbenv) = env  in
  let delta,_ = decompose_prod (subst1 ci (prod_it mkImplicit dbenv)) in
    ENVIRON(sign,delta)
;;

(* yields env if current pattern of first row is not a dummy var,
 * otherwise it undumize its identifier and renames the variable cur 
 * in context with the name of the current of the
 * first row.
 *)
let rename_cur_ctxt env cur gd =
  if gd.mat =[] then env
  else
    let r = List.hd gd.mat in
    let current = row_current r in
    match current with
      PatVar (_,Name id) when not (starts_with_underscore id) ->
 	change_name_rel env cur id
    | _ -> env
;;

(* supposes that if |env|=n then the prefix of branch_env coincides with env
 * except for the name of db variables
 *)
let common_prefix_ctxt env branch_env =
  let (ENVIRON(sign,db))=env in
  let (ENVIRON(_,branch_db)) = branch_env in 
  let j = List.length db in
  let rndb,_= chop_list j (List.rev branch_db)
  in (ENVIRON(sign, List.rev  rndb))
;;

let nf_ise_dependent sigma c t = dependent c (nf_ise1 sigma t)

let tm_depends current sigma ltm =
  let rec dep_rec = function 
      [] -> false
    | (IsInd(tm,{params=params;realargs=args}),_)::ltm -> 
	 List.exists (nf_ise_dependent sigma current) params
	 or List.exists (nf_ise_dependent sigma current) args
	 or (dep_rec ltm)
    | (MayBeNotInd (tm,t),_)::ltm -> 
	nf_ise_dependent sigma current t or (dep_rec ltm)
  in dep_rec ltm
;;



(* substitutes the current of the row by t in rhs. If the current of the row 
 * is an as-pattern, (p AS id) then it   expands recursively al as in such
 * patern by by  (expand rhs p)[id<- t]
 *)
(* t is the current tomatch (used for expanding as-patterns) *)
let subst_current value r =
  let cur = row_current r in
  let nrhs = absolutize_alias_and_hdname value r.rhs cur 
  in   {dependencies = r.dependencies;
	 patterns = pop_row_current r.patterns;
	 rhs = nrhs} 
;;

(* t is the current tomatch (used for expanding as-patterns) *)
let shift_current_to_dep  r  =
  let curpatt = row_current r in
  let value = constr_of_pat (whd_as curpatt) in 
  {dependencies = push (insert_lifted value) r.dependencies;
   patterns = pop_row_current r.patterns;
   rhs = absolutize_alias value r.rhs curpatt}
;;


(* =========================================================================
 * the following functions determine the context of dependencies of a 
 * a vector of terms. They are useful to build abstractions wrt to dependencies
 * =========================================================================*)
(* the type of c is (T p1..pn u1..um) (s.t. p1..pn are parameters of T
 *  and T:(x1:P1)...(xn:Pn)(y1:B1)..(ym:Bm)s) then
 *  [push_params env (c,(p1..pn,u1..um),_,_,_)] = 
 *     (env@[B1;..;Bm;(T (lift m p1)..(lift m pn) (Rel m)..(Rel 1))], 
 *      [u1;..um; c])
 *  in order to build later [y1:B1]..[ym:Bm](T p1'..pm' y1..ym)
 *  (where pi' = lift m pi)
 *)

let push_params sigma env (c,ind_data,_) =
  let {mind=ity;params=params;
       realargs=args;nparams=nparams;arity=arity}= ind_data in
  let lam_arity = to_lambda nparams arity in
  let arity0 = whd_beta (applist (lam_arity, params)) in
  let env0,s = splay_prod mtevd (* to castify here *) arity0 in
  let env0' = List.map (fun (na,t) -> (na,make_type t (Mach.sort_of sigma env t))) env0 in
  let m = nb_prod arity0  in
  let params0 = List.map (lift m) params in
  let args0 = rel_list 0 m in
  let t = make_type (applist (mutind_of_ind ity, params0@args0)) (destSort s) in
  let env1 = (Anonymous,t)::env0' in
  let dbenv0 =
    List.map (fun (na,t) -> Environ.named_hd (body_of_type t) na,t) env1 in
  let nind_data = {ind_data with params=params0;realargs=args0}
  in (List.fold_right add_rel dbenv0 env, nind_data, args@[c]);;


(* the type of current is (T p1..pn u1..um) (s.t. p1..pn are parameters of T
 *  and T:(x1:P1)...(xn:Pn)(y1:B1)..(ym:Bm)s) then
 * (tyenv_of_term tj) = [B1;..;Bm]
 *  in order to build later [y1:B1]..[ym:Bm]someterm
 *)

let abstract_arity res = function
    IsInd (current,{params=params;nparams=nparams;arity=arity}) ->
      let lam_arity = to_lambda nparams arity in 
      let arity0 = whd_beta (applist (lam_arity, params)) in
      let env0,_ = splay_prod mtevd arity0 in
      let k = List.length env0 in
	k, lamn k env0 (lift k res)
  | MayBeNotInd (_,_) -> 0,res
;;


(* =============================================== *)
(*   for mlcase                                    *)
(* =============================================== *)
(*
let rec abst = function
    [] -> dummy_mark
 | (tj::ltm) -> 
     let res = abst ltm in
     let envty = tyenv_of_term tj in
     let _,nres,_ = lam_and_popl (List.length envty) envty res []
     in nres

in abst ltmj
;;
*)

(* if ltmj=[j1;...jn] then this builds the abstraction
 *  [d1_bar:D1_bar] ...[dn_bar:Dn_bar](lift m pred)
 *  where di_bar are the dependencies of the type ji._TYPE and m is the sum
 *  of the lengths of d1_bar ... d1_n. 
 * The abstractions are not binding, because the predicate is properly lift
 *) 
let abstract_pred_lterms (pred,ltm) =
  let rec abst = function
      [] -> pred
    | (tj::ltm) -> snd (abstract_arity (abst ltm) tj)
  in abst ltm;;

let info_abstract_pred_lterms (pred,ltm) =
  let rec abst linfo = function
      [] -> linfo,pred
    | (tj::ltm) -> 
     	let linfo,res = abst linfo ltm in
     	let k,nres = abstract_arity res tj in
     	let info = if k=0 then SYNT else INH
     	in (info::linfo),nres
  in abst [] ltm;;


(* if the type of cur is : (I p_bar d_bar) where d_bar are d_bar are 
 * dependencies, then this function builds (pred d_bar)
 * Precondition: pred has at least the same number of abstractions as d_bars 
 * length
 *)  
let apply_to_dep env pred = function
  IsInd (c,ind_data) ->
    let {realargs=args} = ind_data in
    let k = nb_localargs ind_data in
      if k=0 then pred
      else
	let tyargs = args@[c] in
	let (ldep,_) = chop_list k tyargs
	in whd_beta (applist (pred, ldep))
  | MayBeNotInd (c,t) -> pred
;;

(* if dummy_pred = [x1:Implicit]..[xk:Implicit]...[xk+j:Implicit]P 
 * and ipred = [y1:T1]..[yk:Tk]T
 * the result is [y1:T1]..[yk:Tk][xk+1:Implicit]...[xk+j:Implicit](lift j T)

 *** CADUC ? ***
let replace_dummy_abstractions dummy_pred ipred =
  let k = nb_lam ipred in
  let j = (nb_lam dummy_pred) - k in 
  let (env,body) = decompose_lam ipred in
  let (_,ndpred,_) = push_and_liftl k [] dummy_pred [] in
  let dummy_env = decompose_lam ndpred in
    lam_it env (lam_it dummy_env (lift j body));;
 *)

(* ==   == *)



(* analogue strategy as Christine's MLCASE *)
let find_implicit_pred sigma ith_branch_builder env (current,ind_data,_) =
  let {fullmind=ct;nconstr=nconstr} = ind_data in
  let isrec = false in 
  let rec findtype i = 
    if i > nconstr then 
      errorlabstrm "find_implicit_pred"
 	(mssg_mlcase_infer_failure (Rel 80) env)
    else 
      try
 	(let expti = Indrec.branch_scheme sigma isrec i ct in
       	let _,bri= ith_branch_builder i  in
       	let fi = bri._TYPE in 
       	let efit = nf_ise1 sigma fi in 
       	let pred =
          pred_case_ml_onebranch env sigma isrec 
            (current,ct) (i,bri._VAL,efit) in
 	if has_ise pred or (has_synth pred) then error"isevar" else pred)
      with UserError _ -> findtype (i+1)   in
  try  findtype 1  
  with Induc ->
    error "find_implicit_pred" (mssg_mlcase_not_inductive (Rel 80) env) 
;;

(* =============================================== *)
(* Strategies for building elimination predicates  *)
(* =============================================== *)
(* we build new predicate p for elimination  
 * by 0-splitting (we use inheritance or synthesis) 
 *)
let build_nondep_predicate  env (current,ind_data,_) gd =
  let _,tl_tm = pop gd.tomatch in
  let n = nb_localargs ind_data in 

(* gd.pred has the form [deptm_1]..[deptm_r]P (as given by the user, this is
 * an invariant of the algorithm) 
 * then p = [deptm_1] ([demptm_2]...[deptm_r]P   val_deptm_2...val_dpetm_r)
 *      next_pred = [deptm_1]..[deptm_r]P
 *)
  if not gd.case_dep then 
(* this computations is done now in build_nondep_branch
 let abs = to_lambda nparams arityind in  
 let narity = whd_beta (applist (abs, params)) in
 let next_pred = if info=SYNT then lambda_ize n narity (extract_lifted gd.pred)                  else  extract_lifted gd.pred in
*)
    let next_pred = extract_lifted gd.pred  in
    let (env0,pred0,_) = push_lam_and_liftl n [] next_pred [] in
    let depargs= List.map (lift n) (find_depargs env tl_tm) in
    let p =
      if depargs=[] (*or n=0*)  
      then lamn n env0 pred0
      else lamn n env0 (whd_beta (applist (pred0,depargs)))
    in (p,next_pred)
  else
    let pp = pTERMINENV(env, (extract_lifted gd.pred)) in
    errorlabstrm "build_nondep_predicate" 
      [<'sTR "Predicate  "; pp;
      	'sTR " is not correct for non-dependent elimination.">]
;;


(* TODO: Display in the message the nested dependent pattern found *)
let mssg_nested_dep_patt env mat =
[< 'sTR "Compilation of Dependent Cases fails when there are";'cUT;
   'sTR "nested patterns (in constructor form)  of dependent types."; 'cUT;
   'sTR "Try to transform your expression in a sequence of Dependent Cases"; 
   'cUT ; 'sTR "with simple patterns.">]
;;

(*
(* ity is closed *)  (* devrait être déplacé en tête *)
let rec to_lambda_pred isevars ind_data n env prod =
  if n=0 then prod 
  else match prod with 
    (DOP2(Prod,ty,DLAM(na,bd))) ->
      mkLambda na ty 
	(to_lambda_pred isevars ind_data (n-1) 
(*	   (Mach.push_rel !isevars (na,ty) env) bd)*)
	   (add_rel (na,outcast_type ty) env) bd)
  | DOP2(Cast,c,_) -> to_lambda_pred isevars ind_data n env c
  | _  -> error "to_lambda_unif"
;;
*)

let build_dep_predicate isevars env (current,ind_data,info) gd =
  if gd.case_dep then 
    let n = nb_localargs ind_data in

    if n=0 then (* the predicate is already dependent *)
      let npred =
	to_lambda 1 (extract_lifted gd.pred)
      in npred,npred
    else 
      if info=SYNT then 
     	errorlabstrm "build_dep_predicate" (mssg_nested_dep_patt env gd.mat)
      else 
  	let npred =
	  to_lambda (n+1) (extract_lifted gd.pred) 
  	in npred,npred
  
  else anomalylabstrm "build_dep_predicate"
      [<'sTR "build_dep_predicate was called with gd.case_dep=false ">]
;;

(* =================================== *)
(*   Principal functions               *)
(* =================================== *)

let my_norec_branch_scheme sigma i mind = 
  let typc =  type_inst_construct sigma i mind in
  let rec crec typc =
    match whd_betadeltaiota sigma typc with 
      DOP2(Prod,c,DLAM(name,t)) -> DOP2(Prod,c,DLAM(name,crec t))
    | (DOPN(AppL,v))  ->  appvect (mkExistential, tl_vect v)
    | _ -> mkExistential
  in crec typc
;;

let find_type_case_branches sigma env (current,ind_data,_) p =
  let {fullmind=ct;mind=ity;params=params;realargs=args} = ind_data in
  if not (is_for_mlcase p) then

    (* En attendant mieux ... *)
    let pt = Mach.newtype_of sigma env p in

    let evalpt = nf_ise1 sigma pt in
    let (_,bty,_)= type_case_branches env sigma ct evalpt p current
    in bty
  else
    let build_branch i = my_norec_branch_scheme sigma i ct in
    let lbr = List.map build_branch (interval 1 ind_data.nconstr)
    in  Array.of_list lbr
;;

(* if ityparam :(d_bar:D_bar)s
 * then we abstract the dependencies and the object building the non-binding
 * abstraction  [d_bar:D_bar][_:(I param d_bar)]body_br 
 *)

(**************************************************************************)

(* returns env,gd',args'  where:
 * if ltmj= e1...en then
 * we prepend (e1,INH_FIRST)(e2:INH)..(en,INH) to gd.tomatch (gd') and  
 * if not gd.case_dep  then env'=env and args'=[]
 *)
let push_tomatch env gd ltm =
  if not gd.case_dep  then  
    env, prepend_tomatch (List.map (fun tm -> (tm,INH)) ltm) gd,[]
  else
    let rec push_rec gd args = function 
      [] -> (gd,args)
    | (IsInd (c,ind_data) as tm)::l ->
	let {realargs=args} = ind_data in
  	let tyargs = args@[c] in
  	let ngd,resargs =  push_rec gd args l in
  	(prepend_tomatch [(tm,INH)] ngd, (tyargs@resargs))
    | (MayBeNotInd _)::l ->
	errorlabstrm "push_tomatch" 
	  [< 'sTR "Cases on terms of non inductive type is incompatible"; 
	     'fNL; 'sTR "with dependent case analysis" >]
  in
    let ngd,nargs = push_rec gd [] (List.tl ltm) in
    let fst_tm = (List.hd ltm) ,INH_FIRST in
      (env, prepend_tomatch [fst_tm] ngd, nargs)
;;

(* ---------------------------------------------------------*)




type dependency_option = DEP | NONDEP;;

(* if ityparam :(d_bar:D_bar)s
 * then we abstract the dependencies and the object building the non-binding
 * abstraction  [d_bar:D_bar]body_br 
 *)
let abstract_dep_generalized_args ind_data env brj =
  let {mind=ity;params=params;nparams=nparams;arity=arity}=ind_data in
  let lam_arity = to_lambda nparams arity in
  let arity0 = whd_beta (applist (lam_arity, params)) in
  let m =  nb_localargs ind_data in
  let params0 = List.map (lift m) params in
  let nity = applist (mutind_of_ind ity, params0@(rel_list 0 m)) in
  let arityenv,_ = splay_prod mtevd arity0 in
  {_VAL =
    lamn m arityenv (Environ.lambda_name (Anonymous,nity,lift (m+1) brj._VAL));
   _TYPE =
    prodn m arityenv (Environ.prod_name (Anonymous,nity,lift (m+1) brj._TYPE));
   _KIND = brj._KIND}
;;


(* *)
let check_if_may_need_dep_elim sigma current gd =
    let _,tl_tm= pop gd.tomatch in
      if (isRel current) & (tm_depends current sigma tl_tm)
      then warning_needs_dep_elim();;

let rec cc trad env gd =
 match (gdstatus env gd) with
   Match_Current (current,ind_data,info as cji) ->
     if not gd.case_dep then 
       (check_if_may_need_dep_elim !(trad.isevars) current gd;
	match_current trad env cji gd)
     else
       match_current_dep trad env cji gd
 | All_Variables -> substitute_rhs trad  env gd
 | Any_Tomatch   -> build_leaf trad env gd 

     (* for compiling dependent elimination *) 
 | All_Variables_Dep -> substitute_rhs_dep trad  env gd 
 | Any_Tomatch_Dep   -> build_leaf_dep     trad  env gd 
 | Solve_Constraint -> solve_constraint    trad  env gd 


and solve_constraint trad env gd =
 let cur,ci,npred= destruct_constraint gd in
 let ngd =  {case_dep = gd.case_dep; 
             pred = insert_lifted npred;
             deptm = solve_dependencies !(trad.isevars) env gd (cur,ci);
             tomatch = gd.tomatch;
             mat = gd.mat}
 in cc trad env ngd


and build_dep_branch trad env gd bty (current,ind_data,info) i =
 let sigma = !(trad.isevars) in
 let {mind=ity;params=params;realargs=args;nparams=nparams} = ind_data in
 let n =  (List.length args)+1 in
 let _,ty = decomp_n_prod sigma nparams (type_mconstruct sigma i (mutind_of_ind ity)) in
 let l,_ = splay_prod sigma ty in
 let lpatt = List.map (fun (na,ty) -> (to_mutind xtra_tm sigma ty,SYNT)) l in
 let ngd =  pop_and_prepend_tomatch lpatt gd in
 let ci_param = applist (ith_constructor i ind_data, params) in

 let rnnext_env0,next_mat = submat ngd.case_dep sigma env i 
                                    ind_data params current ngd.mat in
 let next_predicate = insert_constraint env ngd bty.(i-1) 
                                       ((current,info),ci_param)  in
 let next_gd = {ngd with
                  pred = insert_lifted next_predicate;
                  mat = next_mat} in
 let brenv,body_br = cc trad rnnext_env0 next_gd in
 let branch =
  if empty next_gd.tomatch 
  then body_br (* all the generalisations done in the elimination predicate 
                * have been consumed *)
  else let (_,nextinfo),_ = pop  next_gd.tomatch  in
  if nextinfo=SYNT then body_br (* there's no generalisation to consume *)
   else (* consume generalisations in the elim pred. through abstractions *)
   match (gdstatus rnnext_env0 next_gd) with
     Match_Current _ | All_Variables | All_Variables_Dep -> body_br
    | _ -> (* we abstract the generalized argument tomatch of 
            * elimination predicate [d_bar:D_bar][_:(I param d_bar)]body_br 
            *)
        abstract_dep_generalized_args ind_data rnnext_env0 body_br
 in
 let rnnext_env = common_prefix_ctxt env brenv in
 rnnext_env,
 {_VAL=eta_reduce_if_rel branch._VAL;_TYPE=branch._TYPE;_KIND=branch._KIND}
                           
(**************************************************************
 * to deal with multiple patterns of dependent families (ex. Nacira)!!
     
and build_nondep_branch sigma env gd next_pred bty (current,ind_data,info) i=
 let (ity,(params,args),nparams,arityind,nconstr) = ind_data in
 let n = nb_localargs ind_data in 
 let k = nb_prod (type_mconstruct sigma i ity) - nparams in
 let body,(next_env,ngd,curlp) = 
   push_lpatt_and_liftl k bty.(i-1) SYNT
             (env,
                 {case_dep= gd.case_dep; 
                  pred= insert_lifted next_pred; 
                  deptm = gd.deptm;
                  tomatch = snd (pop gd.tomatch);
                  mat = gd.mat},
                  (current::params)) in
 let (cur::lp) = curlp in 
 let lifted_params = Array.of_list lp in
 let ci = applist (ith_constructor i ind_data, lp@(rel_list 0 k)) in 

 let rnnext_env0,next_mat=submat ngd.case_dep sigma next_env i 
                                 ind_data lp cur ngd.mat in

 let ninfo,npred = 
  if n=0 then (SYNT, ngd.pred) (* as we treat only non-dep. elimination *)
  else let  dep_ci = args_app body in 
       if Array.length dep_ci=0   then  (info,ngd.pred) else
        let brpred = whd_beta (appvect (extract_lifted ngd.pred, dep_ci)) in
        let ciargs_patt =  List.map fst (fst (chop_list k ngd.tomatch)) in 
          (*we put pred. under same format that should be given by user
           * and set info to be INH, to indicate that dependecies have been
           * generalized *)
           let pred0 = abstract_pred_lterms next_env (brpred, ciargs_patt) 
           in (INH,(insert_lifted pred0))  in
 
 (* we change info of next current as current my pass from SYNT to INH
  * whenver dependencies are generalized in elimination predicate *)
 let ntomatch = 
   if empty ngd.tomatch then ngd.tomatch 
    else let ((next_cur ,_),nltm)= pop ngd.tomatch
         in push (next_cur, ninfo) nltm     in
 let next_gd = 
  {case_dep = ngd.case_dep;
   pred =  npred;
   deptm = solve_dependencies !(trad.isevars) next_env ngd (cur, ci);
   tomatch = ntomatch ;
   mat = next_mat} in
 let brenv,body_br = cc trad rnnext_env0 next_gd in
 let rnnext_env = common_prefix_ctxt next_env brenv in
 let _,branch,_ = lam_and_popl_named  k (get_rels rnnext_env) body_br []
 in rnnext_env,(eta_reduce_if_rel branch)

******************************************************)

(* build__nondep_branch ensures the invariant that elimination predicate in 
 * gd is always under the same form the user is expected to give it.
 * Thus, whenever an argument is destructed, for each
 * synthesed argument, the corresponding predicate is computed assuring
 * that the invariant.
 * Whenever we match an object u of type (I param t_bar),where I is a dependent
 * family of arity (x_bar:D_bar)s, in order to compile we
 *  1) replace the current element in gd by  (Rel 1) of type (I param x_bar)
 *     pushing to the environment env the new declarations  
 *     [x_bar : D_bar][_:(I param x_bar)]
 *  2) compile new gd in the environment env[x_bar : D_bar][_:(I param x_bar)]
 *     using the type (I param x_bar) to solve dependencies 
 *  3) pop the declarations [x_bar : D_bar][_:(I param x_bar)] from the
 *     environment by abstracting the result of compilation. We obtain a
 *     term ABST. Then apply the abstraction ABST to t_bar and u.
 *     The result is whd_beta (ABST t_bar u)
 *)

and build_nondep_branch trad env gd next_pred bty
 (current,ind_data,info as cji) i =
 let {mind=ity;params=params;nparams=nparams} = ind_data in
 let n = nb_localargs ind_data in
 let k = nb_prod (type_mconstruct !(trad.isevars) i (mutind_of_ind ity)) - nparams in

 (* if current is not rel, then we replace by rel so to solve dependencies *)
 let (nenv,ncurargs,ncur,ncurgd,npred,nbty) = 
  if isRel current 
   then (env, [], current, gd, (insert_lifted next_pred), bty.(i-1))
   else
     (* we push current and dependencies to environment *)
     let (relenv,nind_data,relargs) = push_params !(trad.isevars) env cji in

     (* we lift predicate and type branch w.r.t. to pushed arguments *) 
     let nrelargs = List.length relargs in
     let (curgd,lpred) = lift_gd nrelargs gd, lift_lfconstr nrelargs (insert_lifted next_pred)
     in (relenv, relargs, (Rel 1), 
	 (replace_gd_current(IsInd(Rel 1,nind_data),info) curgd),
         lpred,  lift nrelargs bty.(i-1))     in

 let body,(next_env,ngd,curlp) = 
   push_lpatt_and_liftl k nbty SYNT
            (nenv,
                 {case_dep= ncurgd.case_dep; 
                  pred= npred;
                  deptm = ncurgd.deptm;
                  tomatch = snd (pop ncurgd.tomatch);
                  mat = ncurgd.mat},
                 ncur::params) in

 match curlp with
     [] -> assert false
   | (cur::lp) ->
 let ci = applist (ith_constructor i ind_data, lp@(rel_list 0 k)) in 

 let rnnext_env0,next_mat=submat ngd.case_dep !(trad.isevars) next_env i 
                                 ind_data lp cur ngd.mat in

 if next_mat = [] then
      (* there is no row in the matrix corresponding to the ith constructor *)
      errorlabstrm "build_nondep_branch" (mssg_may_need_inversion())
 else

  let (linfo,npred) = 
    let  dep_ci = args_app body in
    let brpred = if (n=0 or Array.length dep_ci=0) then 
                    (* elmination predicate of ngd has correct number
                     * of abstractions *)
                     extract_lifted ngd.pred 
                 else whd_beta (appvect (extract_lifted ngd.pred, dep_ci)) in
    let ciargs_patt =  List.map fst (fst (chop_list k ngd.tomatch)) in 
           (*we put pred. under same format that should be given by user
            * and set info to be INH, to indicate that dependecies have been
            * generalized *)
    let linfo,pred0 = info_abstract_pred_lterms (brpred, ciargs_patt) 
    in
    (linfo,(insert_lifted pred0))
  in
 
 (* we change info of next current as current my pass from SYNT to INH
  * whenver dependencies are generalized in elimination predicate *)
 let ntomatch = 
  let synt_tomatch, inh_tomatch = chop_list k ngd.tomatch in
  let nsynt_tomatch = List.map2 (fun info (tm,_) -> (tm,info))
                            linfo synt_tomatch
  in nsynt_tomatch @ inh_tomatch  in 
   
 let next_gd = 
  {case_dep = ngd.case_dep;
   pred =  npred;
   deptm = solve_dependencies !(trad.isevars) next_env ngd (cur, ci);
   tomatch = ntomatch ;
   mat = next_mat}
 in

 let final_env, final_branch =
  let brenv,body_br = cc trad rnnext_env0 next_gd in
  let rnnext_env = common_prefix_ctxt next_env brenv in
  let branchenv,localenv = chop_list k (get_rels rnnext_env) in
  let localenv = List.map (fun (na,t) -> (na,incast_type t)) localenv in
  (* Avant ici, on nommait les Anonymous *)
  let branchval = lam_it body_br._VAL localenv in
  let branchtyp = prod_it body_br._TYPE localenv in
  ENVIRON(get_globals rnnext_env, branchenv),
  {_VAL=branchval;_TYPE=branchtyp;_KIND=body_br._KIND}

 in

 (* we restablish initial current by abstracting and applying  *)
 let p = List.length ncurargs  in
 let abstenv,localenv = chop_list p (get_rels final_env) in
  let localenv = List.map (fun (na,t) -> (na,incast_type t)) localenv in
  (* Avant ici, on nommait les Anonymous *)
 let abst = lam_it final_branch._VAL localenv in
 let typ = 
   substn_many (Array.map make_substituend (Array.of_list ncurargs)) 0
     final_branch._TYPE in
 let app = whd_beta (applist (abst, ncurargs)) in
 ENVIRON(get_globals final_env, abstenv),
 {_VAL = eta_reduce_if_rel app;
  _TYPE = typ;
  _KIND = final_branch._KIND}

and match_current trad env (current,ind_data,info as cji) gd =
  let {mind=ity;nparams=nparams;realargs=realargs;arity=arity;nconstr=nconstr} = ind_data in
  let _,tl_tm = pop gd.tomatch in

  (* we build new predicate p for elimination  *)
  let (p,next_pred) =
   build_nondep_predicate env cji gd in

  (* we build the branches *)
  let bty = find_type_case_branches !(trad.isevars) env cji p  in

  let build_ith_branch gd = build_nondep_branch trad env gd 
                               next_pred bty cji   in

  let build_case ()=
    let newenv,v =
      match List.map (build_ith_branch gd) (interval 1 nconstr) with
	  [] -> (*  nconstr=0 *)
	    env,
	  mkMutCaseA (ci_of_mind (mutind_of_ind ity)) 
		    (eta_reduce_if_rel p) current [||]

      | (bre1,f)::lenv_f as brl -> 
        let lf = Array.map Machops.j_val
		   (Array.of_list (f::(List.map snd lenv_f))) in
	let rec check_conv i =
	  if i = nconstr then () else
	    if not (Evarconv.the_conv_x_leq trad.isevars env lf.(i) bty.(i))
	    then 
	      let c = nf_ise1 !(trad.isevars) current
	      and lfi = nf_betaiota (nf_ise1 !(trad.isevars) lf.(i)) in
	      error_ill_formed_branch CCI env c i lfi (nf_betaiota bty.(i))
	    else check_conv (i+1)
	in
	check_conv 0;
        (common_prefix_ctxt env bre1,
         mkMutCaseA (ci_of_mind (mutind_of_ind ity)) (eta_reduce_if_rel p)
	   current lf) in
    newenv,
    {_VAL = v;
     _TYPE = whd_beta (applist (p,realargs));
     _KIND = sort_of_arity (Evd.mt_evd ()) arity}

  in
(*
  let build_mlcase () =
    if nconstr=0 
    then errorlabstrm "match_current" [< 'sTR "cannot treat ml-case">]
    else 
      let n = nb_localargs ind_data in
      let np= extract_lifted gd.pred  in
      let k = nb_lam np in
      let (_,npred) = decompose_lam np in
      let next_gd = {case_dep= gd.case_dep; 
                     pred= insert_lifted npred;
                     deptm = gd.deptm;
                     tomatch = gd.tomatch;
                     mat = gd.mat}
      in
      try (* we try to find out the predicate and recall match_current *)
       (let ipred = find_implicit_pred !(trad.isevars)
		      (build_ith_branch  next_gd) 
                      env cji in
         (* we abstract with the rest of tomatch *)
        let env0,bodyp = decompose_lam_n n ipred in
         (*we put pred. under same format that should be given by user*)
        let ipred0 = abstract_pred_lterms (bodyp, List.map fst tl_tm) in
        let nipred = lamn n env0 ipred0  in
        let explicit_gd = {gd with pred= insert_lifted nipred}
 
        in match_current trad env cji explicit_gd)

      with UserError(_,s) -> errorlabstrm "build_mlcase" 
                  [<'sTR "Not enough information to solve implicit Case" >] 

  in if is_for_mlcase p then  build_mlcase ()
     else *)  build_case ()


and match_current_dep trad env (current,ind_data,info as cji) gd =
  let sigma = !(trad.isevars) in 
  let {mind=ity;params=params;realargs=args;nconstr=nconstr;arity=arity}=ind_data in

  let nenv,ncurrent,ngd0=  
    if info=SYNT then   (* we try to guess the type of current *)
      if nb_prod (extract_lifted gd.pred) >0  then 
        (* we replace current implicit by (Rel 1) *) 
       	let nenv,ngd = push_and_lift_gdn 1 (extract_lifted gd.pred) (env,gd) in
	let ngd0 = replace_gd_current
		     (IsInd(Rel 1,lift_ind_data 1 ind_data),info) ngd
       	in nenv,(Rel 1),ngd0 
      else anomalylabstrm "match_current_dep" 
          [<'sTR "sth. wrong with gd.predicate">]
    else env,current,gd    (* i.e. current is typable in current env *)
  in       

  (* we build new predicate p for elimination  *)
  let (p,next_pred) = build_dep_predicate trad.isevars  nenv cji ngd0  in

  let np=whd_constraint p in
  
  (* we build the branches *)
  let bty = find_type_case_branches !(trad.isevars) nenv cji np  in

  let build_ith_branch env gd = build_dep_branch trad env gd bty cji in

  let ngd1 = replace_gd_pred (to_prod (nb_lam next_pred) next_pred) ngd0 in

  let build_dep_case () = 
   let nenv,rescase,casetyp =
    if info=SYNT then 
      (*= builds [d_bar:D_bar][h:(I~d_bar)]<..>Cases current of lf end =*)

      let lf = List.map (fun i -> Machops.j_val
			     (snd (build_ith_branch nenv ngd1 i)))
                            (interval 1 nconstr) in
      let case_exp =
 	mkMutCaseA (ci_of_mind (mutind_of_ind ity)) (eta_reduce_if_rel np)
	  current (Array.of_list lf) in
      let _,rescase,_ = elam_and_popl_named 1 nenv case_exp [] in
      let casetyp = whd_beta (applist (np,args)) in
      nenv,rescase,casetyp
    else  
      if info = INH_FIRST then
     (*= Consumes and initial tomatch so builds <..>Cases current of lf end =*)
       let lf = List.map (fun i -> Machops.j_val
			      (snd (build_ith_branch nenv ngd1 i)))
                  (interval 1 nconstr) in
       let rescase = mkMutCaseA (ci_of_mind (mutind_of_ind ity)) 
		 (eta_reduce_if_rel np) current (Array.of_list lf) in
       let casetyp = whd_beta (applist (np,args)) in
       nenv,rescase,casetyp

      else  (* we treat an INH value *)
       (* Consumes and initial tomatch abstracting that was generalized 
        *  [m:T] <..>Cases current of lf end  *) 
        let n = (List.length args)+1 in
        let nenv1,ngd2 = push_and_lift_gdn n (extract_lifted gd.pred)
			     (nenv, ngd1) in
	let np1 = lift n np in
        let lf = List.map (fun i -> Machops.j_val
			       (snd (build_ith_branch nenv1 ngd2 i))) 
                       (interval 1 nconstr)   in
        (* Now we replace the initial INH tomatch value (given by the user) 
         * by (Rel 1) so to link it to the product. The instantiation of the
         * this (Rel 1) by initial value will be done by the application 
         *)
        let case_exp =
           mkMutCaseA (ci_of_mind (mutind_of_ind ity)) np1 (Rel 1) (Array.of_list lf) in 
        let nenv2,rescase,_ = elam_and_popl_named n nenv1 case_exp [] in
	let casetyp = whd_beta (applist (np,args@[(Rel 1)])) in
        nenv2,rescase,casetyp

   in
   nenv,
   {_VAL = rescase;
    _TYPE = casetyp;
    _KIND = sort_of_arity (Evd.mt_evd ()) arity}
  in build_dep_case ()


and bare_substitute_rhs trad tm_is_dependent env gd =
 let (cur,info),tm = pop gd.tomatch in
 let nenv = rename_cur_ctxt env (term_tomatch cur) gd in
 let npred = 
   if gd.case_dep then gd.pred
    else (* le prochain argument n'est pas filtrable (i.e. parce que les
          *  motifs sont tous des variables ou parce qu'il n'y a plus de
          *  motifs), alors npred est gd.pred *)    
     let tmp_gd ={case_dep = gd.case_dep; pred = gd.pred; deptm = gd.deptm;
                  tomatch = tm; 
                  mat = List.map (subst_current (term_tomatch cur)) gd.mat} in
     let pred0 = extract_lifted gd.pred in
     let pred1 = apply_to_dep env pred0 cur 
     in insert_lifted pred1 in

 let ngd = if tm_is_dependent then
              {case_dep = gd.case_dep; 
               pred = npred;
               deptm = push_lifted (term_tomatch cur) gd.deptm;
               tomatch = tm; 
               mat = List.map shift_current_to_dep gd.mat}  
           else {case_dep = gd.case_dep; 
                 pred = npred;
                 deptm = gd.deptm;
                 tomatch = tm; 
                 mat = List.map (subst_current (term_tomatch cur))  gd.mat}  
  in let brenv,res =  cc trad nenv ngd
     in (common_prefix_ctxt nenv brenv), res


(* to preserve the invariant that elimination predicate is under the same
 * form we ask to the user, berfore substitution we compute the correct
 * elimination predicat whenver the argument is not inherited (i.e. info=SYNT)
 *)
and substitute_rhs trad env gd =
 let (curj,info),tm = pop gd.tomatch in
 let nenv = rename_cur_ctxt env (term_tomatch curj) gd in
 let npred = 
  match info with
   SYNT -> (* we abstract dependencies in elimination predicate, to maintain
             * the invariant, that gd.pred has always the correct number of
             * dependencies *)
            (*we put pred. under same format that should be given by user*)
   (try let npred = abstract_pred_lterms ((extract_lifted gd.pred),[curj])
        in insert_lifted npred
    with _ -> gd.pred )

  | _          -> gd.pred  in

 let ngd = {gd with pred= npred} in
 let tm_is_dependent = depends env (term_tomatch curj) tm 
 in bare_substitute_rhs trad tm_is_dependent env ngd


and substitute_rhs_dep trad env gd =
 let (curj,info),_ = pop gd.tomatch in
 let ([_,ty as v], npred) = get_n_prod 1 (extract_lifted gd.pred) in
 let nenv,ngd = push_and_lift_gd v (env,gd) in
 let ncur = (Rel 1) in
 let (_,ntm) = pop ngd.tomatch in
 let next_gd = {case_dep= gd.case_dep;
                 pred = insert_lifted npred;
                 deptm = ngd.deptm;
                 tomatch = [(to_mutind ncur !(trad.isevars) ty,info)]@ntm;
                 mat= ngd.mat}  in
 let tm_is_dependent = dependent ncur npred in
 let nenv0,body= bare_substitute_rhs trad tm_is_dependent nenv next_gd in
 let (na,ty),nenv1 = uncons_rel_env nenv0 in
 let nbodyval = Environ.lambda_name (na,incast_type ty,body._VAL) in
 let nbodytyp = Environ.prod_name (na,incast_type ty,body._TYPE) in
 let (nbodyval,nbodytyp) =
   if info=INH_FIRST then
     (applist(nbodyval,[term_tomatch curj]),
      subst1 (term_tomatch curj) body._TYPE)
   else (nbodyval,nbodytyp) in
 (nenv1, {_VAL=nbodyval;_TYPE=nbodytyp;_KIND=body._KIND})

and build_leaf trad env gd =
  match gd.mat with 
  | [] -> errorlabstrm "build_leaf" (mssg_may_need_inversion())
  | _::_::_ -> errorlabstrm "build_leaf" [<'sTR "Some clauses are redondant" >]
  | [row] ->
      let rhs = row.rhs in
      if rhs.user_ids <> [] then 
	anomaly "Some user pattern variables has not been substituted";
      if rhs.private_ids <> [] then 
	anomaly "Some private pattern variables has not been substituted";
      let j =
	try trad.pretype (mk_tycon (extract_lifted gd.pred)) env rhs.it
	with UserError(s,stream) -> 
	  raise (CCError("build_leaf",env,gd,(Some rhs.it),(s,stream))) in
      let subst = List.map (fun (id,c) -> (id,make_substituend c)) rhs.subst in
      let judge =
      {_VAL = substitute_dependencies (replace_vars subst j._VAL)
		(gd.deptm, row.dependencies);
       _TYPE = substitute_dependencies (replace_vars subst j._TYPE)
		 (gd.deptm, row.dependencies);
       _KIND = j._KIND} in
      env,judge

and build_leaf_dep trad env gd  = build_leaf trad env gd 
;;


(* Devrait être inutile et pris en compte par pretype 
let check_coercibility isevars env ty indty =
  if not (Evarconv.the_conv_x isevars env ty indty)
  then errorlabstrm "productize" 
    [< 'sTR "The type "; pTERMINENV (env,ty);
       'sTR " in the Cases annotation predicate"; 'sPC;
       'sTR "is not convertible to the inductive type"; 'sPC;
       pTERM indty >];;

(* productize [x1:A1]..[xn:An]u builds (x1:A1)..(xn:An)u and uses
   the types of tomatch to make some type inference *)
let check_pred_correctness isevars env tomatchl pred =
  let cook n = function
    | IsInd(c,({mind=ity;params=params;realargs=args;arity=arity} as ind_data))
      -> (applist (mutind_of_ind ity,(List.map (lift n) params)
		   @(rel_list 0 (nb_localargs ind_data))),
	  lift n (whd_beta (applist (arity,params))))
    | MayBeNotInd (_,_) -> anomaly "Should have been catched in case_dependent"
  in
  let rec checkrec n pred = function
      |	[] -> pred
      | tm::ltm ->
	  let (ty1,arity) = cook n tm in
	  let rec follow n (arity,pred) =
            match (whd_betadeltaiota mtevd arity,
		   whd_betadeltaiota !isevars pred) with
		DOP2(Prod,ty2,DLAM(_,bd2)),DOP2(Lambda,ty,DLAM(na,bd)) ->
		  check_coercibility isevars env ty2 ty;
		  follow (n+1) (bd2,bd)
	      | _ , DOP2(Lambda,ty,DLAM(na,bd)) ->
		  check_coercibility isevars env ty1 ty;
		  checkrec (n+1) bd ltm
	  in follow n (arity,pred)
  in checkrec 0 pred tomatchl
;;
*)
let build_expected_arity isdep tomatchl sort =
  let cook n = function
    | IsInd(c,({mind=ity;params=params;realargs=args;arity=arity} as ind_data))
      -> (applist (mutind_of_ind ity,(List.map (lift n) params)
		   @(rel_list 0 (nb_localargs ind_data))),
	  lift n (whd_beta (applist (arity,params))))
    | MayBeNotInd (_,_) -> anomaly "Should have been catched in case_dependent"
  in
  let rec buildrec n = function
      |	[] -> sort
      | tm::ltm ->
	  let (ty1,arity) = cook n tm in
	  let rec follow n arity =
            match whd_betadeltaiota mtevd arity with
		DOP2(Prod,ty2,DLAM(na,bd2)) ->
		  DOP2(Prod,ty2,DLAM(na,follow (n+1) bd2))
	      | _ ->
		  if isdep then
		  DOP2(Prod,ty1,DLAM(Anonymous,buildrec (n+1) ltm))
		  else buildrec n ltm
	  in follow n arity
  in buildrec 0 tomatchl

let rec productize  lam  = 
  match strip_outer_cast lam with 
    DOP2(Lambda,ty,DLAM(n,bd)) -> mkProd n ty (productize bd)
  | x  -> x                      
;;

(* determines wether the multiple case is dependent or not. For that
 * the predicate given by the user is eta-expanded. If the result
 * of expansion is pred, then :
 * if pred=[x1:T1]...[xn:Tn]P and tomatchj=[|[e1:S1]...[ej:Sj]] then
 * if n= SUM {i=1 to j} nb_prod (arity Sj)
 *  then case_dependent= false
 *  else if n= j+(SUM (i=1 to j) nb_prod(arity Sj))
 *        then case_dependent=true
 *        else error! (can not treat mixed dependent and non dependent case
 *)
let case_dependent env sigma predj tomatchj =
  let nb_dep_ity = function
      IsInd (_,ind_data) -> nb_localargs ind_data 
    | MayBeNotInd (c,t) -> errorlabstrm "case_dependent"
	            (error_case_not_inductive CCI env c t)
  in
  let etapred = eta_expand sigma predj._VAL predj._TYPE in
  let n = nb_lam etapred in
  let _,sort = decomp_prod sigma predj._TYPE in
  let ndepv = List.map nb_dep_ity tomatchj in
  let sum = List.fold_right (fun i j -> i+j)  ndepv 0  in
  if n=sum then (false,build_expected_arity true tomatchj sort)
  else if n=sum+ List.length tomatchj
  then (true,build_expected_arity true tomatchj sort)
  else errorlabstrm "case_dependent" 
      (mssg_wrong_predicate_arity env etapred sum (sum+ List.length tomatchj))
;;


(* builds the matrix of equations testing that each row has n patterns
 * and linearizing the _ patterns.
 *)
(*
let matx_of_eqns sigma env eqns n =
  let build_row = function
    | (ids,lpatt,rhs) ->
      	List.iter check_pat_arity lpatt;
	let (_,rlpatt) = rename_lpatt [] lpatt in
      	let _ = check_linearity env rlpatt lhs in
    	if List.length rlpatt = n
    	then { dependencies = []; 
               patterns =
	       { past = [];
		 future = 
		 List.map insert_lfpattern rlpatt};
               rhs = insert_lifted rhs}
    	else errorlabstrm "matx_of_eqns" (mssg_number_of_patterns env lhs n)
    | _ -> errorlabstrm "expand_mastx_patterns"
	  [<'sTR "empty list of patterns">]

  in List.map build_row eqns
;;
*)
(* Syntactic correctness has already been done in astterm *)
let matx_of_eqns sigma env eqns n =
  let build_row (ids,lpatt,rhs) =
    List.iter check_pat_arity lpatt;
    { dependencies = []; 
      patterns = { past = []; future = lpatt};
      rhs = {private_ids=[];subst=[];user_ids=ids;rhs_lift=0;it=rhs}}

  in List.map build_row eqns
;;


let initial_gd cd npred matx =
  { case_dep=cd;
    pred=insert_lifted npred; 
    deptm = []; 
    tomatch = []; 
    mat = matx }
;;


(*--------------------------------------------------------------------------*
 * A few functions to infer the inductive type from the patterns instead of *
 * checking that the patterns correspond to the ind. type of the            *
 * destructurated object. Allows type inference of examples like            *
 *  [n]Cases n of O => true | _ => false end                                *
 *--------------------------------------------------------------------------*)

(* Computing the inductive type from the matrix of patterns *)

let rec find_row_ind = function
    [] -> None
  | PatVar _ :: l -> find_row_ind l
  | PatCstr(_,c,_) :: _ -> Some c
  | PatAs(_,_,p)::l -> find_row_ind (p::l)
;;

let find_pretype mat =
  let lpatt = List.map (fun r -> List.hd r.patterns.future) mat in
  match find_row_ind lpatt with
    Some c -> mutind_of_constructor c
  | None -> anomalylabstrm "find_pretype" 
       	[<'sTR "Expecting a patt. in constructor form and found empty list">]
;;

(* Split type ty as the application of an inductive type to arguments.
 * If ty is not an inductive type, we look if we can infer if from the
 * constructor names in the first row of mat. We define evars that will
 * stand for the params & args of this inductive type. Works fine for
 * the params, but we cannot get information from the branches to find
 * the value of the arguments...
 *)
(*
let evar_find_mrectype isevars env mat ty =
  try find_mrectype !isevars ty
  with Induc ->
    (inh_coerce_to_ind isevars env ty (find_pretype mat);
     find_mrectype !isevars ty)
;;
*)

(* Same as above, but we do the unification for all the rows that contain
 * constructor patterns. This is what we do at the higher level of patterns.
 * For nested patterns, we do this unif when we ``expand'' the matrix, and we
 * use the function above.
 *)

let transpose mat =
  List.fold_right (List.map2 (fun p c -> p::c)) mat
    (if mat = [] then [] else List.map (fun _ -> []) (List.hd mat))
;;

let inh_coerce_to_ind isevars env ty tyi =
  let (ntys,_) = splay_prod !isevars (mind_arity tyi) in
  let evarl =
    List.map
      (fun (_,ty) ->
	 let s = Mach.sort_of mtevd env ty in
	   fst (new_isevar isevars env (mkCast ty (mkSort s)) CCI)) ntys in
  let expected_typ = applist (tyi,evarl) in
     (* devrait être indifférent d'exiger leq ou pas puisque pour 
        un inductif cela doit être égal *)
  if Evarconv.the_conv_x_leq isevars env expected_typ ty then ty
  else raise Induc
;;

let coerce_row trad env row tomatch =
  let j = trad.pretype mt_tycon env tomatch in
  match find_row_ind row with
      Some cstr ->
	(let tyi = mutind_of_constructor cstr in
	 try 
	   let indtyp = inh_coerce_to_ind trad.isevars env j._TYPE tyi in
	   IsInd (j._VAL,try_mutind_of !(trad.isevars) j._TYPE)
	 with Induc -> 
          errorlabstrm "coerce_row"
	    (mssg_tomatch_of_unexpected_type cstr j._TYPE))
    | None -> 
	try IsInd (j._VAL,try_mutind_of !(trad.isevars) j._TYPE)
	with Induc -> MayBeNotInd (j._VAL,j._TYPE)
;;

let coerce_to_indtype trad env matx tomatchl =
  let pats = List.map (fun r ->  r.patterns.future) matx in
  List.map2 (coerce_row trad env) (transpose pats) tomatchl
;;

(* (mach_)compile_multcase:
 * The multcase that are in rhs are rawconstr
 * when we arrive at the leaves we call
 * trad.pretype that will  call compile recursively.
 * compile (<pred>Case e1..en end of ...)= ([x1...xn]t' e1...en)
 * where t' is the result of the translation. 
 * INVARIANT for NON-DEP COMPILATION: predicate in gd is always under the same
 * form we ask the user to write <..>.
 * Thus, during the algorithm, whenever the argument to match is inherited
 * (i.e. info<>SYNT) the elimination predicate in gd should have the correct
 * number of abstractions. Whenever the argument to match is synthesed we have
 * to abstract all the dependencies in the elimination predicate, before 
 * processing the tomatch argument. The invariant is thus preserved in the
 * functions build_nondep_branch y substitute_rhs.
 * Note: this function is used by trad.ml 
 *)

let compile_multcase_fail trad vtcon env (predopt, tomatchl, eqns) =

 (* We build the matrix of patterns and right-hand-side *)
 let matx = matx_of_eqns !(trad.isevars) env eqns (List.length tomatchl) in

 (* We build the vector of terms to match consistently with the *)
 (* constructors found in patterns *)
 let tomatchj = coerce_to_indtype trad env matx tomatchl in

 (* We build the elimination predicate and check its consistency with *)
 (* the type of arguments to match *)
 let cd,npred =
   match predopt with
   | None ->
       let finalres =
	 match vtcon with
	  | (_,(_,Some p)) -> p
	  | _ -> let ty = mkCast dummy_sort dummy_sort in
		 let (c,_) = new_isevar trad.isevars env ty CCI in c
       in (false,abstract_pred_lterms (finalres,tomatchj))
   | Some pred ->
     (* First call to exemeta to know if it is dependent *)
     let predj1 = trad.pretype mt_tycon env pred in
     let cdep,arity = case_dependent env !(trad.isevars) predj1 tomatchj in
     (* We got the expected arity of pred and relaunch pretype with it *)
     let predj = trad.pretype (mk_tycon arity) env pred in
     let etapred = eta_expand !(trad.isevars) predj._VAL predj._TYPE in
     if cdep then (cdep, productize etapred)
     else (cdep,etapred) in

 let gdi = initial_gd cd npred matx in

 (* we push the terms to match to gd *)
 let env1,gd,args = push_tomatch env gdi tomatchj in

 (* Now we compile, abstract and reapply the terms tomatch *)
 let brenv,body = cc trad env1 gd in 
 let rnenv1 = common_prefix_ctxt env1 brenv in
 let k = List.length (get_rels env1) - List.length (get_rels env) in
 let env2,abst,_ = elam_and_popl k rnenv1 body._VAL [] in
 let typ = body._TYPE in (* DEVRAIT ETRE INCORRECT *)
 let res = if args=[] then abst
           else whd_beta (applist (abst, args)) in
(*
 let rest = Mach.newtype_of !(trad.isevars) env2 res in
 let resl = Mach.newtype_of !(trad.isevars) env2 rest in
*)
 {_VAL=res;_TYPE=typ;_KIND=body._KIND}
;;

let compile_multcase (pretype,isevars) vtcon env macro =
 let trad = {pretype=(fun vtyc env -> pretype vtyc env);
             isevars = isevars} in
 try  compile_multcase_fail trad vtcon env macro
 with UserError("Ill-formed branches", s) ->  mssg_ill_typed_branch (s)
    | CCError ("build_leaf", errenv, errgd,errrhs,innermssg) ->
         mssg_build_leaf  errenv  errgd errrhs innermssg
;;
