(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

(*i*)
open Pp
open Util
open Names
open Nameops
open Libnames
open Rawterm
open Term
(*i*)


(* This is the subtype of rawconstr allowed in syntactic extensions *)
type aconstr =
  | ARef of global_reference
  | AVar of identifier
  | AApp of aconstr * aconstr list
  | ALambda of name * aconstr * aconstr
  | AProd of name * aconstr * aconstr
  | ALetIn of name * aconstr * aconstr
  | AOldCase of case_style * aconstr option * aconstr * aconstr array
  | ASort of rawsort
  | AHole of hole_kind
  | AMeta of int
  | ACast of aconstr * aconstr
  
let name_app f e = function
  | Name id -> let (id, e) = f id e in (Name id, e)
  | Anonymous -> Anonymous, e

let map_aconstr_with_binders_loc loc g f e = function
  | AVar (id) -> RVar (loc,id)
  | AApp (a,args) -> RApp (loc,f e a, List.map (f e) args)
  | ALambda (na,ty,c) ->
      let na,e = name_app g e na in RLambda (loc,na,f e ty,f e c)
  | AProd (na,ty,c) ->
      let na,e = name_app g e na in RProd (loc,na,f e ty,f e c)
  | ALetIn (na,b,c) ->
      let na,e = name_app g e na in RLetIn (loc,na,f e b,f e c)
  | AOldCase (b,tyopt,tm,bv) ->
      ROrderedCase (loc,b,option_app (f e) tyopt,f e tm,Array.map (f e) bv)
  | ACast (c,t) -> RCast (loc,f e c,f e t)
  | ASort x -> RSort (loc,x)
  | AHole x  -> RHole (loc,x)
  | AMeta n -> RMeta (loc,n)
  | ARef x -> RRef (loc,x)

let rec subst_aconstr subst raw =
  match raw with
  | ARef ref -> 
      let ref' = subst_global subst ref in 
	if ref' == ref then raw else
	  ARef ref'

  | AVar _ -> raw

  | AApp (r,rl) -> 
      let r' = subst_aconstr subst r 
      and rl' = list_smartmap (subst_aconstr subst) rl in
	if r' == r && rl' == rl then raw else
	  AApp(r',rl')

  | ALambda (n,r1,r2) -> 
      let r1' = subst_aconstr subst r1 and r2' = subst_aconstr subst r2 in
	if r1' == r1 && r2' == r2 then raw else
	  ALambda (n,r1',r2')

  | AProd (n,r1,r2) -> 
      let r1' = subst_aconstr subst r1 and r2' = subst_aconstr subst r2 in
	if r1' == r1 && r2' == r2 then raw else
	  AProd (n,r1',r2')

  | ALetIn (n,r1,r2) -> 
      let r1' = subst_aconstr subst r1 and r2' = subst_aconstr subst r2 in
	if r1' == r1 && r2' == r2 then raw else
	  ALetIn (n,r1',r2')

  | AOldCase (b,ro,r,ra) -> 
      let ro' = option_smartmap (subst_aconstr subst) ro
      and r' = subst_aconstr subst r 
      and ra' = array_smartmap (subst_aconstr subst) ra in
	if ro' == ro && r' == r && ra' == ra then raw else
	  AOldCase (b,ro',r',ra')

  | AMeta _ | ASort _ -> raw

  | AHole (ImplicitArg (ref,i)) ->
      let ref' = subst_global subst ref in 
	if ref' == ref then raw else
	  AHole (ImplicitArg (ref',i))
  | AHole ( (AbstractionType _ | QuestionMark | CasesType |
      InternalHole | TomatchTypeParameter _)) -> raw

  | ACast (r1,r2) -> 
      let r1' = subst_aconstr subst r1 and r2' = subst_aconstr subst r2 in
	if r1' == r1 && r2' == r2 then raw else
	  ACast (r1',r2')

let rec aux = function
  | RVar (_,id) -> AVar id
  | RApp (_,g,args) -> AApp (aux g, List.map aux args)
  | RLambda (_,na,ty,c) -> ALambda (na,aux ty,aux c)
  | RProd (_,na,ty,c) -> AProd (na,aux ty,aux c)
  | RLetIn (_,na,b,c) -> ALetIn (na,aux b,aux c)
  | ROrderedCase (_,b,tyopt,tm,bv) ->
      AOldCase (b,option_app aux tyopt,aux tm, Array.map aux bv)
  | RCast (_,c,t) -> ACast (aux c,aux t)
  | RSort (_,s) -> ASort s
  | RHole (_,w) -> AHole w
  | RRef (_,r) -> ARef r
  | RMeta (_,n) -> AMeta n
  | RDynamic _ | RRec _ | RCases _ | REvar _ ->
      error "Fixpoints, cofixpoints, existential variables and pattern-matching  not \
allowed in abbreviatable expressions"

let aconstr_of_rawconstr = aux

(*s Concrete syntax for terms *)

type scope_name = string

type notation = string

type explicitation = int

type cases_pattern_expr =
  | CPatAlias of loc * cases_pattern_expr * identifier
  | CPatCstr of loc * reference * cases_pattern_expr list
  | CPatAtom of loc * reference option
  | CPatNumeral of loc * Bignat.bigint
  | CPatDelimiters of loc * scope_name * cases_pattern_expr

type constr_expr =
  | CRef of reference
  | CFix of loc * identifier located * fixpoint_expr list
  | CCoFix of loc * identifier located * cofixpoint_expr list
  | CArrow of loc * constr_expr * constr_expr
  | CProdN of loc * (name located list * constr_expr) list * constr_expr
  | CLambdaN of loc * (name located list * constr_expr) list * constr_expr
  | CLetIn of loc * name located * constr_expr * constr_expr
  | CAppExpl of loc * reference * constr_expr list
  | CApp of loc * constr_expr * (constr_expr * explicitation option) list
  | CCases of loc * constr_expr option * constr_expr list *
      (loc * cases_pattern_expr list * constr_expr) list
  | COrderedCase of loc * case_style * constr_expr option * constr_expr
      * constr_expr list
  | CHole of loc
  | CMeta of loc * int
  | CSort of loc * rawsort
  | CCast of loc * constr_expr * constr_expr
  | CNotation of loc * notation * (identifier * constr_expr) list
  | CGrammar of loc * aconstr * (identifier * constr_expr) list
  | CNumeral of loc * Bignat.bigint
  | CDelimiters of loc * scope_name * constr_expr
  | CDynamic of loc * Dyn.t

and fixpoint_expr = identifier * int * constr_expr * constr_expr

and cofixpoint_expr = identifier * constr_expr * constr_expr

let constr_loc = function
  | CRef (Ident (loc,_)) -> loc
  | CRef (Qualid (loc,_)) -> loc
  | CFix (loc,_,_) -> loc
  | CCoFix (loc,_,_) -> loc
  | CArrow (loc,_,_) -> loc
  | CProdN (loc,_,_) -> loc
  | CLambdaN (loc,_,_) -> loc
  | CLetIn (loc,_,_,_) -> loc
  | CAppExpl (loc,_,_) -> loc
  | CApp (loc,_,_) -> loc
  | CCases (loc,_,_,_) -> loc
  | COrderedCase (loc,_,_,_,_) -> loc
  | CHole loc -> loc
  | CMeta (loc,_) -> loc
  | CSort (loc,_) -> loc
  | CCast (loc,_,_) -> loc
  | CNotation (loc,_,_) -> loc
  | CGrammar (loc,_,_) -> loc
  | CNumeral (loc,_) -> loc
  | CDelimiters (loc,_,_) -> loc
  | CDynamic _ -> dummy_loc

let cases_pattern_loc = function
  | CPatAlias (loc,_,_) -> loc
  | CPatCstr (loc,_,_) -> loc
  | CPatAtom (loc,_) -> loc
  | CPatNumeral (loc,_) -> loc
  | CPatDelimiters (loc,_,_) -> loc

let replace_vars_constr_expr l t =
  if l = [] then t else failwith "replace_constr_expr: TODO"

let occur_var_constr_ref id = function
  | Ident (loc,id') -> id = id'
  | Qualid _ -> false

let rec occur_var_constr_expr id = function
  | CRef r -> occur_var_constr_ref id r
  | CArrow (loc,a,b) -> occur_var_constr_expr id a or occur_var_constr_expr id b
  | CAppExpl (loc,r,l) ->
      occur_var_constr_ref id r or List.exists (occur_var_constr_expr id) l
  | CApp (loc,f,l) ->
      occur_var_constr_expr id f or
      List.exists (fun (a,_) -> occur_var_constr_expr id a) l
  | CProdN (_,l,b) -> occur_var_binders id b l
  | CLambdaN (_,l,b) -> occur_var_binders id b l
  | CLetIn (_,na,a,b) -> occur_var_binders id b [[na],a]
  | CCast (loc,a,b) -> occur_var_constr_expr id a or occur_var_constr_expr id b
  | CNotation (_,_,l) -> List.exists (fun (_,x) -> occur_var_constr_expr id x) l
  | CGrammar (loc,_,l) -> List.exists (fun (_,x) -> occur_var_constr_expr id x)l
  | CDelimiters (loc,_,a) -> occur_var_constr_expr id a
  | CHole _ | CMeta _ | CSort _ | CNumeral _ | CDynamic _ -> false
  | CCases (loc,_,_,_) 
  | COrderedCase (loc,_,_,_,_) 
  | CFix (loc,_,_) 
  | CCoFix (loc,_,_) -> 
      Pp.warning "Capture check in multiple binders not done"; false

and occur_var_binders id b = function
  | (idl,a)::l -> 
      occur_var_constr_expr id a or
      (not (List.mem (Name id) (snd (List.split idl)))
      & occur_var_binders id b l)
  | [] -> occur_var_constr_expr id b

let mkIdentC id  = CRef (Ident (dummy_loc, id))
let mkRefC r     = CRef r
let mkAppC (f,l) = CApp (dummy_loc, f, List.map (fun x -> (x,None)) l)
let mkCastC (a,b)  = CCast (dummy_loc,a,b)
let mkLambdaC (idl,a,b) = CLambdaN (dummy_loc,[idl,a],b)
let mkLetInC (id,a,b)   = CLetIn (dummy_loc,id,a,b)
let mkProdC (idl,a,b)   = CProdN (dummy_loc,[idl,a],b)

(* Used in correctness and interface *)

let map_binders f g e bl =
  (* TODO: avoid variable capture in [t] by some [na] in [List.tl nal] *)
  let h (nal,t) (e,bl) =
    (List.fold_right (fun (_,na) -> name_fold g na) nal e,(nal,f e t)::bl) in
  List.fold_right h bl (e,[])

let map_constr_expr_with_binders f g e = function
  | CArrow (loc,a,b) -> CArrow (loc,f e a,f e b)
  | CAppExpl (loc,r,l) -> CAppExpl (loc,r,List.map (f e) l) 
  | CApp (loc,a,l) -> CApp (loc,f e a,List.map (fun (a,i) -> (f e a,i)) l)
  | CProdN (loc,bl,b) ->
      let (e,bl) = map_binders f g e bl in CProdN (loc,bl,f e b)
  | CLambdaN (loc,bl,b) ->
      let (e,bl) = map_binders f g e bl in CLambdaN (loc,bl,f e b)
  | CLetIn (loc,na,a,b) -> CLetIn (loc,na,f e a,f (name_fold g (snd na) e) b)
  | CCast (loc,a,b) -> CCast (loc,f e a,f e b)
  | CNotation (loc,n,l) -> CNotation (loc,n,List.map (fun (x,t) ->(x,f e t)) l)
  | CGrammar (loc,r,l) -> CGrammar (loc,r,List.map (fun (x,t) ->(x,f e t)) l)
  | CDelimiters (loc,s,a) -> CDelimiters (loc,s,f e a)
  | CHole _ | CMeta _ | CSort _ | CNumeral _ | CDynamic _ | CRef _ as x -> x
  | CCases (loc,po,a,bl) ->
      (* TODO: apply g on the binding variables in pat... *)
      (* hard because no syntactic diff between a constructor and a var *)
      let bl = List.map (fun (loc,pat,rhs) -> (loc,pat,f e rhs)) bl in
      CCases (loc,option_app (f e) po,List.map (f e) a,bl)
  | COrderedCase (loc,s,po,a,bl) ->
      COrderedCase (loc,s,option_app (f e) po,f e a,List.map (f e) bl)
  | CFix (loc,id,dl) ->
      CFix (loc,id,List.map (fun (id,n,t,d) -> (id,n,f e t,f e d)) dl)
  | CCoFix (loc,id,dl) ->
      CCoFix (loc,id,List.map (fun (id,t,d) -> (id,f e t,f e d)) dl)

(* For binders parsing *)

type local_binder =
  | LocalRawDef of name located * constr_expr
  | LocalRawAssum of name located list * constr_expr

(* Concrete syntax for modules and modules types *)

type with_declaration_ast = 
  | CWith_Module of identifier * qualid located
  | CWith_Definition of identifier * constr_expr

type module_type_ast = 
  | CMTEident of qualid located
  | CMTEwith of module_type_ast * with_declaration_ast

type module_ast = 
  | CMEident of qualid located
  | CMEapply of module_ast * module_ast
