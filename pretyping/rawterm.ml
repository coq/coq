(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

(*i*)
open Util
open Names
open Sign
open Term
open Libnames
open Nametab
(*i*)

(* Untyped intermediate terms, after ASTs and before constr. *)

type loc = int * int

(* locs here refers to the ident's location, not whole pat *)
(* the last argument of PatCstr is a possible alias ident for the pattern *)
type cases_pattern =
  | PatVar of loc * name
  | PatCstr of loc * constructor * cases_pattern list * name

type rawsort = RProp of Term.contents | RType of Univ.universe option

type fix_kind = RFix of (int array * int) | RCoFix of int

type binder_kind = BProd | BLambda | BLetIn

type quantified_hypothesis = AnonHyp of int | NamedHyp of identifier

type 'a explicit_substitution = (quantified_hypothesis * 'a) list

type 'a substitution = 
  | ImplicitBindings of 'a list
  | ExplicitBindings of 'a explicit_substitution
  | NoBindings

type 'a with_bindings = 'a * 'a substitution

type hole_kind =
  | ImplicitArg of global_reference * int
  | AbstractionType of name
  | QuestionMark
  | CasesType
  | InternalHole
  | TomatchTypeParameter of inductive * int

type 'ctxt reference =
  | RConst of constant * 'ctxt
  | RInd of inductive * 'ctxt
  | RConstruct of constructor * 'ctxt
  | RVar of identifier
  | REVar of int * 'ctxt

type rawconstr = 
  | RRef of loc * global_reference
  | RVar of loc * identifier
  | REvar of loc * existential_key
  | RMeta of loc * int
  | RApp of loc * rawconstr * rawconstr list
  | RLambda of loc * name * rawconstr * rawconstr
  | RProd of loc * name * rawconstr * rawconstr
  | RLetIn of loc * name * rawconstr * rawconstr
  | RCases of loc * Term.case_style * rawconstr option * rawconstr list * 
      (loc * identifier list * cases_pattern list * rawconstr) list
  | ROldCase of loc * bool * rawconstr option * rawconstr * 
      rawconstr array
  | RRec of loc * fix_kind * identifier array * 
      rawconstr array * rawconstr array
  | RSort of loc * rawsort
  | RHole of (loc * hole_kind)
  | RCast of loc * rawconstr * rawconstr
  | RDynamic of loc * Dyn.t


(*i - if PRec (_, names, arities, bodies) is in env then arities are
   typed in env too and bodies are typed in env enriched by the
   arities incrementally lifted 

  [On pourrait plutot mettre les arités aves le type qu'elles auront
   dans le contexte servant à typer les body ???]

   - boolean in POldCase means it is recursive
i*)

let rec subst_pat subst pat = 
  match pat with
  | PatVar _ -> pat
  | PatCstr (loc,((kn,i),j),cpl,n) -> 
      let kn' = subst_kn subst kn 
      and cpl' = list_smartmap (subst_pat subst) cpl in
	if kn' == kn && cpl' == cpl then pat else
	  PatCstr (loc,((kn',i),j),cpl',n)
	
let rec subst_raw subst raw = 
  match raw with
  | RRef (loc,ref) -> 
      let ref' = subst_global subst ref in 
	if ref' == ref then raw else
	  RRef (loc,ref')

  | RVar _ -> raw
  | REvar _ -> raw
  | RMeta _ -> raw

  | RApp (loc,r,rl) -> 
      let r' = subst_raw subst r 
      and rl' = list_smartmap (subst_raw subst) rl in
	if r' == r && rl' == rl then raw else
	  RApp(loc,r',rl')

  | RLambda (loc,n,r1,r2) -> 
      let r1' = subst_raw subst r1 and r2' = subst_raw subst r2 in
	if r1' == r1 && r2' == r2 then raw else
	  RLambda (loc,n,r1',r2')

  | RProd (loc,n,r1,r2) -> 
      let r1' = subst_raw subst r1 and r2' = subst_raw subst r2 in
	if r1' == r1 && r2' == r2 then raw else
	  RProd (loc,n,r1',r2')

  | RLetIn (loc,n,r1,r2) -> 
      let r1' = subst_raw subst r1 and r2' = subst_raw subst r2 in
	if r1' == r1 && r2' == r2 then raw else
	  RLetIn (loc,n,r1',r2')

  | RCases (loc,cs,ro,rl,branches) -> 
      let ro' = option_smartmap (subst_raw subst) ro 
      and rl' = list_smartmap (subst_raw subst) rl
      and branches' = list_smartmap 
			(fun (loc,idl,cpl,r as branch) ->
			   let cpl' = list_smartmap (subst_pat subst) cpl
			   and r' = subst_raw subst r in
			     if cpl' == cpl && r' == r then branch else
			       (loc,idl,cpl',r'))
			branches
      in
	if ro' == ro && rl' == rl && branches' == branches then raw else
	  RCases (loc,cs,ro',rl',branches')

  | ROldCase (loc,b,ro,r,ra) -> 
      let ro' = option_smartmap (subst_raw subst) ro
      and r' = subst_raw subst r 
      and ra' = array_smartmap (subst_raw subst) ra in
	if ro' == ro && r' == r && ra' == ra then raw else
	  ROldCase (loc,b,ro',r',ra')

  | RRec (loc,fix,ida,ra1,ra2) -> 
      let ra1' = array_smartmap (subst_raw subst) ra1
      and ra2' = array_smartmap (subst_raw subst) ra2 in
	if ra1' == ra1 && ra2' == ra2 then raw else
	  RRec (loc,fix,ida,ra1',ra2')

  | RSort _ -> raw

  | RHole (loc,ImplicitArg (ref,i)) ->
      let ref' = subst_global subst ref in 
	if ref' == ref then raw else
	  RHole (loc,ImplicitArg (ref',i))
  | RHole (loc, (AbstractionType _ | QuestionMark | CasesType |
      InternalHole | TomatchTypeParameter _)) -> raw

  | RCast (loc,r1,r2) -> 
      let r1' = subst_raw subst r1 and r2' = subst_raw subst r2 in
	if r1' == r1 && r2' == r2 then raw else
	  RCast (loc,r1',r2')

  | RDynamic _ -> raw

let dummy_loc = (0,0)

let loc_of_rawconstr = function
  | RRef (loc,_) -> loc
  | RVar (loc,_) -> loc
  | REvar (loc,_) -> loc
  | RMeta (loc,_) -> loc
  | RApp (loc,_,_) -> loc
  | RLambda (loc,_,_,_) -> loc
  | RProd (loc,_,_,_) -> loc
  | RLetIn (loc,_,_,_) -> loc
  | RCases (loc,_,_,_,_) -> loc
  | ROldCase (loc,_,_,_,_) -> loc
  | RRec (loc,_,_,_,_) -> loc
  | RSort (loc,_) -> loc
  | RHole (loc,_) -> loc
  | RCast (loc,_,_) -> loc
  | RDynamic (loc,_) -> loc

let join_loc (deb1,_) (_,fin2) = (deb1,fin2)

type 'a raw_red_flag = {
  rBeta : bool;
  rIota : bool;
  rZeta : bool;
  rDelta : bool; (* true = delta all but rConst; false = delta only on rConst*)
  rConst : 'a list
}

type ('a,'b) red_expr_gen =
  | Red of bool
  | Hnf
  | Simpl
  | Cbv of 'b raw_red_flag
  | Lazy of 'b raw_red_flag
  | Unfold of (int list * 'b) list
  | Fold of 'a list
  | Pattern of (int list * 'a) list
  | ExtraRedExpr of string * 'a

type 'a or_metanum = AN of loc * 'a | MetaNum of loc * int

type 'a may_eval =
  | ConstrTerm of 'a
  | ConstrEval of ('a, qualid or_metanum) red_expr_gen * 'a
  | ConstrContext of (loc * identifier) * 'a
  | ConstrTypeOf of 'a
