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
open Univ
open Names
open Nameops
open Term
open Termops
open Inductive
open Sign
open Environ
open Libnames
open Declare
open Impargs
open Topconstr
open Rawterm
open Pattern
open Nametab
(*i*)

(* Translation from rawconstr to front constr *)

(**********************************************************************)
(* Parametrization                                                    *)

(* This governs printing of local context of references *)
let print_arguments = ref false

(* If true, prints local context of evars, whatever print_arguments *)
let print_evar_arguments = ref false

(* This forces printing of cast nodes *)
let print_casts = ref true

(* This governs printing of implicit arguments.  When
   [print_implicits] is on then [print_implicits_explicit_args] tells
   how implicit args are printed. If on, implicit args are printed
   prefixed by "!" otherwise the function and not the arguments is
   prefixed by "!" *)
let print_implicits = ref false
let print_implicits_explicit_args = ref false

(* This forces printing of coercions *)
let print_coercions = ref false

(* This forces printing universe names of Type{.} *)
let print_universes = ref false


let with_option o f x =
  let old = !o in o:=true;
  try let r = f x in o := old; r
  with e -> o := old; raise e

let with_arguments f = with_option print_arguments f
let with_casts f = with_option print_casts f
let with_implicits f = with_option print_implicits f
let with_coercions f = with_option print_coercions f
let with_universes f = with_option print_universes f

(**********************************************************************)
(* conversion of references                                           *)

let ids_of_ctxt ctxt =
  Array.to_list
    (Array.map
       (function c -> match kind_of_term c with
	  | Var id -> id
	  | _ ->
       error
       "Termast: arbitrary substitution of references not yet implemented")
     ctxt)

let idopt_of_name = function 
  | Name id -> Some id
  | Anonymous -> None

let extern_evar loc n = warning "No notation for Meta"; CMeta (loc,n)

let extern_ref r = Qualid (dummy_loc,shortest_qualid_of_global None r)

(**********************************************************************)
(* conversion of patterns                                             *)

let rec extern_cases_pattern = function   (* loc is thrown away for printing *)
  | PatVar (loc,Name id) -> CPatAtom (loc,Some (Ident (loc,id)))
  | PatVar (loc,Anonymous) -> CPatAtom (loc, None) 
  | PatCstr(loc,cstrsp,args,na) ->
      let args = List.map extern_cases_pattern args in
      let p = CPatCstr (loc,extern_ref (ConstructRef cstrsp),args) in
      (match na with
	| Name id -> CPatAlias (loc,p,id)
	| Anonymous -> p)
	
let occur_name na aty =
  match na with
    | Name id -> occur_var_constr_expr id aty
    | Anonymous -> false

(* Implicit args indexes are in ascending order *)
let explicitize impl f args =
  let n = List.length args in
  let rec exprec q = function
    | a::args, imp::impl when is_status_implicit imp ->
        let tail = exprec (q+1) (args,impl) in
        let visible =
          (!print_implicits & !print_implicits_explicit_args)
          or not (is_inferable_implicit n imp) in
        if visible then (a,Some q) :: tail else tail
    | a::args, _::impl -> (a,None) :: exprec (q+1) (args,impl)
    | args, [] -> List.map (fun a -> (a,None)) args (*In case of polymorphism*)
    | [], _ -> [] in
  let args = exprec 1 (args,impl) in
  if args = [] then f else CApp (dummy_loc, f, args)

let rec skip_coercion dest_ref (f,args as app) =
  if !print_coercions then app
  else
    try
      match dest_ref f with
	| Some r ->
	    (match Classops.hide_coercion r with
	       | Some n ->
		   if n >= List.length args then app
		   else (* We skip a coercion *)
		     let _,fargs = list_chop n args in
	       	     skip_coercion dest_ref (List.hd fargs,List.tl fargs)
	       | None -> app)
	| None -> app
    with Not_found -> app

let extern_app impl f args =
  if !print_implicits & not !print_implicits_explicit_args then 
    CAppExpl (dummy_loc, f, args)
  else
    explicitize impl (CRef f) args

let loc = dummy_loc

let rec extern = function
  | RRef (_,ref) -> CRef (extern_ref ref)

  | RVar (_,id) -> CRef (Ident (loc,id))

  | REvar (_,n) -> extern_evar loc n

  | RMeta (_,n) -> CMeta (loc,n)

  | RApp (_,f,args) ->
      let (f,args) =
	skip_coercion (function RRef(_,r) -> Some r | _ -> None) (f,args) in
      let args = List.map extern args in
      (match f with
	 | REvar (loc,ev) -> extern_evar loc ev (* we drop args *)
	 | RRef (loc,ref) ->
	     extern_app (implicits_of_global ref) (extern_ref ref) args
	 | _       -> explicitize [] (extern f) args)

  | RProd (_,Anonymous,t,c) ->
      (* Anonymous product are never factorized *)
      CArrow (loc,extern t,extern c)

  | RLetIn (_,na,t,c) ->
      CLetIn (loc,(loc,na),extern t,extern c)

  | RProd (_,na,t,c) ->
      let t = extern t in
      let (idl,c) = factorize_prod t c in
      CProdN (loc,[(loc,na)::idl,t],c)

  | RLambda (_,na,t,c) ->
      let t = extern t in
      let (idl,c) = factorize_lambda t c in
      CLambdaN (loc,[(loc,na)::idl,t],c)

  | RCases (_,typopt,tml,eqns) ->
      let pred = option_app extern typopt in
      let tml = List.map extern tml in
      let eqns = List.map extern_eqn eqns in 
      CCases (loc,pred,tml,eqns)
	
  | ROrderedCase (_,cs,typopt,tm,bv) ->
      let bv = Array.to_list (Array.map extern bv) in
      COrderedCase (loc,cs,option_app extern typopt,extern tm,bv)

  | RRec (_,fk,idv,tyv,bv) ->
      (match fk with
	 | RFix (nv,n) ->
	     let listdecl = 
	       Array.mapi
		 (fun i fi -> (fi,nv.(i),extern tyv.(i),extern bv.(i))) idv
	     in 
	     CFix (loc,(loc,idv.(n)),Array.to_list listdecl)
	 | RCoFix n -> 
	     let listdecl =
               Array.mapi (fun i fi -> (fi,extern tyv.(i),extern bv.(i))) idv
	     in
	     CCoFix (loc,(loc,idv.(n)),Array.to_list listdecl))

  | RSort (_,s) ->
      let s = match s with
	 | RProp _ -> s
	 | RType (Some _) when !print_universes -> s
	 | RType _ -> RType None in
      CSort (loc,s)

  | RHole (_,e) -> CHole loc

  | RCast (_,c,t) -> CCast (loc,extern c,extern t)

  | RDynamic (_,d) -> CDynamic (loc,d)
	
and factorize_prod aty = function
  | RProd (_,Name id,ty,c)
      when aty = extern ty
	& not (occur_var_constr_expr id aty) (*To avoid na in ty escapes scope*)
	-> let (nal,c) = factorize_prod aty c in ((loc,Name id)::nal,c)
  | c -> ([],extern c)

and factorize_lambda aty = function
  | RLambda (_,na,ty,c)
      when aty = extern ty
	& not (occur_name na aty) (* To avoid na in ty' escapes scope *)
	-> let (nal,c) = factorize_lambda aty c in ((loc,na)::nal,c)
  | c -> ([],extern c)

and extern_eqn (loc,ids,pl,c) =
  (loc,List.map extern_cases_pattern pl,extern c)
(*
and extern_numerals r =
  on_numeral (fun p ->
    match filter p r with
      | Some f 

and extern_symbols r =
*)

let extern_rawconstr = extern

(******************************************************************)
(* Main translation function from constr -> constr_expr *)
       
let extern_constr at_top env t =
  let t' =
    if !print_casts then t
    else Reductionops.local_strong strip_outer_cast t in
  let avoid = if at_top then ids_of_context env else [] in
  extern (Detyping.detype env avoid (names_of_rel_context env) t')

(******************************************************************)
(* Main translation function from pattern -> constr_expr *)

let rec extern_pattern tenv env = function
  | PRef ref -> CRef (extern_ref ref)

  | PVar id -> CRef (Ident (loc,id))

  | PEvar n -> extern_evar loc n

  | PRel n ->
      CRef (Ident (loc,
        try match lookup_name_of_rel n env with
	 | Name id   -> id
	 | Anonymous ->
	     anomaly "ast_of_pattern: index to an anonymous variable"
       with Not_found ->
	 id_of_string ("[REL "^(string_of_int n)^"]")))

  | PMeta None -> CHole loc

  | PMeta (Some n) -> CMeta (loc,n)

  | PApp (f,args) ->
      let (f,args) = 
	skip_coercion (function PRef r -> Some r | _ -> None)
	  (f,Array.to_list args) in
      let args = List.map (extern_pattern tenv env) args in
      (match f with
	 | PRef ref ->
	     extern_app (implicits_of_global ref) (extern_ref ref) args
	 | _       -> explicitize [] (extern_pattern tenv env f) args)

  | PSoApp (n,args) ->
      let args = List.map (extern_pattern tenv env) args in
      (* [-n] is the trick to embed a so patten into a regular application *)
      (* see constrintern.ml and g_constr.ml4 *)
      explicitize [] (CMeta (loc,-n)) args

  | PProd (Anonymous,t,c) ->
      (* Anonymous product are never factorized *)
      CArrow (loc,extern_pattern tenv env t,extern_pattern tenv env c)

  | PLetIn (na,t,c) ->
      CLetIn (loc,(loc,na),extern_pattern tenv env t,extern_pattern tenv env c)

  | PProd (na,t,c) ->
      let t = extern_pattern tenv env t in
      let (idl,c) = factorize_prod_pattern tenv (add_name na env) t c in
      CProdN (loc,[(loc,na)::idl,t],c)

  | PLambda (na,t,c) ->
      let t = extern_pattern tenv env t in
      let (idl,c) = factorize_lambda_pattern tenv (add_name na env) t c in
      CLambdaN (loc,[(loc,na)::idl,t],c)

  | PCase (cs,typopt,tm,bv) ->
      let bv = Array.to_list (Array.map (extern_pattern tenv env) bv) in
      COrderedCase
	(loc,cs,option_app (extern_pattern tenv env) typopt,
	 extern_pattern tenv env tm,bv)

  | PFix f -> extern (Detyping.detype tenv [] env (mkFix f))

  | PCoFix c -> extern (Detyping.detype tenv [] env (mkCoFix c))

  | PSort s ->
      let s = match s with
	 | RProp _ -> s
	 | RType (Some _) when !print_universes -> s
	 | RType _ -> RType None in
      CSort (loc,s)

and factorize_prod_pattern tenv env aty = function
  | PProd (Name id as na,ty,c)
      when aty = extern_pattern tenv env ty
	& not (occur_var_constr_expr id aty) (*To avoid na in ty escapes scope*)
	-> let (nal,c) = factorize_prod_pattern tenv (na::env) aty c in
	   ((loc,Name id)::nal,c)
  | c -> ([],extern_pattern tenv env c)

and factorize_lambda_pattern tenv env aty = function
  | PLambda (na,ty,c)
      when aty = extern_pattern tenv env ty
	& not (occur_name na aty) (* To avoid na in ty' escapes scope *)
	-> let (nal,c) = factorize_lambda_pattern tenv (add_name na env) aty c
           in ((loc,na)::nal,c)
  | c -> ([],extern_pattern tenv env c)
