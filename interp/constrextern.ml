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
open Symbols
(*i*)

(* Translation from rawconstr to front constr *)

(**********************************************************************)
(* Parametrization                                                    *)

(* This governs printing of local context of references *)
let print_arguments = ref false

(* If true, prints local context of evars, whatever print_arguments *)
let print_evar_arguments = ref false

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

(* This suppresses printing of numeral and symbols *)
let print_no_symbol = ref false

let with_option o f x =
  let old = !o in o:=true;
  try let r = f x in o := old; r
  with e -> o := old; raise e

let with_arguments f = with_option print_arguments f
let with_implicits f = with_option print_implicits f
let with_coercions f = with_option print_coercions f
let with_universes f = with_option print_universes f
let without_symbols f = with_option print_no_symbol f

(**********************************************************************)
(* Various externalisation functions *)

let insert_delimiters e = function
  | None -> e
  | Some sc -> CDelimiters (dummy_loc,sc,e)

let insert_pat_delimiters e = function
  | None -> e
  | Some sc -> CPatDelimiters (dummy_loc,sc,e)

let loc = dummy_loc (* shorter... *)

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
(* conversion of terms and cases patterns                             *)

let rec extern_cases_pattern_in_scope scopes pat =
  try 
    if !print_no_symbol then raise No_match;
    let (sc,n) = Symbols.uninterp_cases_numeral pat in
    match Symbols.availability_of_numeral sc scopes with
    | None -> raise No_match
    | Some scopt -> insert_pat_delimiters (CPatNumeral (loc,n)) scopt
  with No_match ->
  match pat with
  | PatVar (_,Name id) -> CPatAtom (loc,Some (Ident (loc,id)))
  | PatVar (_,Anonymous) -> CPatAtom (loc, None) 
  | PatCstr(_,cstrsp,args,na) ->
      let args = List.map (extern_cases_pattern_in_scope scopes) args in
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
  if (!print_implicits & not !print_implicits_explicit_args) then 
    CAppExpl (dummy_loc, f, args)
  else
    explicitize impl (CRef f) args

let rec extern_args extern scopes args subscopes =
  match args with
    | [] -> []
    | a::args ->
	let argscopes, subscopes = match subscopes with
	  | [] -> scopes, []
	  | scopt::subscopes -> option_cons scopt scopes, subscopes in
	extern argscopes a :: extern_args extern scopes args subscopes

let rec extern scopes r =
  try 
    if !print_no_symbol then raise No_match;
    extern_numeral scopes r (Symbols.uninterp_numeral r)
  with No_match ->

  try 
    if !print_no_symbol then raise No_match;
    extern_symbol scopes r (Symbols.uninterp_notations r)
  with No_match -> match r with

  | RRef (_,ref) -> CRef (extern_ref ref)

  | RVar (_,id) -> CRef (Ident (loc,id))

  | REvar (_,n) -> extern_evar loc n

  | RMeta (_,n) -> CMeta (loc,n)

  | RApp (_,f,args) ->
      let (f,args) =
	skip_coercion (function RRef(_,r) -> Some r | _ -> None) (f,args) in
      (match f with
	 | REvar (loc,ev) -> extern_evar loc ev (* we drop args *)
	 | RRef (loc,ref) ->
	     let subscopes = Symbols.find_arguments_scope ref in
	     let args = extern_args extern scopes args subscopes in
	     extern_app (implicits_of_global ref) (extern_ref ref) args
	 | _       -> 
	     explicitize [] (extern scopes f) (List.map (extern scopes) args))

  | RProd (_,Anonymous,t,c) ->
      (* Anonymous product are never factorized *)
      CArrow (loc,extern scopes t,extern scopes c)

  | RLetIn (_,na,t,c) ->
      CLetIn (loc,(loc,na),extern scopes t,extern scopes c)

  | RProd (_,na,t,c) ->
      let t = extern scopes t in
      let (idl,c) = factorize_prod scopes t c in
      CProdN (loc,[(loc,na)::idl,t],c)

  | RLambda (_,na,t,c) ->
      let t = extern scopes t in
      let (idl,c) = factorize_lambda scopes t c in
      CLambdaN (loc,[(loc,na)::idl,t],c)

  | RCases (_,typopt,tml,eqns) ->
      let pred = option_app (extern scopes) typopt in
      let tml = List.map (extern scopes) tml in
      let eqns = List.map (extern_eqn scopes) eqns in 
      CCases (loc,pred,tml,eqns)
	
  | ROrderedCase (_,cs,typopt,tm,bv) ->
      let bv = Array.to_list (Array.map (extern scopes) bv) in
      COrderedCase
	(loc,cs,option_app (extern scopes) typopt,extern scopes tm,bv)

  | RRec (_,fk,idv,tyv,bv) ->
      (match fk with
	 | RFix (nv,n) ->
	     let listdecl = 
	       Array.mapi (fun i fi ->
		 (fi,nv.(i),extern scopes tyv.(i),extern scopes bv.(i))) idv
	     in 
	     CFix (loc,(loc,idv.(n)),Array.to_list listdecl)
	 | RCoFix n -> 
	     let listdecl =
               Array.mapi (fun i fi ->
		 (fi,extern scopes tyv.(i),extern scopes bv.(i))) idv
	     in
	     CCoFix (loc,(loc,idv.(n)),Array.to_list listdecl))

  | RSort (_,s) ->
      let s = match s with
	 | RProp _ -> s
	 | RType (Some _) when !print_universes -> s
	 | RType _ -> RType None in
      CSort (loc,s)

  | RHole (_,e) -> CHole loc

  | RCast (_,c,t) -> CCast (loc,extern scopes c,extern scopes t)

  | RDynamic (_,d) -> CDynamic (loc,d)
	
and factorize_prod scopes aty = function
  | RProd (_,Name id,ty,c)
      when aty = extern scopes ty
	& not (occur_var_constr_expr id aty) (* avoid na in ty escapes scope *)
	-> let (nal,c) = factorize_prod scopes aty c in ((loc,Name id)::nal,c)
  | c -> ([],extern scopes c)

and factorize_lambda scopes aty = function
  | RLambda (_,na,ty,c)
      when aty = extern scopes ty
	& not (occur_name na aty) (* To avoid na in ty' escapes scope *)
	-> let (nal,c) = factorize_lambda scopes aty c in ((loc,na)::nal,c)
  | c -> ([],extern scopes c)

and extern_eqn scopes (loc,ids,pl,c) =
  (loc,List.map (extern_cases_pattern_in_scope scopes) pl,extern scopes c)

and extern_numeral scopes t (sc,n) =
  match Symbols.availability_of_numeral sc scopes with
    | None -> raise No_match
    | Some scopt -> insert_delimiters (CNumeral (loc,n)) scopt

and extern_symbol scopes t = function
  | [] -> raise No_match
  | (keyrule,pat,n as rule)::rules ->
      try
	(* Adjusts to the number of arguments expected by the notation *)
	let (t,args) = match t,n with
	  | RApp (_,f,args), Some n when List.length args > n ->
	      let args1, args2 = list_chop n args in
	      RApp (loc,f,args1), args2
	  | _ -> t,[] in
	(* Try matching ... *)
	let subst = match_aconstr t pat in
	(* Try availability of interpretation ... *)
        let e =
          match keyrule with
          | NotationRule (sc,ntn) ->
	      (match Symbols.availability_of_notation (sc,ntn) scopes with
                  (* Uninterpretation is not allowed in current context *)
              | None -> raise No_match
                  (* Uninterpretation is allowed in current context *)
	      | Some scopt ->
	          let scopes = option_cons scopt scopes in
	          let l = list_map_assoc (extern scopes) subst in
	          insert_delimiters (CNotation (loc,ntn,l)) scopt)
          | SynDefRule kn ->
              CRef (Qualid (loc, shortest_qualid_of_syndef kn)) in
 	if args = [] then e 
	else explicitize [] e (List.map (extern scopes) args)
      with
	  No_match -> extern_symbol scopes t rules

let extern_rawconstr = 
  extern (Symbols.current_scopes())

let extern_cases_pattern = 
  extern_cases_pattern_in_scope (Symbols.current_scopes())

(******************************************************************)
(* Main translation function from constr -> constr_expr *)
       
let extern_constr at_top env t =
  let avoid = if at_top then ids_of_context env else [] in
  extern (Symbols.current_scopes())
    (Detyping.detype env avoid (names_of_rel_context env) t)

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

  | PFix f ->
      extern (Symbols.current_scopes()) (Detyping.detype tenv [] env (mkFix f))

  | PCoFix c ->
      extern (Symbols.current_scopes())
        (Detyping.detype tenv [] env (mkCoFix c))

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
