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
open Reserve
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

let print_meta_as_hole = ref false

let with_arguments f = Options.with_option print_arguments f
let with_implicits f = Options.with_option print_implicits f
let with_coercions f = Options.with_option print_coercions f
let with_universes f = Options.with_option print_universes f
let without_symbols f = Options.with_option print_no_symbol f
let with_meta_as_hole f = Options.with_option print_meta_as_hole f

(**********************************************************************)
(* Various externalisation functions *)

let insert_delimiters e = function
  | None -> e
  | Some sc -> CDelimiters (dummy_loc,sc,e)

let insert_pat_delimiters e = function
  | None -> e
  | Some sc -> CPatDelimiters (dummy_loc,sc,e)

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

let extern_evar loc n =
  warning
    "Existential variable turned into meta-variable during externalization";
  CMeta (loc,n)

let raw_string_of_ref = function
  | ConstRef kn -> 
      "CONST("^(string_of_kn kn)^")"
  | IndRef (kn,i) ->
      "IND("^(string_of_kn kn)^","^(string_of_int i)^")"
  | ConstructRef ((kn,i),j) -> 
      "CONSTRUCT("^
      (string_of_kn kn)^","^(string_of_int i)^","^(string_of_int j)^")"
  | VarRef id -> 
      "SECVAR("^(string_of_id id)^")"

let extern_reference loc vars r =
  try Qualid (loc,shortest_qualid_of_global vars r)
  with Not_found ->
    (* happens in debugger *)
    Ident (loc,id_of_string (raw_string_of_ref r))

(**********************************************************************)
(* conversion of terms and cases patterns                             *)

let rec extern_cases_pattern_in_scope scopes vars pat =
  try 
    if !print_no_symbol then raise No_match;
    let (sc,n) = Symbols.uninterp_cases_numeral pat in
    match Symbols.availability_of_numeral sc scopes with
    | None -> raise No_match
    | Some key ->
        let loc = pattern_loc pat in
        insert_pat_delimiters (CPatNumeral (loc,n)) key
  with No_match ->
  match pat with
  | PatVar (loc,Name id) -> CPatAtom (loc,Some (Ident (loc,id)))
  | PatVar (loc,Anonymous) -> CPatAtom (loc, None) 
  | PatCstr(loc,cstrsp,args,na) ->
      let args = List.map (extern_cases_pattern_in_scope scopes vars) args in
      let p = CPatCstr
        (loc,extern_reference loc vars (ConstructRef cstrsp),args) in
      (match na with
	| Name id -> CPatAlias (loc,p,id)
	| Anonymous -> p)
	
let occur_name na aty =
  match na with
    | Name id -> occur_var_constr_expr id aty
    | Anonymous -> false

(* Implicit args indexes are in ascending order *)
let explicitize loc impl f args =
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
  if args = [] then f else CApp (loc, f, args)

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

let extern_app loc impl f args =
  if !print_implicits &
    not !print_implicits_explicit_args &
    List.exists is_status_implicit impl
  then 
    CAppExpl (loc, f, args)
  else
    explicitize loc impl (CRef f) args

let rec extern_args extern scopes env args subscopes =
  match args with
    | [] -> []
    | a::args ->
	let argscopes, subscopes = match subscopes with
	  | [] -> scopes, []
	  | scopt::subscopes -> option_cons scopt scopes, subscopes in
	extern argscopes env a :: extern_args extern scopes env args subscopes

let rec extern inctx scopes vars r =
  try 
    if !print_no_symbol then raise No_match;
    extern_numeral (Rawterm.loc r) scopes (Symbols.uninterp_numeral r)
  with No_match ->

  try 
    if !print_no_symbol then raise No_match;
    extern_symbol scopes vars r (Symbols.uninterp_notations r)
  with No_match -> match r with
  | RRef (loc,ref) -> CRef (extern_reference loc vars ref)

  | RVar (loc,id) -> CRef (Ident (loc,id))

  | REvar (loc,n) -> extern_evar loc n

  | RMeta (loc,n) -> if !print_meta_as_hole then CHole loc else CMeta (loc,n)

  | RApp (loc,f,args) ->
      let (f,args) =
	if inctx then
	  skip_coercion (function RRef(_,r) -> Some r | _ -> None) (f,args)
	else 
	  (f,args) in
      (match f with
	 | REvar (loc,ev) -> extern_evar loc ev (* we drop args *)
	 | RRef (loc,ref) ->
	     let subscopes = Symbols.find_arguments_scope ref in
	     let args = extern_args (extern true) scopes vars args subscopes in
	     extern_app loc (implicits_of_global ref)
               (extern_reference loc vars ref)
	       args
	 | _       -> 
	     explicitize loc [] (extern inctx scopes vars f)
               (List.map (extern true scopes vars) args))

  | RProd (loc,Anonymous,t,c) ->
      (* Anonymous product are never factorized *)
      CArrow (loc,extern true scopes vars t, extern true scopes vars c)

  | RLetIn (loc,na,t,c) ->
      CLetIn (loc,(loc,na),extern false scopes vars t,
              extern inctx scopes (add_vname vars na) c)

  | RProd (loc,na,t,c) ->
      let t = extern true scopes vars (anonymize_if_reserved na t) in
      let (idl,c) = factorize_prod scopes (add_vname vars na) t c in
      CProdN (loc,[(dummy_loc,na)::idl,t],c)

  | RLambda (loc,na,t,c) ->
      let t = extern true scopes vars (anonymize_if_reserved na t) in
      let (idl,c) = factorize_lambda inctx scopes (add_vname vars na) t c in
      CLambdaN (loc,[(dummy_loc,na)::idl,t],c)

  | RCases (loc,typopt,tml,eqns) ->
      let pred = option_app (extern true scopes vars) typopt in
      let tml = List.map (extern false scopes vars) tml in
      let eqns = List.map (extern_eqn (typopt<>None) scopes vars) eqns in 
      CCases (loc,pred,tml,eqns)
	
  | ROrderedCase (loc,cs,typopt,tm,bv) ->
      let bv = Array.to_list (Array.map (extern (typopt<>None) scopes vars) bv)
      in
      COrderedCase
	(loc,cs,option_app (extern true scopes vars) typopt,
         extern false scopes vars tm,bv)

  | RRec (loc,fk,idv,tyv,bv) ->
      let vars' = Array.fold_right Idset.add idv vars in
      (match fk with
	 | RFix (nv,n) ->
	     let listdecl = 
	       Array.mapi (fun i fi ->
		 (fi,nv.(i),extern false scopes vars tyv.(i),
                  extern false scopes vars' bv.(i))) idv
	     in 
	     CFix (loc,(loc,idv.(n)),Array.to_list listdecl)
	 | RCoFix n -> 
	     let listdecl =
               Array.mapi (fun i fi ->
		 (fi,extern false scopes vars tyv.(i),
                  extern false scopes vars' bv.(i))) idv
	     in
	     CCoFix (loc,(loc,idv.(n)),Array.to_list listdecl))

  | RSort (loc,s) ->
      let s = match s with
	 | RProp _ -> s
	 | RType (Some _) when !print_universes -> s
	 | RType _ -> RType None in
      CSort (loc,s)

  | RHole (loc,e) -> CHole loc

  | RCast (loc,c,t) ->
      CCast (loc,extern false scopes vars c,extern false scopes vars t)

  | RDynamic (loc,d) -> CDynamic (loc,d)
	
and factorize_prod scopes vars aty = function
  | RProd (loc,(Name id as na),ty,c)
      when aty = extern true scopes vars (anonymize_if_reserved na ty)
	& not (occur_var_constr_expr id aty) (* avoid na in ty escapes scope *)
	-> let (nal,c) = factorize_prod scopes (Idset.add id vars) aty c in
           ((loc,Name id)::nal,c)
  | c -> ([],extern true scopes vars c)

and factorize_lambda inctx scopes vars aty = function
  | RLambda (loc,na,ty,c)
      when aty = extern inctx scopes vars (anonymize_if_reserved na ty)
	& not (occur_name na aty) (* To avoid na in ty' escapes scope *)
	-> let (nal,c) =
	     factorize_lambda inctx scopes (add_vname vars na) aty c in
           ((loc,na)::nal,c)
  | c -> ([],extern inctx scopes vars c)

and extern_eqn inctx scopes vars (loc,ids,pl,c) =
  (loc,List.map (extern_cases_pattern_in_scope scopes vars) pl,
   extern inctx scopes vars c)

and extern_numeral loc scopes (sc,n) =
  match Symbols.availability_of_numeral sc scopes with
    | None -> raise No_match
    | Some key -> insert_delimiters (CNumeral (loc,n)) key

and extern_symbol scopes vars t = function
  | [] -> raise No_match
  | (keyrule,pat,n as rule)::rules ->
      let loc = Rawterm.loc t in
      try
	(* Adjusts to the number of arguments expected by the notation *)
	let (t,args) = match t,n with
	  | RApp (_,f,args), Some n when List.length args > n ->
	      let args1, args2 = list_chop n args in
	      RApp (dummy_loc,f,args1), args2
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
	      | Some (scopt,key) ->
	          let scopes = option_cons scopt scopes in
	          let l =
		    List.map (fun (c,scl) ->
		      extern (* assuming no overloading: *) true
		        (scl@scopes) vars c)
                      subst in
	          insert_delimiters (CNotation (loc,ntn,l)) key)
          | SynDefRule kn ->
              CRef (Qualid (loc, shortest_qualid_of_syndef kn)) in
 	if args = [] then e 
	else explicitize loc [] e (List.map (extern true scopes vars) args)
      with
	  No_match -> extern_symbol scopes vars t rules

let extern_rawconstr vars c = 
  extern false (Symbols.current_scopes()) vars c

let extern_cases_pattern vars p = 
  extern_cases_pattern_in_scope (Symbols.current_scopes()) vars p

(******************************************************************)
(* Main translation function from constr -> constr_expr *)

let loc = dummy_loc (* for constr and pattern, locations are lost *)

let extern_constr at_top env t =
  let vars = vars_of_env env in
  let avoid = if at_top then ids_of_context env else [] in
  extern (not at_top) (Symbols.current_scopes()) vars
    (Detyping.detype env avoid (names_of_rel_context env) t)

(******************************************************************)
(* Main translation function from pattern -> constr_expr *)

let rec extern_pattern tenv vars env = function
  | PRef ref -> CRef (extern_reference loc vars ref)

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
      let args = List.map (extern_pattern tenv vars env) args in
      (match f with
	 | PRef ref ->
	     extern_app loc (implicits_of_global ref)
               (extern_reference loc vars ref)
	       args
	 | _       -> explicitize loc [] (extern_pattern tenv vars env f) args)

  | PSoApp (n,args) ->
      let args = List.map (extern_pattern tenv vars env) args in
      (* [-n] is the trick to embed a so patten into a regular application *)
      (* see constrintern.ml and g_constr.ml4 *)
      explicitize loc [] (CMeta (loc,-n)) args

  | PProd (Anonymous,t,c) ->
      (* Anonymous product are never factorized *)
      CArrow (loc,extern_pattern tenv vars env t,
              extern_pattern tenv vars env c)

  | PLetIn (na,t,c) ->
      CLetIn (loc,(loc,na),extern_pattern tenv vars env t,
              extern_pattern tenv (add_vname vars na) (na::env) c)

  | PProd (na,t,c) ->
      let t = extern_pattern tenv vars env t in
      let (idl,c) =
        factorize_prod_pattern tenv (add_vname vars na) (na::env) t c in
      CProdN (loc,[(loc,na)::idl,t],c)

  | PLambda (na,t,c) ->
      let t = extern_pattern tenv vars env t in
      let (idl,c) =
        factorize_lambda_pattern tenv (add_vname vars na) (na::env) t c in
      CLambdaN (loc,[(loc,na)::idl,t],c)

  | PCase (cs,typopt,tm,bv) ->
      let bv = Array.to_list (Array.map (extern_pattern tenv vars env) bv) in
      COrderedCase
	(loc,cs,option_app (extern_pattern tenv vars env) typopt,
	 extern_pattern tenv vars env tm,bv)

  | PFix f ->
      extern true (Symbols.current_scopes()) vars
        (Detyping.detype tenv [] env (mkFix f))

  | PCoFix c ->
      extern true (Symbols.current_scopes()) vars
        (Detyping.detype tenv [] env (mkCoFix c))

  | PSort s ->
      let s = match s with
	 | RProp _ -> s
	 | RType (Some _) when !print_universes -> s
	 | RType _ -> RType None in
      CSort (loc,s)

and factorize_prod_pattern tenv vars env aty = function
  | PProd (Name id as na,ty,c)
      when aty = extern_pattern tenv vars env ty
      & not (occur_var_constr_expr id aty) (*To avoid na in ty escapes scope*)
	-> let (nal,c) =
          factorize_prod_pattern tenv (add_vname vars na) (na::env) aty c in
	   ((loc,Name id)::nal,c)
  | c -> ([],extern_pattern tenv vars env c)

and factorize_lambda_pattern tenv vars env aty = function
  | PLambda (na,ty,c)
      when aty = extern_pattern tenv vars env ty
	& not (occur_name na aty) (* To avoid na in ty' escapes scope *)
	-> let (nal,c) =
          factorize_lambda_pattern tenv (add_vname vars na) (na::env) aty c
        in ((loc,na)::nal,c)
  | c -> ([],extern_pattern tenv vars env c)

let extern_pattern tenv env pat =
  extern_pattern tenv (vars_of_env tenv) env pat
