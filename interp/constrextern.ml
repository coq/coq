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

(* For the translator *)
let temporary_implicits_out = ref []
let set_temporary_implicits_out l = temporary_implicits_out := l
let get_temporary_implicits_out id =
  try List.assoc id !temporary_implicits_out
  with Not_found -> []

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
  CPatVar (loc,(false,make_ident "META" (Some n)))

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

(* v7->v8 translation *)

let is_coq_root d =
  let d = repr_dirpath d in d <> [] & string_of_id (list_last d) = "Coq"

let is_module m =
  let d = repr_dirpath (Lib.library_dp()) in
  d <> [] & string_of_id (List.hd d) = m

let translate_v7_string = function
  (* ZArith *)
  | "double_moins_un" -> "double_minus_one"
  | "double_moins_deux" -> "double_minus_two"
  | "entier" -> "N"
  | "SUPERIEUR" -> "GREATER"
  | "EGAL" -> "EQUAL"
  | "INFERIEUR" -> "LESS"
  | "add" -> "Padd"
  | "times" when not (is_module "Mapfold") -> "Pmult"
  | "true_sub" -> "Psub"
  | "add_un" -> "Padd_one"
  | "sub_un" -> "Psub_one"
  | "sub_pos" -> "PNsub"
  | "sub_neg" -> "PNsub_carry"
  | "convert_add_un" -> "convert_Padd_one"
  | "compare_convert_INFERIEUR" -> "compare_convert_LESS"
  | "compare_convert_SUPERIEUR" -> "compare_convert_GREATER"
  | "compare_convert_EGAL"      -> "compare_convert_EQUAL"
  | "convert_compare_INFERIEUR" -> "convert_compare_LESS"
  | "convert_compare_SUPERIEUR" -> "convert_compare_GREATER"
  | "convert_compare_EGAL"      -> "convert_compare_EQUAL"
  | "Zcompare_EGAL"             -> "Zcompare_EQUAL"
  | "Nul" -> "Null"
  | "Un_suivi_de" -> "double_plus_one"
  | "Zero_suivi_de" -> "double"
  | "is_double_moins_un" -> "is_double_minus_one"
  | "Zplus_sym" -> "Zplus_comm"
  | "Zmult_sym" -> "Zmult_comm"
  | "sub_pos_SUPERIEUR" -> "sub_pos_GREATER"
  | "inject_nat" -> "INZ"
  | "convert" -> "IPN"
  | "anti_convert" -> "INP"
  | "convert_intro" -> "IPN_inj"
  | "convert_add" -> "IPN_add"
  | "convert_add_carry" -> "IPN_add_carry"
  | "compare_convert_O" -> "lt_O_IPN"
  | "Zopp_intro" -> "Zopp_inj"
  (* Arith *)
  | "plus_sym" -> "plus_comm"
  | "mult_sym" -> "mult_comm"
  | "max_sym" -> "max_comm"
  | "min_sym" -> "min_comm"
  | "gt_not_sym" -> "gt_asym"
  | "fact_growing" -> "fact_le"
  (* Lists *)
  | "idempot_rev" -> "involutive_rev"
  (* Bool *)
  | "orb_sym" -> "orb_comm"
  | "andb_sym" -> "andb_comm"
  (* Reals *)
    (* redundant *)
  | "Rle_sym1" -> "Rle_ge"
  | "Rmin_sym" -> "Rmin_comm"
  | s when String.length s >= 7 & 
      let s' = String.sub s 0 7 in
      (s' = "unicite" or s' = "unicity") ->
      "uniqueness"^(String.sub s 7 (String.length s - 7))
  (* Default *)
  | x -> x

let id_of_v7_string s =
  id_of_string (if !Options.v7 then s else translate_v7_string s)

let v7_to_v8_dir_id dir id =
  if Options.do_translate()
    & (is_coq_root (Lib.library_dp()) or is_coq_root dir)
  then id_of_string (translate_v7_string (string_of_id id)) else id

let v7_to_v8_id = v7_to_v8_dir_id empty_dirpath

let shortest_qualid_of_v7_global ctx ref =
  let fulldir,_ = repr_path (sp_of_global ref) in
  let dir,id = repr_qualid (shortest_qualid_of_global ctx ref) in
  make_qualid dir (v7_to_v8_dir_id fulldir id)

let extern_reference loc vars r =
  try Qualid (loc,shortest_qualid_of_v7_global vars r)
  with Not_found ->
    (* happens in debugger *)
    Ident (loc,id_of_string (raw_string_of_ref r))

(**********************************************************************)
(* conversion of terms and cases patterns                             *)

let make_current_scope (scopt,scopes) = option_cons scopt scopes

let rec extern_cases_pattern_in_scope scopes vars pat =
  try 
    if !print_no_symbol then raise No_match;
    let (sc,n) = Symbols.uninterp_cases_numeral pat in
    match Symbols.availability_of_numeral sc (make_current_scope scopes) with
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

let is_projection nargs = function
  | Some r -> 
      (try Recordops.find_projection_nparams r + 1 = nargs
       with Not_found -> false)
  | None ->
      false

(* Implicit args indexes are in ascending order *)
(* inctx is useful only if there is a last argument to be deduced from ctxt *)
let explicitize loc inctx impl (cf,f) args =
  let n = List.length args in
  let rec exprec q = function
    | a::args, imp::impl when is_status_implicit imp ->
        let tail = exprec (q+1) (args,impl) in
        let visible =
          (!print_implicits & !print_implicits_explicit_args)
          or not (is_inferable_implicit inctx n imp)
          or ((match a with CHole _ -> false | _ -> true)
              & Options.do_translate()) in
        if visible then (a,Some q) :: tail else tail
    | a::args, _::impl -> (a,None) :: exprec (q+1) (args,impl)
    | args, [] -> List.map (fun a -> (a,None)) args (*In case of polymorphism*)
    | [], _ -> [] in
  let isproj = is_projection (List.length args) cf in
  let args = exprec 1 (args,impl) in
  if args = [] then f else CApp (loc, (isproj, f), args)

let rec skip_coercion dest_ref (f,args as app) =
  if !print_coercions or Options.do_translate () then app
  else
    try
      match dest_ref f with
	| Some r ->
	    (match Classops.hide_coercion r with
	       | Some n ->
		   if n >= List.length args then app
		   else (* We skip a coercion *)
		     let fargs = list_skipn n args in
	       	     skip_coercion dest_ref (List.hd fargs,List.tl fargs)
	       | None -> app)
	| None -> app
    with Not_found -> app

let extern_app loc inctx impl (cf,f) args =
  if !print_implicits &
    not !print_implicits_explicit_args &
    List.exists is_status_implicit impl
  then 
    if args = [] (* maybe caused by a hidden coercion *) then CRef f 
    else CAppExpl (loc, (is_projection (List.length args) cf, f), args)
  else
    explicitize loc inctx impl (cf,CRef f) args

let rec extern_args extern scopes env args subscopes =
  match args with
    | [] -> []
    | a::args ->
	let argscopes, subscopes = match subscopes with
	  | [] -> (None,scopes), []
	  | scopt::subscopes -> (scopt,scopes), subscopes in
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

  | RVar (loc,id) -> CRef (Ident (loc,v7_to_v8_id id))

  | REvar (loc,n) -> extern_evar loc n

  | RPatVar (loc,n) -> if !print_meta_as_hole then CHole loc else CPatVar (loc,n)

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
	     let args =
	       extern_args (extern true) (snd scopes) vars args subscopes in
	     extern_app loc inctx (implicits_of_global_out ref)
               (Some ref,extern_reference loc vars ref)
	       args
	 | RVar (loc,id) -> (* useful for translation of inductive *)
	     let args = List.map (extern true scopes vars) args in
	     extern_app loc inctx (get_temporary_implicits_out id)
	       (None,Ident (loc,v7_to_v8_id id))
	       args
	 | _       -> 
	     explicitize loc inctx [] (None,extern false scopes vars f)
               (List.map (extern true scopes vars) args))

  | RProd (loc,Anonymous,t,c) ->
      (* Anonymous product are never factorized *)
      CArrow (loc,extern_type scopes vars t, extern_type scopes vars c)

  | RLetIn (loc,na,t,c) ->
      CLetIn (loc,(loc,na),extern false scopes vars t,
              extern inctx scopes (add_vname vars na) c)

  | RProd (loc,na,t,c) ->
      let t = extern_type scopes vars (anonymize_if_reserved na t) in
      let (idl,c) = factorize_prod scopes (add_vname vars na) t c in
      CProdN (loc,[(dummy_loc,na)::idl,t],c)

  | RLambda (loc,na,t,c) ->
      let t = extern_type scopes vars (anonymize_if_reserved na t) in
      let (idl,c) = factorize_lambda inctx scopes (add_vname vars na) t c in
      CLambdaN (loc,[(dummy_loc,na)::idl,t],c)

  | RCases (loc,typopt,tml,eqns) ->
      let pred = option_app (extern_type scopes vars) typopt in
      let tml = List.map (extern false scopes vars) tml in
      let eqns = List.map (extern_eqn (typopt<>None) scopes vars) eqns in 
      CCases (loc,pred,tml,eqns)
	
  | ROrderedCase (loc,cs,typopt,tm,bv) ->
      let bv = Array.to_list (Array.map (extern (typopt<>None) scopes vars) bv)
      in
      COrderedCase
	(loc,cs,option_app (extern_type scopes vars) typopt,
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
      CCast (loc,extern false scopes vars c,extern_type scopes vars t)

  | RDynamic (loc,d) -> CDynamic (loc,d)

and extern_type (_,scopes) = extern true (Some Symbols.type_scope,scopes)

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
  match Symbols.availability_of_numeral sc (make_current_scope scopes) with
    | None -> raise No_match
    | Some key -> insert_delimiters (CNumeral (loc,n)) key

and extern_symbol (tmp_scope,scopes as allscopes) vars t = function
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
	      let scopes' = option_cons tmp_scope scopes in
	      (match Symbols.availability_of_notation (sc,ntn) scopes' with
                  (* Uninterpretation is not allowed in current context *)
              | None -> raise No_match
                  (* Uninterpretation is allowed in current context *)
	      | Some (scopt,key) ->
	          let scopes = option_cons scopt scopes in
	          let l =
		    List.map (fun (c,(scopt,scl)) ->
		      extern (* assuming no overloading: *) true
		        (scopt,scl@scopes) vars c)
                      subst in
	          insert_delimiters (CNotation (loc,ntn,l)) key)
          | SynDefRule kn ->
              CRef (Qualid (loc, shortest_qualid_of_syndef kn)) in
 	if args = [] then e 
	else
	  (* TODO: compute scopt for the extra args, in case, head is a ref *)
	  explicitize loc false [] (None,e)
	  (List.map (extern true allscopes vars) args)
      with
	  No_match -> extern_symbol allscopes vars t rules

let extern_rawconstr vars c = 
  extern false (None,Symbols.current_scopes()) vars c

let extern_cases_pattern vars p = 
  extern_cases_pattern_in_scope (None,Symbols.current_scopes()) vars p

(******************************************************************)
(* Main translation function from constr -> constr_expr *)

let loc = dummy_loc (* for constr and pattern, locations are lost *)

let extern_constr at_top env t =
  let vars = vars_of_env env in
  let avoid = if at_top then ids_of_context env else [] in
  extern (not at_top) (None,Symbols.current_scopes()) vars
    (Detyping.detype env avoid (names_of_rel_context env) t)

(******************************************************************)
(* Main translation function from pattern -> constr_expr *)

let rec raw_of_pat tenv env = function
  | PRef ref -> RRef (loc,ref)
  | PVar id -> RVar (loc,id)
  | PEvar n -> REvar (loc,n)
  | PRel n ->
      let id = try match lookup_name_of_rel n env with
	| Name id   -> id
	| Anonymous ->
	    anomaly "rawconstr_of_pattern: index to an anonymous variable"
      with Not_found -> id_of_string ("[REL "^(string_of_int n)^"]") in
      RVar (loc,id)
  | PMeta None -> RHole (loc,InternalHole)
  | PMeta (Some n) -> RPatVar (loc,(false,n))
  | PApp (f,args) ->
      RApp (loc,raw_of_pat tenv env f,array_map_to_list (raw_of_pat tenv env) args)
  | PSoApp (n,args) ->
      RApp (loc,RPatVar (loc,(true,n)),
        List.map (raw_of_pat tenv env) args)
  | PProd (na,t,c) ->
      RProd (loc,na,raw_of_pat tenv env t,raw_of_pat tenv (na::env) c)
  | PLetIn (na,t,c) ->
      RLetIn (loc,na,raw_of_pat tenv env t, raw_of_pat tenv (na::env) c)
  | PLambda (na,t,c) ->
      RLambda (loc,na,raw_of_pat tenv env t, raw_of_pat tenv (na::env) c)
  | PCase ((_,(IfStyle|LetStyle as cs)),typopt,tm,bv) ->
      ROrderedCase (loc,cs,option_app (raw_of_pat tenv env) typopt,
         raw_of_pat tenv env tm,Array.map (raw_of_pat tenv env) bv)
  | PCase ((_,cs),typopt,tm,[||]) ->
      RCases (loc,option_app (raw_of_pat tenv env) typopt,
         [raw_of_pat tenv env tm],[])
  | PCase ((Some ind,cs),typopt,tm,bv) ->
      let avoid = List.fold_right (name_fold (fun x l -> x::l)) env [] in
      Detyping.detype_case false
	(fun tenv _ -> raw_of_pat tenv)
	(fun tenv _ -> raw_of_eqn tenv)
	tenv avoid env ind cs typopt tm bv
  | PCase _ -> error "Unsupported case-analysis while printing pattern"
  | PFix f -> Detyping.detype tenv [] env (mkFix f)
  | PCoFix c -> Detyping.detype tenv [] env (mkCoFix c)
  | PSort s -> RSort (loc,s)

and raw_of_eqn tenv env constr construct_nargs branch =
  let make_pat x env b ids =
    let avoid = List.fold_right (name_fold (fun x l -> x::l)) env [] in
    let id = next_name_away_with_default "x" x avoid in
    PatVar (dummy_loc,Name id),(Name id)::env,id::ids
  in
  let rec buildrec ids patlist env n b =
    if n=0 then
      (dummy_loc, ids, 
       [PatCstr(dummy_loc, constr, List.rev patlist,Anonymous)],
       raw_of_pat tenv env b)
    else
      match b with
	| PLambda (x,_,b) -> 
	    let pat,new_env,new_ids = make_pat x env b ids in
            buildrec new_ids (pat::patlist) new_env (n-1) b

	| PLetIn (x,_,b) -> 
	    let pat,new_env,new_ids = make_pat x env b ids in
            buildrec new_ids (pat::patlist) new_env (n-1) b

	| _ ->
	    error "Unsupported branch in case-analysis while printing pattern"
  in 
  buildrec [] [] env construct_nargs branch

let extern_pattern tenv env pat =
  extern true (None,Symbols.current_scopes()) Idset.empty
    (raw_of_pat tenv env pat)
