(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Pp
open Util
open Options
open Names
open Nameops
open Libnames
open Impargs
open Rawterm
open Pattern
open Pretyping
open Topconstr
open Nametab
open Symbols

type implicits_env = (identifier * Impargs.implicits_list) list

let interning_grammar = ref false

let for_grammar f x =
  interning_grammar := true;
  let a = f x in
  interning_grammar := false;
  a

(* For the translator *)
let temporary_implicits_in = ref []
let set_temporary_implicits_in l = temporary_implicits_in := l

(**********************************************************************)
(* Internalisation errors                                             *)

type internalisation_error =
  | VariableCapture of identifier
  | WrongExplicitImplicit
  | NegativeMetavariable
  | NotAConstructor of reference
  | UnboundFixName of bool * identifier
  | NonLinearPattern of identifier
  | BadPatternsNumber of int * int
  | BadExplicitationNumber of int * int option

exception InternalisationError of loc * internalisation_error

let explain_variable_capture id =
  str "The variable " ++ pr_id id ++ str " occurs in its type"

let explain_wrong_explicit_implicit =
  str "Found an explicitly given implicit argument but was expecting" ++
  fnl () ++ str "a regular one"

let explain_negative_metavariable =
  str "Metavariable numbers must be positive"

let explain_not_a_constructor ref =
  str "Unknown constructor: " ++ pr_reference ref

let explain_unbound_fix_name is_cofix id =
  str "The name" ++ spc () ++ pr_id id ++ 
  spc () ++ str "is not bound in the corresponding" ++ spc () ++
  str (if is_cofix then "co" else "") ++ str "fixpoint definition"

let explain_non_linear_pattern id =
  str "The variable " ++ pr_id id ++ str " is bound several times in pattern"

let explain_bad_patterns_number n1 n2 =
  let s = if n1 > 1 then "s" else "" in
  str "Expecting " ++ int n1 ++ str " pattern" ++ str s ++ str " but found "
    ++ int n2

let explain_bad_explicitation_number n po =
  let s = match po with
    | None -> "a regular argument"
    | Some p -> string_of_int p in
  str "Bad explicitation number: found " ++ int n ++ 
  str" but was expecting " ++ str s

let explain_internalisation_error = function
  | VariableCapture id -> explain_variable_capture id
  | WrongExplicitImplicit -> explain_wrong_explicit_implicit
  | NegativeMetavariable -> explain_negative_metavariable
  | NotAConstructor ref -> explain_not_a_constructor ref
  | UnboundFixName (iscofix,id) -> explain_unbound_fix_name iscofix id
  | NonLinearPattern id -> explain_non_linear_pattern id
  | BadPatternsNumber (n1,n2) -> explain_bad_patterns_number n1 n2
  | BadExplicitationNumber (n,po) -> explain_bad_explicitation_number n po

let error_unbound_patvar loc n =
  user_err_loc
    (loc,"glob_qualid_or_patvar", str "?" ++ pr_patvar n ++ 
      str " is unbound")

(**********************************************************************)
(* Dump of globalization (to be used by coqdoc)                       *)

let add_glob loc ref = 
(*i
  let sp = Nametab.sp_of_global (Global.env ()) ref in
  let dir,_ = repr_path sp in
  let rec find_module d = 
    try 
      let qid = let dir,id = split_dirpath d in make_qualid dir id in
      let _ = Nametab.locate_loaded_library qid in d
    with Not_found -> find_module (dirpath_prefix d) 
  in
  let s = string_of_dirpath (find_module dir) in
  i*)
  let sp = Nametab.sp_of_global ref in
  let id = let _,id = repr_path sp in string_of_id id in
  let dp = string_of_dirpath (Declare.library_part ref) in
  dump_string (Printf.sprintf "R%d %s.%s\n" (fst loc) dp id)

(**********************************************************************)
(* Remembering the parsing scope of variables in notations            *)

let make_current_scope (scopt,scopes) = option_cons scopt scopes

let set_var_scope loc id (_,_,scopt,scopes) (_,_,varscopes) =
  try 
    let idscopes = List.assoc id varscopes in
    if !idscopes <> None & 
      make_current_scope (out_some !idscopes)
      <> make_current_scope (scopt,scopes) then
      user_err_loc (loc,"set_var_scope",
        pr_id id ++ str " already occurs in a different scope")
    else
      idscopes := Some (scopt,scopes)
  with Not_found ->
    if_verbose warning ("Could not globalize " ^ (string_of_id id))

(**********************************************************************)
(* Discriminating between bound variables and global references       *)

(* [vars1] is a set of name to avoid (used for the tactic language);
   [vars2] is the set of global variables, env is the set of variables
   abstracted until this point *)

let intern_var (env,impls,_,_) ((vars1,unbndltacvars),vars2,_) loc id =
  (* Is [id] bound in current env or ltac vars bound to constr *)
  if Idset.mem id env or List.mem id vars1
  then
    RVar (loc,id), (try List.assoc id impls with Not_found -> []), []
  else
  (* Is [id] bound to a free name in ltac (this is an ltac error message) *)
  try
    match List.assoc id unbndltacvars with
      | None -> user_err_loc (loc,"intern_var",
	  pr_id id ++ str " ist not bound to a term")
      | Some id0 -> Pretype_errors.error_var_not_found_loc loc id0
  with Not_found ->
  (* Is [id] a section variable *)
  let _ = Sign.lookup_named id vars2 in
  (* Car Fixpoint met les fns définies temporairement comme vars de sect *)
  let imps, args_scopes =
    try
      let ref = VarRef id in
      implicits_of_global ref, find_arguments_scope ref
    with _ -> [], [] in
  RRef (loc, VarRef id), imps, args_scopes

(* Is it a global reference or a syntactic definition? *)
let intern_qualid loc qid =
  try match Nametab.extended_locate qid with
  | TrueGlobal ref ->
    if !dump then add_glob loc ref;
    RRef (loc, ref), implicits_of_global ref, find_arguments_scope ref
  | SyntacticDef sp ->
      (Syntax_def.search_syntactic_definition loc sp),[],[]
  with Not_found ->
    error_global_not_found_loc loc qid

let intern_reference env lvar = function
  | Qualid (loc, qid) ->
      intern_qualid loc qid
  | Ident (loc, id) ->
      (* For old ast syntax compatibility *)
      if (string_of_id id).[0] = '$' then RVar (loc,id),[],[] else
      (* End old ast syntax compatibility *)
      (* Pour traduction des implicites d'inductifs et points-fixes *)
      try RVar (loc,id), List.assoc id !temporary_implicits_in, []
      with Not_found ->
      (* Fin pour traduction *)
      try intern_var env lvar loc id
      with Not_found -> 
      try intern_qualid loc (make_short_qualid id)
      with e ->
	(* Extra allowance for grammars *)
	if !interning_grammar then begin
	  set_var_scope loc id env lvar;
	  RVar (loc,id), [], []
	end
	else raise e

let interp_reference vars r =
  let (r,_,_) = intern_reference (Idset.empty,[],None,[]) (vars,[],[]) r in r

let apply_scope_env (ids,impls,_,scopes as env) = function
  | [] -> (ids,impls,None,scopes), []
  | sc::scl -> (ids,impls,sc,scopes), scl

let rec adjust_scopes env scopes = function
  | [] -> []
  | a::args ->
      let (enva,scopes) = apply_scope_env env scopes in
      enva :: adjust_scopes env scopes args

let rec simple_adjust_scopes = function
  | _,[] -> []
  | [],_::args -> None :: simple_adjust_scopes ([],args)
  | sc::scopes,_::args -> sc :: simple_adjust_scopes (scopes,args)

(**********************************************************************)
(* Cases                                                              *)

(* Check linearity of pattern-matching *)
let rec has_duplicate = function 
  | [] -> None
  | x::l -> if List.mem x l then (Some x) else has_duplicate l

let loc_of_lhs lhs = 
 join_loc (cases_pattern_loc (List.hd lhs)) (cases_pattern_loc (list_last lhs))

let check_linearity lhs ids =
  match has_duplicate ids with
    | Some id ->
	raise (InternalisationError (loc_of_lhs lhs,NonLinearPattern id))
    | None ->
	()

(* Warns if some pattern variable starts with uppercase *)
let check_uppercase loc ids =
(* A quoi ça sert ? Pour l'extraction vers ML ? Maintenant elle est externe
  let is_uppercase_var v =
    match (string_of_id v).[0] with 'A'..'Z' -> true | _  -> false
  in
  let warning_uppercase loc uplid =
    let vars = h 0 (prlist_with_sep pr_coma pr_id uplid) in
    let (s1,s2) = if List.length uplid = 1 then (" ","s ") else ("s "," ") in
    warn (str ("the variable"^s1) ++ vars ++
	  str (" start"^s2^"with an upper case letter in pattern")) in
  let uplid = List.filter is_uppercase_var ids in
  if uplid <> [] then warning_uppercase loc uplid
*)
  ()

(* Match the number of pattern against the number of matched args *)
let check_number_of_pattern loc n l =
  let p = List.length l in
  if n<>p then raise (InternalisationError (loc,BadPatternsNumber (n,p)))

(* Manage multiple aliases *)

  (* [merge_aliases] returns the sets of all aliases encountered at this
     point and a substitution mapping extra aliases to the first one *)
let merge_aliases (ids,subst as aliases) id =
  ids@[id], if ids=[] then subst else (id, List.hd ids)::subst

let alias_of = function
  | ([],_) -> Anonymous
  | (id::_,_) -> Name id

let message_redundant_alias (id1,id2) =
  if_verbose warning 
   ("Alias variable "^(string_of_id id1)^" is merged with "^(string_of_id id2))

(* Differentiating between constructors and matching variables *)
type pattern_qualid_kind =
  | ConstrPat of constructor
  | VarPat of identifier

let find_constructor ref =
  let (loc,qid) = qualid_of_reference ref in
  try match extended_locate qid with
    | SyntacticDef sp ->
	(match Syntax_def.search_syntactic_definition loc sp with
	  | RRef (_,(ConstructRef c as x)) ->
	      if !dump then add_glob loc x; 
 	      c
	  | _ ->
	      raise (InternalisationError (loc,NotAConstructor ref)))
    | TrueGlobal r ->
        let rec unf = function
          | ConstRef cst ->
              (try
		let v = Environ.constant_value (Global.env()) cst in
                unf (reference_of_constr v)
              with
                  Environ.NotEvaluableConst _ | Not_found ->
		    raise (InternalisationError (loc,NotAConstructor ref)))
          | ConstructRef c -> 
	      if !dump then add_glob loc r; 
	      c
          | _ -> raise (InternalisationError (loc,NotAConstructor ref))
        in unf r
  with Not_found ->
    raise (InternalisationError (loc,NotAConstructor ref))

let find_pattern_variable = function
  | Ident (loc,id) -> id
  | Qualid (loc,_) as x -> raise (InternalisationError(loc,NotAConstructor x))

let maybe_constructor ref =
  try ConstrPat (find_constructor ref)
  with InternalisationError _ -> VarPat (find_pattern_variable ref)

let rec intern_cases_pattern scopes aliases tmp_scope = function
  | CPatAlias (loc, p, id) ->
      let aliases' = merge_aliases aliases id in
      intern_cases_pattern scopes aliases' tmp_scope p
  | CPatCstr (loc, head, pl) ->
      let c = find_constructor head in
      let argscs =
	simple_adjust_scopes (find_arguments_scope (ConstructRef c), pl) in
      let (idsl,pl') =
	List.split (List.map2 (intern_cases_pattern scopes ([],[])) argscs pl)
      in
      (aliases::(List.flatten idsl), PatCstr (loc,c,pl',alias_of aliases))
  | CPatNumeral (loc, n) ->
      let scopes = option_cons tmp_scope scopes in
      ([aliases],
      Symbols.interp_numeral_as_pattern loc n (alias_of aliases) scopes)
  | CPatDelimiters (loc, key, e) ->
      intern_cases_pattern (find_delimiters_scope loc key::scopes)
        aliases None e
  | CPatAtom (loc, Some head) ->
      (match maybe_constructor head with
	 | ConstrPat c ->
	     ([aliases], PatCstr (loc,c,[],alias_of aliases))
	 | VarPat id ->
	     let aliases = merge_aliases aliases id in
	     ([aliases], PatVar (loc,alias_of aliases)))
  | CPatAtom (loc, None) ->
      ([aliases], PatVar (loc,alias_of aliases))

(**********************************************************************)
(* Fix and CoFix                                                      *)

let rec intern_fix = function
  | [] -> ([],[],[],[])
  | (fi, n, c, t)::rest->
      let (lf,ln,lc,lt) = intern_fix rest in
      (fi::lf, n::ln, c::lc, t::lt)

let rec intern_cofix = function
  | [] -> ([],[],[])
  | (fi, c, t)::rest -> 
      let (lf,lc,lt) = intern_cofix rest in
      (fi::lf, c::lc, t::lt)

(**********************************************************************)
(* Utilities for binders                                              *)

let check_capture loc ty = function
  | Name id when occur_var_constr_expr id ty ->
      raise (InternalisationError (loc,VariableCapture id))
  | _ ->
      ()

let locate_if_isevar loc na = function
  | RHole _ -> 
      (try match na with
	| Name id ->  Reserve.find_reserved_type id
	| Anonymous -> raise Not_found 
      with Not_found -> RHole (loc, BinderType na))
  | x -> x

(**********************************************************************)
(* Utilities for application                                          *)


let check_projection nargs = function
  | RRef (loc, ref) ->
      (try
	let n = Recordops.find_projection_nparams ref in
	if nargs <> n+1 then 
	  user_err_loc (loc,"",str "Projection has not enough parameters");
      with Not_found -> 
	user_err_loc
	(loc,"",pr_global_env Idset.empty ref ++ str " is not a registered projection"))
  | r -> user_err_loc (loc_of_rawconstr r, "", str "Not a projection")

let set_hole_implicit i = function
  | RRef (loc,r) -> (loc,ImplicitArg (r,i))
  | RVar (loc,id) -> (loc,ImplicitArg (VarRef id,i))
  | _ -> anomaly "Only refs have implicits"

(**********************************************************************)
(* Syntax extensions                                                  *)

let coerce_to_id = function
  | CRef (Ident (_,id)) -> id 
  | c ->
      user_err_loc (constr_loc c, "subst_rawconstr",
        str"This expression should be a simple identifier")

let traverse_binder subst id (ids,impls,tmpsc,scopes as env) =
  let id = try coerce_to_id (fst (List.assoc id subst)) with Not_found -> id in
  id,(Idset.add id ids,impls,tmpsc,scopes)

type ameta_scope =
  | RefArg of (global_reference * int) list
  | TypeArg

let rec subst_rawconstr loc interp subst (ids,impls,_,scopes as env) = function
  | AVar id ->
      let (a,(scopt,subscopes)) =
	(* subst remembers the delimiters stack in the interpretation *)
	(* of the notations *)
	try List.assoc id subst
	with Not_found -> (CRef (Ident (loc,id)),(None,[])) in
      let env = (ids,impls,scopt,subscopes@scopes) in
      interp env a
(*
  | AApp (ARef ref,args) ->
      let argscopes = find_arguments_scope ref in
      let argsenv = adjust_scopes env argscopes args in
      RApp (loc,RRef (loc,ref),
        List.map2 (subst_rawconstr loc interp subst) argsenv args)
	(* TODO: adjust type_scope for lambda, annotations, etc *)
*)
  | t ->
      map_aconstr_with_binders_loc loc (traverse_binder subst)
      (subst_rawconstr loc interp subst) (ids,impls,None,scopes) t

let set_type_scope (ids,impls,tmp_scope,scopes) =
  (ids,impls,Some Symbols.type_scope,scopes)

(**********************************************************************)
(* Main loop                                                          *)

let internalise sigma env allow_soapp lvar c =
  let rec intern (ids,impls,tmp_scope,scopes as env) = function
    | CRef ref as x ->
	let (c,imp,subscopes) = intern_reference env lvar ref in
	(match intern_impargs c env imp subscopes [] with
          | [] -> c
          | l -> RApp (constr_loc x, c, l))
    | CFix (loc, (locid,iddef), ldecl) ->
	let (lf,ln,lc,lt) = intern_fix ldecl in
	let n =
	  try
	    (list_index iddef lf) -1
          with Not_found ->
	    raise (InternalisationError (locid,UnboundFixName (false,iddef)))
	in
	let ids' = List.fold_right Idset.add lf ids in
	let defl =
	  Array.of_list (List.map (intern (ids',impls,None,scopes)) lt) in
	let arityl = Array.of_list (List.map (intern_type env) lc) in
	RRec (loc,RFix (Array.of_list ln,n), Array.of_list lf, arityl, defl)
    | CCoFix (loc, (locid,iddef), ldecl) ->
	let (lf,lc,lt) = intern_cofix ldecl in
	let n =
          try 
	    (list_index iddef lf) -1
          with Not_found ->
	    raise (InternalisationError (locid,UnboundFixName (true,iddef)))
	in
	let ids' = List.fold_right Idset.add lf ids in
	let defl =
	  Array.of_list (List.map (intern (ids',impls,None,scopes)) lt) in
	let arityl = Array.of_list (List.map (intern_type env) lc) in
	RRec (loc,RCoFix n, Array.of_list lf, arityl, defl)
    | CArrow (loc,c1,c2) ->
        RProd (loc, Anonymous, intern_type env c1, intern_type env c2)
    | CProdN (loc,[],c2) ->
        intern_type env c2
    | CProdN (loc,(nal,ty)::bll,c2) ->
        iterate_prod loc env ty (CProdN (loc, bll, c2)) nal
    | CLambdaN (loc,[],c2) ->
        intern env c2
    | CLambdaN (loc,(nal,ty)::bll,c2) ->
	iterate_lam loc env ty (CLambdaN (loc, bll, c2)) nal
    | CLetIn (loc,(_,na),c1,c2) ->
	RLetIn (loc, na, intern env c1,
          intern (name_fold Idset.add na ids,impls,tmp_scope,scopes) c2)
    | CNotation (loc,"- _",[CNumeral(_,Bignat.POS p)]) ->
	let scopes = option_cons tmp_scope scopes in
        Symbols.interp_numeral loc (Bignat.NEG p) scopes
    | CNotation (loc,ntn,args) ->
	let scopes = option_cons tmp_scope scopes in
	let (ids,c) = Symbols.interp_notation ntn scopes in
	let subst = List.map2 (fun (id,scl) a -> (id,(a,scl))) ids args in
	subst_rawconstr loc intern subst env c
    | CNumeral (loc, n) ->
	let scopes = option_cons tmp_scope scopes in
	Symbols.interp_numeral loc n scopes
    | CDelimiters (loc, key, e) ->
	intern (ids,impls,None,find_delimiters_scope loc key::scopes) e
    | CAppExpl (loc, (isproj,ref), args) ->
        let (f,_,args_scopes) = intern_reference env lvar ref in
	if isproj then check_projection (List.length args) f;
	RApp (loc, f, intern_args env args_scopes args)
    | CApp (loc, (isproj,f), args) ->
	let (c, impargs, args_scopes) =
	  match f with
	    | CRef ref -> intern_reference env lvar ref
	    | _ -> (intern env f, [], [])
        in
	let args = intern_impargs c env impargs args_scopes args in
	if isproj then check_projection (List.length args) c;
	(match c with 
	  | RApp (loc', f', args') ->
	      (* May happen with the ``...`` and `...` grammars *)
	      RApp (join_loc loc' loc, f',args'@args)
	  | _ -> RApp (loc, c, args))
    | CCases (loc, po, tms, eqns) ->
	RCases (loc, option_app (intern_type env) po,
		List.map (intern env) tms,
		List.map (intern_eqn (List.length tms) env) eqns)
    | COrderedCase (loc, tag, po, c, cl) ->
	ROrderedCase (loc, tag, option_app (intern_type env) po,
	          intern env c,
		  Array.of_list (List.map (intern env) cl))
    | CHole loc -> 
	RHole (loc, QuestionMark)
    | CPatVar (loc, n) when allow_soapp ->
	RPatVar (loc, n)
    | CPatVar (loc, (false,n)) when Options.do_translate () ->
	RVar (loc, n)
    | CPatVar (loc, (false,n as x)) ->
        if List.mem n (fst (let (a,_,_) = lvar in a))
	  (* & !Options.v7 : ne pas exiger, Tauto est encore en V7 ! *) then 
	  RVar (loc, n)
	else
          error_unbound_patvar loc n
    | CPatVar (loc, _) ->
	raise (InternalisationError (loc,NegativeMetavariable))
    | CEvar (loc, n) ->
	REvar (loc, n)
    | CSort (loc, s) ->
	RSort(loc,s)
    | CCast (loc, c1, c2) ->
	RCast (loc,intern env c1,intern_type env c2)

    | CDynamic (loc,d) -> RDynamic (loc,d)

  and intern_type (ids,impls,tmp_scope,scopes) =
    intern (ids,impls,Some Symbols.type_scope,scopes)

  and intern_eqn n (ids,impls,tmp_scope,scopes as env) (loc,lhs,rhs) =
	let (idsl_substl_list,pl) =
	  List.split 
	    (List.map (intern_cases_pattern scopes ([],[]) None) lhs) in
	let idsl, substl = List.split (List.flatten idsl_substl_list) in
	let eqn_ids = List.flatten idsl in
	let subst = List.flatten substl in 
	(* Linearity implies the order in ids is irrelevant *)
	check_linearity lhs eqn_ids;
	check_uppercase loc eqn_ids;
	check_number_of_pattern loc n pl;
	let rhs = replace_vars_constr_expr subst rhs in
	List.iter message_redundant_alias subst;
	let env_ids = List.fold_right Idset.add eqn_ids ids in
	(loc, eqn_ids,pl,intern (env_ids,impls,tmp_scope,scopes) rhs)

  and iterate_prod loc2 (ids,impls,tmpsc,scopes as env) ty body = function
    | (loc1,na)::nal ->
	if nal <> [] then check_capture loc1 ty na;
	let ids' = name_fold Idset.add na ids in
	let body = iterate_prod loc2 (ids',impls,tmpsc,scopes) ty body nal in
	let ty = locate_if_isevar loc1 na (intern_type env ty) in
	RProd (join_loc loc1 loc2, na, ty, body)
    | [] -> intern env body

  and iterate_lam loc2 (ids,impls,tmpsc,scopes as env) ty body = function
    | (loc1,na)::nal ->
	if nal <> [] then check_capture loc1 ty na;
	let ids' = name_fold Idset.add na ids in
	let body = iterate_lam loc2 (ids',impls,tmpsc,scopes) ty body nal in
	let ty = locate_if_isevar loc1 na (intern_type env ty) in
	RLambda (join_loc loc1 loc2, na, ty, body)
    | [] -> intern env body

  and intern_impargs c env l subscopes args =
    let rec aux n l subscopes args = 
      let (enva,subscopes') = apply_scope_env env subscopes in
      match (l,args) with 
      | (imp::l', (a,Some j)::args') ->
	  if is_status_implicit imp & j>=n then
	    if j=n then 
	      (intern enva a)::(aux (n+1) l' subscopes' args')
	    else 
	      (RHole (set_hole_implicit n c))::(aux (n+1) l' subscopes' args)
	  else 
	    let e = if is_status_implicit imp then Some n else None in
	    raise
	      (InternalisationError(constr_loc a,BadExplicitationNumber (j,e)))
      | (imp::l',(a,None)::args') -> 
	  if is_status_implicit imp then 
	    (RHole (set_hole_implicit n c))::(aux (n+1) l' subscopes' args)
	  else 
	    (intern enva a)::(aux (n+1) l' subscopes' args')
      | ([],args) -> intern_tailargs env subscopes args
      | (_::l',[]) ->
          if List.for_all is_status_implicit l then
            (RHole (set_hole_implicit n c))::(aux (n+1) l' subscopes args)
          else []
    in 
    aux 1 l subscopes args

  and intern_tailargs env subscopes = function
    | (a,Some _)::args' ->
	raise (InternalisationError (constr_loc a, WrongExplicitImplicit))
    | (a,None)::args ->
      let (enva,subscopes) = apply_scope_env env subscopes in
      (intern enva a) :: (intern_tailargs env subscopes args)
    | [] -> []

  and intern_args env subscopes = function
    | [] -> []
    | a::args ->
        let (enva,subscopes) = apply_scope_env env subscopes in
        (intern enva a) :: (intern_args env subscopes args)

  in 
  try 
    intern env c
  with
      InternalisationError (loc,e) ->
	user_err_loc (loc,"internalize",explain_internalisation_error e)

(**************************************************************************)
(* Functions to translate constr_expr into rawconstr                       *)
(**************************************************************************)

let extract_ids env =
  List.fold_right Idset.add 
    (Termops.ids_of_rel_context (Environ.rel_context env))
    Idset.empty

let interp_rawconstr_gen isarity sigma env impls allow_soapp ltacvar c =
  let tmp_scope = if isarity then Some Symbols.type_scope else None in
  internalise sigma (extract_ids env, impls, tmp_scope,[])
    allow_soapp (ltacvar,Environ.named_context env, []) c

let interp_rawconstr sigma env c =
  interp_rawconstr_gen false sigma env [] false ([],[]) c

let interp_rawtype sigma env c =
  interp_rawconstr_gen true sigma env [] false ([],[]) c

let interp_rawtype_with_implicits sigma env impls c =
  interp_rawconstr_gen true sigma env impls false ([],[]) c

(*
(* The same as interp_rawconstr but with a list of variables which must not be
   globalized *)

let interp_rawconstr_wo_glob sigma env lvar c =
  interp_rawconstr_gen sigma env [] (Some []) lvar c
*)

(*********************************************************************)
(* Functions to parse and interpret constructions *)

let interp_constr sigma env c =
  understand sigma env (interp_rawconstr sigma env c)

let interp_openconstr sigma env c =
  understand_gen_tcc sigma env [] None (interp_rawconstr sigma env c)

let interp_casted_openconstr sigma env c typ =
  understand_gen_tcc sigma env [] (Some typ) (interp_rawconstr sigma env c)

let interp_type sigma env c =
  understand_type sigma env (interp_rawtype sigma env c)

let interp_binder sigma env na t =
  let t = interp_rawtype sigma env t in
  understand_type sigma env (locate_if_isevar (loc_of_rawconstr t) na t)

let interp_type_with_implicits sigma env impls c =
  understand_type sigma env (interp_rawtype_with_implicits sigma env impls c)

let judgment_of_rawconstr sigma env c =
  understand_judgment sigma env (interp_rawconstr sigma env c)

let type_judgment_of_rawconstr sigma env c =
  understand_type_judgment sigma env (interp_rawconstr sigma env c)

(* To retype a list of key*constr with undefined key *)
let retype_list sigma env lst =
  List.fold_right (fun (x,csr) a ->
    try (x,Retyping.get_judgment_of env sigma csr)::a with
    | Anomaly _ -> a) lst []

(*  List.map (fun (x,csr) -> (x,Retyping.get_judgment_of env sigma csr)) lst*)

type ltac_sign = 
  identifier list * (identifier * identifier option) list

type ltac_env = 
  (identifier * Term.constr) list * (identifier * identifier option) list

(* Interprets a constr according to two lists *)
(* of instantiations (variables and metas)    *)
(* Note: typ is retyped *)
let interp_constr_gen sigma env (ltacvars,unbndltacvars) c exptyp =
  let c = interp_rawconstr_gen false sigma env [] false
    (List.map fst ltacvars,unbndltacvars) c in
  let typs = retype_list sigma env ltacvars in
  understand_gen sigma env typs exptyp c

(*Interprets a casted constr according to two lists of instantiations
  (variables and metas)*)
let interp_openconstr_gen sigma env (ltacvars,unbndltacvars) c exptyp =
  let c = interp_rawconstr_gen false sigma env [] false
    (List.map fst ltacvars,unbndltacvars) c in
  let typs = retype_list sigma env ltacvars in
  understand_gen_tcc sigma env typs exptyp c

let interp_casted_constr sigma env c typ = 
  understand_gen sigma env [] (Some typ) (interp_rawconstr sigma env c)

let interp_constrpattern_gen sigma env (ltacvar,unbndltacvar) c =
  let c = interp_rawconstr_gen false sigma env [] true
    (List.map fst ltacvar,unbndltacvar) c in
  pattern_of_rawconstr c

let interp_constrpattern sigma env c =
  interp_constrpattern_gen sigma env ([],[]) c

let interp_aconstr vars a =
  let env = Global.env () in
  (* [vl] is intended to remember the scope of the free variables of [a] *)
  let vl = List.map (fun id -> (id,ref None)) vars in
  let c = for_grammar (internalise Evd.empty (extract_ids env, [], None, [])
    false (([],[]),Environ.named_context env,vl)) a in
  (* Translate and check that [c] has all its free variables bound in [vars] *)
  let a = aconstr_of_rawconstr vars c in
  (* Returns [a] and the ordered list of variables with their scopes *)
  (* Variables occurring in binders have no relevant scope since bound *)
  List.map
    (fun (id,r) -> (id,match !r with None -> None,[] | Some (a,l) -> a,l)) vl,
  a
