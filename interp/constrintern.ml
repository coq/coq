(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

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
open Cases
open Topconstr
open Nametab
open Notation
open Inductiveops

(* To interpret implicits and arg scopes of recursive variables in
   inductive types and recursive definitions *)
type var_internalisation_data =
    identifier list * Impargs.implicits_list * scope_name option list

type implicits_env = (identifier * var_internalisation_data) list
type full_implicits_env = identifier list * implicits_env

let interning_grammar = ref false

(* Historically for parsing grammar rules, but in fact used only for
   translator, v7 parsing, and unstrict tactic internalisation *)
let for_grammar f x =
  interning_grammar := true;
  let a = f x in
    interning_grammar := false;
    a

let variables_bind = ref false

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
  | BadExplicitationNumber of explicitation * int option

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
  str "Expecting " ++ int n1 ++ str (plural n1 " pattern") ++
  str " but found " ++ int n2

let explain_bad_explicitation_number n po =
  match n with
  | ExplByPos n ->
      let s = match po with
	| None -> str "a regular argument"
	| Some p -> int p in
      str "Bad explicitation number: found " ++ int n ++ 
      str" but was expecting " ++ s
  | ExplByName id ->
      let s = match po with
	| None -> str "a regular argument"
	| Some p -> (*pr_id (name_of_position p) in*) failwith "" in
      str "Bad explicitation name: found " ++ pr_id id ++ 
      str" but was expecting " ++ s

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

let error_bad_inductive_type loc =
  user_err_loc (loc,"",str 
    "This should be an inductive type applied to names or \"_\"")

let error_inductive_parameter_not_implicit loc =
  user_err_loc (loc,"", str
   ("The parameters of inductive types do not bind in\n"^
    "the 'return' clauses; they must be replaced by '_' in the 'in' clauses."))

(**********************************************************************)
(* Dump of globalization (to be used by coqdoc)                       *)
let token_number = ref 0
let last_pos = ref 0

type coqdoc_state = Lexer.location_table * int * int

let coqdoc_freeze () =
  let lt = Lexer.location_table() in
  let state = (lt,!token_number,!last_pos) in
    token_number := 0;
    last_pos := 0;
    state

let coqdoc_unfreeze (lt,tn,lp) =
  Lexer.restore_location_table lt;
  token_number := tn;
  last_pos := lp

let add_glob loc ref = 
  let sp = Nametab.sp_of_global ref in
  let lib_dp = Lib.library_part ref in
  let mod_dp,id = repr_path sp in
  let mod_dp_trunc =  drop_dirpath_prefix lib_dp mod_dp in
  let filepath = string_of_dirpath lib_dp in
  let fullname = string_of_qualid (make_qualid mod_dp_trunc id) in
    dump_string (Printf.sprintf "R%d %s %s\n" (fst (unloc loc)) filepath fullname)

let loc_of_notation f loc args ntn =
  if args=[] or ntn.[0] <> '_' then fst (unloc loc)
  else snd (unloc (f (List.hd args)))

let ntn_loc = loc_of_notation constr_loc
let patntn_loc = loc_of_notation cases_pattern_expr_loc

let dump_notation_location pos ((path,df),sc) =
  let rec next growing =
    let loc = Lexer.location_function !token_number in
    let (bp,_) = unloc loc in
      if growing then if bp >= pos then loc else (incr token_number;next true)
      else if bp = pos then loc
      else if bp > pos then (decr token_number;next false)
      else (incr token_number;next true) in
  let loc = next (pos >= !last_pos) in
    last_pos := pos;
    let path = string_of_dirpath path in
    let sc = match sc with Some sc -> " "^sc | None -> "" in
      dump_string (Printf.sprintf "R%d %s \"%s\"%s\n" (fst (unloc loc)) path df sc)

(**********************************************************************)
(* Contracting "{ _ }" in notations *)

let rec wildcards ntn n =
  if n = String.length ntn then []
  else let l = spaces ntn (n+1) in if ntn.[n] = '_' then n::l else l
and spaces ntn n =
  if n = String.length ntn then []
  else if ntn.[n] = ' ' then wildcards ntn (n+1) else spaces ntn (n+1)

let expand_notation_string ntn n =
  let pos = List.nth (wildcards ntn 0) n in
  let hd = if pos = 0 then "" else String.sub ntn 0 pos in
  let tl = 
    if pos = String.length ntn then "" 
    else String.sub ntn (pos+1) (String.length ntn - pos -1) in
  hd ^ "{ _ }" ^ tl

(* This contracts the special case of "{ _ }" for sumbool, sumor notations *)
(* Remark: expansion of squash at definition is done in metasyntax.ml *)
let contract_notation ntn l =
  let ntn' = ref ntn in
  let rec contract_squash n = function
    | [] -> []
    | CNotation (_,"{ _ }",[a]) :: l -> 
        ntn' := expand_notation_string !ntn' n;
        contract_squash n (a::l)
    | a :: l ->
        a::contract_squash (n+1) l in
  let l = contract_squash 0 l in
  (* side effect; don't inline *)
  !ntn',l

let contract_pat_notation ntn l =
  let ntn' = ref ntn in
  let rec contract_squash n = function
    | [] -> []
    | CPatNotation (_,"{ _ }",[a]) :: l -> 
        ntn' := expand_notation_string !ntn' n;
        contract_squash n (a::l)
    | a :: l ->
        a::contract_squash (n+1) l in
  let l = contract_squash 0 l in
  (* side effect; don't inline *)
  !ntn',l

(**********************************************************************)
(* Remembering the parsing scope of variables in notations            *)

let make_current_scope (tmp_scope,scopes) = option_cons tmp_scope scopes

let set_var_scope loc id (_,scopt,scopes) varscopes =
  let idscopes = List.assoc id varscopes in
  if !idscopes <> None & 
    make_current_scope (out_some !idscopes)
    <> make_current_scope (scopt,scopes) then
      user_err_loc (loc,"set_var_scope",
      pr_id id ++ str " already occurs in a different scope")
  else
    idscopes := Some (scopt,scopes)

(**********************************************************************)
(* Discriminating between bound variables and global references       *)

(* [vars1] is a set of name to avoid (used for the tactic language);
   [vars2] is the set of global variables, env is the set of variables
   abstracted until this point *)

let intern_var (env,_,_ as genv) (ltacvars,vars2,vars3,(_,impls)) loc id =
  let (vars1,unbndltacvars) = ltacvars in
  (* Is [id] an inductive type potentially with implicit *)
  try
    let l,impl,argsc = List.assoc id impls in
    let l = List.map 
      (fun id -> CRef (Ident (loc,id)), Some (loc,ExplByName id)) l in
    RVar (loc,id), impl, argsc, l
  with Not_found ->
  (* Is [id] bound in current env or is an ltac var bound to constr *)
  if Idset.mem id env or List.mem id vars1
  then
      RVar (loc,id), [], [], []
  (* Is [id] a notation variable *)
  else if List.mem_assoc id vars3
  then
    (set_var_scope loc id genv vars3; RVar (loc,id), [], [], [])
  else

  (* Is [id] bound to a free name in ltac (this is an ltac error message) *)
  try
    match List.assoc id unbndltacvars with
      | None -> user_err_loc (loc,"intern_var",
	  str "variable " ++ pr_id id ++ str " should be bound to a term")
      | Some id0 -> Pretype_errors.error_var_not_found_loc loc id0
  with Not_found ->
  (* Is [id] a goal or section variable *)
  let _ = Sign.lookup_named id vars2 in
  try
    (* [id] a section variable *)
    (* Redundant: could be done in intern_qualid *)
    let ref = VarRef id in
    RRef (loc, ref), implicits_of_global ref, find_arguments_scope ref, []
  with _ ->
    (* [id] a goal variable *)
    RVar (loc,id), [], [], []

let find_appl_head_data (_,_,_,(_,impls)) = function
  | RRef (_,ref) as x -> x,implicits_of_global ref,find_arguments_scope ref,[]
  | x -> x,[],[],[]

(* Is it a global reference or a syntactic definition? *)
let intern_qualid loc qid =
  try match Nametab.extended_locate qid with
  | TrueGlobal ref ->
      if !dump then add_glob loc ref;
      RRef (loc, ref)
  | SyntacticDef sp ->
      Syntax_def.search_syntactic_definition loc sp
  with Not_found ->
    error_global_not_found_loc loc qid

(* Rule out section vars since these should have been found by intern_var *)
let intern_non_secvar_qualid loc qid =
  match intern_qualid loc qid with
    | RRef (loc, VarRef id) -> error_global_not_found_loc loc qid
    | r -> r

let intern_inductive r =
  let loc,qid = qualid_of_reference r in
  try match Nametab.extended_locate qid with
  | TrueGlobal (IndRef ind) -> ind, []
  | TrueGlobal _ -> raise Not_found
  | SyntacticDef sp ->
      (match Syntax_def.search_syntactic_definition loc sp with
	| RApp (_,RRef(_,IndRef ind),l)
	    when List.for_all (function RHole _ -> true | _ -> false) l ->
	    (ind, List.map (fun _ -> Anonymous) l)
	| _ -> raise Not_found)
  with Not_found ->
    error_global_not_found_loc loc qid

let intern_reference env lvar = function
  | Qualid (loc, qid) ->
      find_appl_head_data lvar (intern_qualid loc qid)
  | Ident (loc, id) ->
      try intern_var env lvar loc id
      with Not_found -> 
      let qid = make_short_qualid id in
      try find_appl_head_data lvar (intern_non_secvar_qualid loc qid)
      with e ->
	(* Extra allowance for non globalizing functions *)
	if !interning_grammar then RVar (loc,id), [], [], []
	else raise e

let interp_reference vars r =
  let r,_,_,_ = intern_reference (Idset.empty,None,[]) (vars,[],[],([],[])) r 
  in r

let apply_scope_env (ids,_,scopes) = function
  | [] -> (ids,None,scopes), []
  | sc::scl -> (ids,sc,scopes), scl

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

let product_of_cases_patterns ids idspl =
  List.fold_right (fun (ids,pl) (ids',ptaill) ->
    (ids@ids',
    (* Cartesian prod of the or-pats for the nth arg and the tail args *)
    List.flatten (
    List.map (fun (subst,p) ->
      List.map (fun (subst',ptail) -> (subst@subst',p::ptail)) ptaill) pl)))
    idspl (ids,[[],[]])

let simple_product_of_cases_patterns pl =
  List.fold_right (fun pl ptaill ->
    List.flatten (List.map (fun (subst,p) ->
      List.map (fun (subst',ptail) -> (subst@subst',p::ptail)) ptaill) pl))
    pl [[],[]]

(* Check linearity of pattern-matching *)
let rec has_duplicate = function 
  | [] -> None
  | x::l -> if List.mem x l then (Some x) else has_duplicate l

let loc_of_lhs lhs = 
 join_loc (cases_pattern_expr_loc (List.hd (List.hd lhs)))
          (cases_pattern_expr_loc (list_last (list_last lhs)))

let check_linearity lhs ids =
  match has_duplicate ids with
    | Some id ->
	raise (InternalisationError (loc_of_lhs lhs,NonLinearPattern id))
    | None ->
	()

(* Match the number of pattern against the number of matched args *)
let check_number_of_pattern loc n l =
  let p = List.length l in
  if n<>p then raise (InternalisationError (loc,BadPatternsNumber (n,p)))

let check_or_pat_variables loc ids idsl =
  if List.exists (fun ids' -> not (list_eq_set ids ids')) idsl then
    user_err_loc (loc, "", str 
    "The components of this disjunctive pattern must bind the same variables")

let check_constructor_length env loc cstr pl pl0 =
  let n = List.length pl + List.length pl0 in
  let nargs = Inductiveops.constructor_nrealargs env cstr in
  let nhyps = Inductiveops.constructor_nrealhyps env cstr in
  if n <> nargs && n <> nhyps (* i.e. with let's *) then
    error_wrong_numarg_constructor_loc loc env cstr nargs

(* Manage multiple aliases *)

  (* [merge_aliases] returns the sets of all aliases encountered at this
     point and a substitution mapping extra aliases to the first one *)
let merge_aliases (ids,subst as _aliases) id =
  ids@[id], if ids=[] then subst else (id, List.hd ids)::subst

let alias_of = function
  | ([],_) -> Anonymous
  | (id::_,_) -> Name id

let message_redundant_alias (id1,id2) =
  if_verbose warning 
   ("Alias variable "^(string_of_id id1)^" is merged with "^(string_of_id id2))

(* Expanding notations *)

let decode_patlist_value = function
  | CPatCstr (_,_,l) -> l
  | _ -> anomaly "Ill-formed list argument of notation"

let rec subst_pat_iterator y t (subst,p) = match p with
  | PatVar (_,id) as x ->
      if id = Name y then t else [subst,x]
  | PatCstr (loc,id,l,alias) ->
      let l' = List.map (fun a -> (subst_pat_iterator y t ([],a))) l in
      let pl = simple_product_of_cases_patterns l' in
      List.map (fun (subst',pl) -> subst'@subst,PatCstr (loc,id,pl,alias)) pl

let subst_cases_pattern loc alias intern subst scopes a =
  let rec aux alias subst = function
  | AVar id ->
      begin
	(* subst remembers the delimiters stack in the interpretation *)
	(* of the notations *)
	try 
	  let (a,(scopt,subscopes)) = List.assoc id subst in
	    intern (subscopes@scopes) ([],[]) scopt a
	with Not_found -> 
	  if id = ldots_var then [], [[], PatVar (loc,Name id)] else
	  anomaly ("Unbound pattern notation variable: "^(string_of_id id))
	  (*
	  (* Happens for local notation joint with inductive/fixpoint defs *)
	  if aliases <> ([],[]) then
	    anomaly "Pattern notation without constructors";
	  [[id],[]], PatVar (loc,Name id)
	  *)
      end
  | ARef (ConstructRef c) ->
      ([],[[], PatCstr (loc,c, [], alias)])
  | AApp (ARef (ConstructRef (ind,_ as c)),args) ->
      let nparams = (fst (Global.lookup_inductive ind)).Declarations.mind_nparams in
      let _,args = list_chop nparams args in
      let idslpll = List.map (aux Anonymous subst) args in
      let ids',pll = product_of_cases_patterns [] idslpll in
      let pl' = List.map (fun (subst,pl) -> 
        subst,PatCstr (loc,c,pl,alias)) pll in
	ids', pl'
  | AList (x,_,iter,terminator,lassoc) ->
      (try 
        (* All elements of the list are in scopes (scopt,subscopes) *)
	let (a,(scopt,subscopes)) = List.assoc x subst in
        let termin = aux Anonymous subst terminator in
        let l = decode_patlist_value a in
        let idsl,v =
	  List.fold_right (fun a (tids,t) -> 
            let uids,u = aux Anonymous ((x,(a,(scopt,subscopes)))::subst) iter in
            let pll = List.map (subst_pat_iterator ldots_var t) u in
            tids@uids, List.flatten pll)
            (if lassoc then List.rev l else l) termin in
        idsl, List.map (fun ((subst, pl) as x) -> 
	  match pl with PatCstr (loc, c, pl, Anonymous) -> (subst, PatCstr (loc, c, pl, alias)) | _ -> x) v
      with Not_found -> 
          anomaly "Inconsistent substitution of recursive notation")
  | t -> user_err_loc (loc,"",str "Invalid notation for pattern")
  in aux alias subst a
    
(* Differentiating between constructors and matching variables *)
type pattern_qualid_kind =
  | ConstrPat of (constructor * cases_pattern list)
  | VarPat of identifier

let rec patt_of_rawterm loc cstr =
  match cstr with
    | RRef (_,(ConstructRef c as x)) ->
	if !dump then add_glob loc x; 
 	(c,[])
    | RApp (_,RApp(_,h,l1),l2) -> patt_of_rawterm loc (RApp(loc,h,l1@l2))
    | RApp (_,RRef(_,(ConstructRef c as x)),pl) ->
        if !dump then add_glob loc x;
        let (mib,_) = Inductive.lookup_mind_specif (Global.env()) (fst c) in
        let npar = mib.Declarations.mind_nparams in
        let (params,args) =
          if List.length pl <= npar then (pl,[]) else
            list_chop npar pl in
        (* All parameters must be _ *)
        List.iter
          (function RHole _ -> ()
            | _ -> raise Not_found) params;
        let pl' = List.map
          (fun c ->
            let (c,pl) = patt_of_rawterm loc c in
            PatCstr(loc,c,pl,Anonymous)) args in
        (c,pl')
    | _ -> raise Not_found

let find_constructor ref =
  let (loc,qid) = qualid_of_reference ref in
  let gref =
    try extended_locate qid
    with Not_found ->
      raise (InternalisationError (loc,NotAConstructor ref)) in
    match gref with
      | SyntacticDef sp ->
          let sdef = Syntax_def.search_syntactic_definition loc sp in
            patt_of_rawterm loc sdef
      | TrueGlobal r ->
          let rec unf = function
            | ConstRef cst ->
		let v = Environ.constant_value (Global.env()) cst in
		  unf (global_of_constr v)
            | ConstructRef c -> 
		if !dump then add_glob loc r; 
		c, []
            | _ -> raise Not_found
          in unf r

let find_pattern_variable = function
  | Ident (loc,id) -> id
  | Qualid (loc,_) as x -> raise (InternalisationError(loc,NotAConstructor x))

let maybe_constructor ref =
  try ConstrPat (find_constructor ref)
  with
      (* patt var does not exists globally *)
    | InternalisationError _ -> VarPat (find_pattern_variable ref)
      (* patt var also exists globally but does not satisfy preconditions *)
    | (Environ.NotEvaluableConst _ | Not_found) ->
        if_verbose msg_warning (str "pattern " ++ pr_reference ref ++
              str " is understood as a pattern variable");
        VarPat (find_pattern_variable ref)

let mustbe_constructor loc ref = 
  try find_constructor ref
  with (Environ.NotEvaluableConst _ | Not_found) ->
    raise (InternalisationError (loc,NotAConstructor ref))

let rec intern_cases_pattern genv scopes (ids,subst as aliases) tmp_scope = 
  function
  | CPatAlias (loc, p, id) ->
      let aliases' = merge_aliases aliases id in
      intern_cases_pattern genv scopes aliases' tmp_scope p
  | CPatCstr (loc, head, pl) ->
      let c,pl0 = mustbe_constructor loc head in
      let argscs =
	simple_adjust_scopes (find_arguments_scope (ConstructRef c), pl) in
      check_constructor_length genv loc c pl0 pl;
      let idslpl =
	List.map2 (intern_cases_pattern genv scopes ([],[])) argscs pl in
      let (ids',pll) = product_of_cases_patterns ids idslpl in
      let pl' = List.map (fun (subst,pl) ->
        (subst, PatCstr (loc,c,pl0@pl,alias_of aliases))) pll in
      ids',pl'
  | CPatNotation (loc,"- _",[CPatPrim(_,Numeral p)]) 
      when Bigint.is_strictly_pos p ->
      let np = Numeral (Bigint.neg p) in
      intern_cases_pattern genv scopes aliases tmp_scope (CPatPrim(loc,np))
  | CPatNotation (_,"( _ )",[a]) ->
      intern_cases_pattern genv scopes aliases tmp_scope a
  | CPatNotation (loc, ntn, args) ->
      let ntn,args = contract_pat_notation ntn args in
      let ((ids',c),df) = Notation.interp_notation loc ntn (tmp_scope,scopes) in
      if !dump then dump_notation_location (patntn_loc loc args ntn) df;
      let subst = List.map2 (fun (id,scl) a -> (id,(a,scl))) ids' args in
      let ids'',pl = subst_cases_pattern loc (alias_of aliases) (intern_cases_pattern genv) subst scopes 
	c
      in ids@ids'', pl
  | CPatPrim (loc, p) ->
      let a = alias_of aliases in
      let (c,df) = Notation.interp_prim_token_cases_pattern loc p a 
	(tmp_scope,scopes) in
      if !dump then dump_notation_location (fst (unloc loc)) df;
      (ids,[subst,c])
  | CPatDelimiters (loc, key, e) ->
      intern_cases_pattern genv (find_delimiters_scope loc key::scopes)
        aliases None e
  | CPatAtom (loc, Some head) ->
      (match maybe_constructor head with
	 | ConstrPat (c,args) ->
	     check_constructor_length genv loc c [] [];
	     (ids,[subst, PatCstr (loc,c,args,alias_of aliases)])
	 | VarPat id ->
	     let ids,subst = merge_aliases aliases id in
	     (ids,[subst, PatVar (loc,alias_of (ids,subst))]))
  | CPatAtom (loc, None) ->
      (ids,[subst, PatVar (loc,alias_of aliases)])
  | CPatOr (loc, pl) ->
      assert (pl <> []);
      let pl' = 
	List.map (intern_cases_pattern genv scopes aliases tmp_scope) pl in
      let (idsl,pl') = List.split pl' in
      let ids = List.hd idsl in
      check_or_pat_variables loc ids (List.tl idsl);
      (ids,List.flatten pl')

(**********************************************************************)
(* Fix and CoFix                                                      *)

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
      with Not_found -> RHole (loc, Evd.BinderType na))
  | x -> x

let check_hidden_implicit_parameters id (_,_,_,(indnames,_)) =
  if List.mem id indnames then
    errorlabstrm "" (str "A parameter or name of an inductive type " ++
    pr_id id ++ str " must not be used as a bound variable in the type \
of its constructor")

let push_name_env lvar (ids,tmpsc,scopes as env) = function
  | Anonymous -> env 
  | Name id -> 
      check_hidden_implicit_parameters id lvar;
      (Idset.add id ids,tmpsc,scopes)

(**********************************************************************)
(* Utilities for application                                          *)

let merge_impargs l args =
  List.fold_right (fun a l ->
    match a with 
      | (_,Some (_,(ExplByName id as x))) when 
	  List.exists (function (_,Some (_,y)) -> x=y | _ -> false) args -> l
      | _ -> a::l)
    l args 

let check_projection isproj nargs r = 
  match (r,isproj) with
  | RRef (loc, ref), Some _ ->
      (try
	let n = Recordops.find_projection_nparams ref + 1 in
	if nargs <> n then
	  user_err_loc (loc,"",str "Projection has not the right number of explicit parameters");
      with Not_found -> 
	user_err_loc
	(loc,"",pr_global_env Idset.empty ref ++ str " is not a registered projection"))
  | _, Some _ -> user_err_loc (loc_of_rawconstr r, "", str "Not a projection")
  | _, None -> ()

let get_implicit_name n imps =
  Some (Impargs.name_of_implicit (List.nth imps (n-1)))

let set_hole_implicit i = function
  | RRef (loc,r) -> (loc,Evd.ImplicitArg (r,i))
  | RVar (loc,id) -> (loc,Evd.ImplicitArg (VarRef id,i))
  | _ -> anomaly "Only refs have implicits"

let exists_implicit_name id =
  List.exists (fun imp -> is_status_implicit imp & id = name_of_implicit imp)

let extract_explicit_arg imps args =
  let rec aux = function
  | [] -> [],[]
  | (a,e)::l ->
      let (eargs,rargs) = aux l in
      match e with
      | None -> (eargs,a::rargs)
      | Some (loc,pos) ->
	  let id = match pos with
	  | ExplByName id ->
	      if not (exists_implicit_name id imps) then
		user_err_loc (loc,"",str "Wrong argument name: " ++ pr_id id);
	      if List.mem_assoc id eargs then
		user_err_loc (loc,"",str "Argument name " ++ pr_id id
		++ str " occurs more than once");
	      id
	  | ExplByPos p ->
	      let id =
		try 
		  let imp = List.nth imps (p-1) in
		  if not (is_status_implicit imp) then failwith "imp";
		  name_of_implicit imp
		with Failure _ (* "nth" | "imp" *) ->
		  user_err_loc (loc,"",str"Wrong argument position: " ++ int p)
	      in
	      if List.mem_assoc id eargs then
		user_err_loc (loc,"",str"Argument at position " ++ int p ++
		  str " is mentioned more than once");
	      id in
	  ((id,(loc,a))::eargs,rargs)
  in aux args

(**********************************************************************)
(* Syntax extensions                                                  *)

let traverse_binder subst (renaming,(ids,tmpsc,scopes as env)) id =
  try
    (* Binders bound in the notation are considered first-order objects *)
    let _,id' = coerce_to_id (fst (List.assoc id subst)) in
    (renaming,(Idset.add id' ids,tmpsc,scopes)), id'
  with Not_found ->
    (* Binders not bound in the notation do not capture variables *)
    (* outside the notation (i.e. in the substitution) *)
    let fvs1 = List.map (fun (_,(c,_)) -> free_vars_of_constr_expr c) subst in
    let fvs2 = List.map snd renaming in
    let fvs = List.flatten (List.map Idset.elements fvs1) @ fvs2 in
    let id' = next_ident_away id fvs in
    let renaming' = if id=id' then renaming else (id,id')::renaming in
    (renaming',env), id'

let decode_constrlist_value = function
  | CAppExpl (_,_,l) -> l
  | _ -> anomaly "Ill-formed list argument of notation"

let rec subst_iterator y t = function
  | RVar (_,id) as x -> if id = y then t else x
  | x -> map_rawconstr (subst_iterator y t) x

let rec subst_aconstr_in_rawconstr loc interp subst (renaming,(ids,_,scopes)) =
  function
  | AVar id ->
      begin
	(* subst remembers the delimiters stack in the interpretation *)
	(* of the notations *)
	try 
	  let (a,(scopt,subscopes)) = List.assoc id subst in
	  interp (ids,scopt,subscopes@scopes) a
	with Not_found -> 
	try 
	  RVar (loc,List.assoc id renaming)
	with Not_found -> 
	  (* Happens for local notation joint with inductive/fixpoint defs *)
	  RVar (loc,id)
      end
  | AList (x,_,iter,terminator,lassoc) ->
      (try 
        (* All elements of the list are in scopes (scopt,subscopes) *)
	let (a,(scopt,subscopes)) = List.assoc x subst in
        let termin = 
          subst_aconstr_in_rawconstr loc interp subst 
	    (renaming,(ids,None,scopes)) terminator in
        let l = decode_constrlist_value a in
	List.fold_right (fun a t -> 
          subst_iterator ldots_var t
            (subst_aconstr_in_rawconstr loc interp 
              ((x,(a,(scopt,subscopes)))::subst)
	      (renaming,(ids,None,scopes)) iter))
            (if lassoc then List.rev l else l) termin
      with Not_found -> 
          anomaly "Inconsistent substitution of recursive notation")
  | t ->
      rawconstr_of_aconstr_with_binders loc (traverse_binder subst)
      (subst_aconstr_in_rawconstr loc interp subst)
      (renaming,(ids,None,scopes)) t

let intern_notation intern (_,tmp_scope,scopes as env) loc ntn args =
  let ntn,args = contract_notation ntn args in
  let ((ids,c),df) = Notation.interp_notation loc ntn (tmp_scope,scopes) in
  if !dump then dump_notation_location (ntn_loc loc args ntn) df;
  let subst = List.map2 (fun (id,scl) a -> (id,(a,scl))) ids args in
  subst_aconstr_in_rawconstr loc intern subst ([],env) c

let set_type_scope (ids,tmp_scope,scopes) =
  (ids,Some Notation.type_scope,scopes)

let reset_tmp_scope (ids,tmp_scope,scopes) =
  (ids,None,scopes)

(**********************************************************************)
(* Main loop                                                          *)

let internalise sigma globalenv env allow_patvar lvar c =
  let rec intern (ids,tmp_scope,scopes as env) = function
    | CRef ref as x ->
	let (c,imp,subscopes,l) = intern_reference env lvar ref in
	(match intern_impargs c env imp subscopes l with
          | [] -> c
          | l -> RApp (constr_loc x, c, l))
    | CFix (loc, (locid,iddef), dl) ->
        let lf = List.map (fun (id,_,_,_,_) -> id) dl in
        let dl = Array.of_list dl in
	let n =
	  try list_index0 iddef lf
          with Not_found ->
	    raise (InternalisationError (locid,UnboundFixName (false,iddef)))
	in
        let idl = Array.map
          (fun (id,(n,order),bl,ty,bd) ->
	     let intern_ro_arg c f =
	       let before, after = list_chop (succ (out_some n)) bl in
	       let ((ids',_,_),rafter) =
		 List.fold_left intern_local_binder (env,[]) after in
	       let ro = (intern (ids', tmp_scope, scopes) c) in
		 f ro, List.fold_left intern_local_binder (env,rafter) before
	     in
	     let ro, ((ids',_,_),rbl) =
	       (match order with
		    CStructRec -> 
		      RStructRec,
		      List.fold_left intern_local_binder (env,[]) bl
		  | CWfRec c ->
		      intern_ro_arg c (fun r -> RWfRec r)
		  | CMeasureRec c ->
		      intern_ro_arg c (fun r -> RMeasureRec r))
	    in
	    let ids'' = List.fold_right Idset.add lf ids' in
	     ((n, ro), List.rev rbl, 
             intern_type (ids',tmp_scope,scopes) ty,
             intern (ids'',None,scopes) bd)) dl in
	RRec (loc,RFix 
	      (Array.map (fun (ro,_,_,_) -> ro) idl,n),
              Array.of_list lf,
              Array.map (fun (_,bl,_,_) -> bl) idl,
              Array.map (fun (_,_,ty,_) -> ty) idl,
              Array.map (fun (_,_,_,bd) -> bd) idl)
    | CCoFix (loc, (locid,iddef), dl) ->
        let lf = List.map (fun (id,_,_,_) -> id) dl in
        let dl = Array.of_list dl in
	let n =
          try list_index0 iddef lf
          with Not_found ->
	    raise (InternalisationError (locid,UnboundFixName (true,iddef)))
	in
        let idl = Array.map
          (fun (id,bl,ty,bd) ->
            let ((ids',_,_),rbl) =
              List.fold_left intern_local_binder (env,[]) bl in
	    let ids'' = List.fold_right Idset.add lf ids' in
            (List.rev rbl,
             intern_type (ids',tmp_scope,scopes) ty,
             intern (ids'',None,scopes) bd)) dl in
	RRec (loc,RCoFix n,
              Array.of_list lf,
              Array.map (fun (bl,_,_) -> bl) idl,
              Array.map (fun (_,ty,_) -> ty) idl,
              Array.map (fun (_,_,bd) -> bd) idl)
    | CArrow (loc,c1,c2) ->
        RProd (loc, Anonymous, intern_type env c1, intern_type env c2)
    | CProdN (loc,[],c2) ->
        intern_type env c2
    | CProdN (loc,(nal,ty)::bll,c2) ->
        iterate_prod loc env ty (CProdN (loc, bll, c2)) nal
    | CLambdaN (loc,[],c2) ->
        intern env c2
    | CLambdaN (loc,(nal,ty)::bll,c2) ->
	iterate_lam loc (reset_tmp_scope env) ty (CLambdaN (loc, bll, c2)) nal
    | CLetIn (loc,(_,na),c1,c2) ->
	RLetIn (loc, na, intern (reset_tmp_scope env) c1,
          intern (push_name_env lvar env na) c2)
    | CNotation (loc,"- _",[CPrim (_,Numeral p)])
	when Bigint.is_strictly_pos p -> 
	intern env (CPrim (loc,Numeral (Bigint.neg p)))
    | CNotation (_,"( _ )",[a]) -> intern env a
    | CNotation (loc,ntn,args) ->
        intern_notation intern env loc ntn args
    | CPrim (loc, p) ->
	let c,df = Notation.interp_prim_token loc p (tmp_scope,scopes) in
	if !dump then dump_notation_location (fst (unloc loc)) df;
	c
    | CDelimiters (loc, key, e) ->
	intern (ids,None,find_delimiters_scope loc key::scopes) e
    | CAppExpl (loc, (isproj,ref), args) ->
        let (f,_,args_scopes,_) = intern_reference env lvar ref in
	check_projection isproj (List.length args) f;
	RApp (loc, f, intern_args env args_scopes args)
    | CApp (loc, (isproj,f), args) ->
        let isproj,f,args = match f with
          (* Compact notations like "t.(f args') args" *)
          | CApp (_,(Some _,f), args') when isproj=None -> isproj,f,args'@args
          (* Don't compact "(f args') args" to resolve implicits separately *)
          | _ -> isproj,f,args in
	let (c,impargs,args_scopes,l) =
          match f with
            | CRef ref -> intern_reference env lvar ref
            | CNotation (loc,ntn,[]) ->
                let c = intern_notation intern env loc ntn [] in
                find_appl_head_data lvar c
            | x -> (intern env f,[],[],[]) in
	let args = 
	  intern_impargs c env impargs args_scopes (merge_impargs l args) in
	check_projection isproj (List.length args) c;
	(match c with 
          (* Now compact "(f args') args" *)
	  | RApp (loc', f', args') -> RApp (join_loc loc' loc, f',args'@args)
	  | _ -> RApp (loc, c, args))
    | CCases (loc, rtnpo, tms, eqns) ->
        let tms,env' = List.fold_right
          (fun citm (inds,env) ->
	    let (tm,ind),nal = intern_case_item env citm in
	    (tm,ind)::inds,List.fold_left (push_name_env lvar) env nal)
	  tms ([],env) in
        let rtnpo = option_map (intern_type env') rtnpo in
        let eqns' = List.map (intern_eqn (List.length tms) env) eqns in
	RCases (loc, rtnpo, tms, List.flatten eqns')
    | CLetTuple (loc, nal, (na,po), b, c) ->
	let env' = reset_tmp_scope env in
        let ((b',(na',_)),ids) = intern_case_item env' (b,(na,None)) in
        let env'' = List.fold_left (push_name_env lvar) env ids in
        let p' = option_map (intern_type env'') po in
        RLetTuple (loc, nal, (na', p'), b',
                   intern (List.fold_left (push_name_env lvar) env nal) c)
    | CIf (loc, c, (na,po), b1, b2) ->
	let env' = reset_tmp_scope env in
        let ((c',(na',_)),ids) = intern_case_item env' (c,(na,None)) in
        let env'' = List.fold_left (push_name_env lvar) env ids in
        let p' = option_map (intern_type env'') po in
        RIf (loc, c', (na', p'), intern env b1, intern env b2)
    | CHole loc -> 
	RHole (loc, Evd.QuestionMark true)
    | CPatVar (loc, n) when allow_patvar ->
	RPatVar (loc, n)
    | CPatVar (loc, _) ->
	raise (InternalisationError (loc,NegativeMetavariable))
    | CEvar (loc, n, l) ->
	REvar (loc, n, option_map (List.map (intern env)) l)
    | CSort (loc, s) ->
	RSort(loc,s)
    | CCast (loc, c1, CastConv (k, c2)) ->
	RCast (loc,intern env c1, CastConv (k, intern_type env c2))
    | CCast (loc, c1, CastCoerce) ->
	RCast (loc,intern env c1, CastCoerce)

    | CDynamic (loc,d) -> RDynamic (loc,d)

  and intern_type env = intern (set_type_scope env)

  and intern_local_binder ((ids,ts,sc as env),bl) = function
    | LocalRawAssum(nal,ty) ->
	let (loc,na) = List.hd nal in
	(* TODO: fail if several names with different implicit types *)
	let ty = locate_if_isevar loc na (intern_type env ty) in
        List.fold_left
          (fun ((ids,ts,sc),bl) (_,na) ->
            ((name_fold Idset.add na ids,ts,sc), (na,None,ty)::bl))
          (env,bl) nal
    | LocalRawDef((loc,na),def) ->
        ((name_fold Idset.add na ids,ts,sc),
         (na,Some(intern env def),RHole(loc,Evd.BinderType na))::bl)

  (* Expands a multiple pattern into a disjunction of multiple patterns *)
  and intern_multiple_pattern scopes pl =
    let idsl_pll = 
      List.map (intern_cases_pattern globalenv scopes ([],[]) None) pl in
    product_of_cases_patterns [] idsl_pll

  (* Expands a disjunction of multiple pattern *)
  and intern_disjunctive_multiple_pattern scopes loc mpl =
    assert (mpl <> []);
    let mpl' = List.map (intern_multiple_pattern scopes) mpl in
    let (idsl,mpl') = List.split mpl' in
    let ids = List.hd idsl in
    check_or_pat_variables loc ids (List.tl idsl);
    (ids,List.flatten mpl')

  (* Expands a pattern-matching clause [lhs => rhs] *)
  and intern_eqn n (ids,tmp_scope,scopes) (loc,lhs,rhs) =
    let eqn_ids,pll = intern_disjunctive_multiple_pattern scopes loc lhs in
    (* Linearity implies the order in ids is irrelevant *)
    check_linearity lhs eqn_ids;
    check_number_of_pattern loc n (snd (List.hd pll));
    let env_ids = List.fold_right Idset.add eqn_ids ids in
    List.map (fun (subst,pl) ->
      let rhs = replace_vars_constr_expr subst rhs in
      List.iter message_redundant_alias subst;
      let rhs' = intern (env_ids,tmp_scope,scopes) rhs in
      (loc,eqn_ids,pl,rhs')) pll

  and intern_case_item (vars,_,scopes as env) (tm,(na,t)) =
    let tm' = intern env tm in
    let ids,typ = match t with
    | Some t -> 
	let tids = ids_of_cases_indtype t in
	let tids = List.fold_right Idset.add tids Idset.empty in
	let t = intern_type (tids,None,scopes) t in
	let loc,ind,l = match t with
	    | RRef (loc,IndRef ind) -> (loc,ind,[])
	    | RApp (loc,RRef (_,IndRef ind),l) -> (loc,ind,l)
	    | _ -> error_bad_inductive_type (loc_of_rawconstr t) in
	let nparams, nrealargs = inductive_nargs globalenv ind in
	let nindargs = nparams + nrealargs in
	if List.length l <> nindargs then
	  error_wrong_numarg_inductive_loc loc globalenv ind nindargs;
	let nal = List.map (function
	  | RHole loc -> Anonymous
	  | RVar (_,id) -> Name id
	  | c -> user_err_loc (loc_of_rawconstr c,"",str "Not a name")) l in
	let parnal,realnal = list_chop nparams nal in
	if List.exists ((<>) Anonymous) parnal then
	  error_inductive_parameter_not_implicit loc;
	realnal, Some (loc,ind,nparams,realnal)
    | None -> 
	[], None in
    let na = match tm', na with
      | RVar (_,id), None when Idset.mem id vars -> Name id
      | _, None -> Anonymous
      | _, Some na -> na in
    (tm',(na,typ)), na::ids

  and iterate_prod loc2 env ty body = function
    | (loc1,na)::nal ->
	if nal <> [] then check_capture loc1 ty na;
	let body = iterate_prod loc2 (push_name_env lvar env na) ty body nal in
	let ty = locate_if_isevar loc1 na (intern_type env ty) in
	RProd (join_loc loc1 loc2, na, ty, body)
    | [] -> intern_type env body

  and iterate_lam loc2 env ty body = function
    | (loc1,na)::nal ->
	if nal <> [] then check_capture loc1 ty na;
	let body = iterate_lam loc2 (push_name_env lvar env na) ty body nal in
	let ty = locate_if_isevar loc1 na (intern_type env ty) in
	RLambda (join_loc loc1 loc2, na, ty, body)
    | [] -> intern env body

  and intern_impargs c env l subscopes args =
    let eargs, rargs = extract_explicit_arg l args in
    let rec aux n impl subscopes eargs rargs =
      let (enva,subscopes') = apply_scope_env env subscopes in
      match (impl,rargs) with
      | (imp::impl', rargs) when is_status_implicit imp ->
	  begin try 
	    let id = name_of_implicit imp in
	    let (_,a) = List.assoc id eargs in
	    let eargs' = List.remove_assoc id eargs in
	    intern enva a :: aux (n+1) impl' subscopes' eargs' rargs
	  with Not_found ->
	  if rargs=[] & eargs=[] & not (maximal_insertion_of imp) then
            (* Less regular arguments than expected: complete *)
            (* with implicit arguments if maximal insertion is set *)
	    []
	  else
	    RHole (set_hole_implicit (n,get_implicit_name n l) c) :: 
	      aux (n+1) impl' subscopes' eargs rargs
	  end
      | (imp::impl', a::rargs') ->
	  intern enva a :: aux (n+1) impl' subscopes' eargs rargs'
      | (imp::impl', []) -> 
	  if eargs <> [] then 
	    (let (id,(loc,_)) = List.hd eargs in
	    user_err_loc (loc,"",str "Not enough non implicit
	    arguments to accept the argument bound to " ++ pr_id id));
	  []
      | ([], rargs) ->
	  assert (eargs = []);
	  intern_args env subscopes rargs
    in aux 1 l subscopes eargs rargs

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

let intern_gen isarity sigma env
               ?(impls=([],[])) ?(allow_patvar=false) ?(ltacvars=([],[]))
               c =
  let tmp_scope = 
    if isarity then Some Notation.type_scope else None in
  internalise sigma env (extract_ids env, tmp_scope,[])
    allow_patvar (ltacvars,Environ.named_context env, [], impls) c

let intern_constr sigma env c = intern_gen false sigma env c 

let intern_type sigma env c = intern_gen true sigma env c 

let intern_pattern env patt =
  try
    intern_cases_pattern env [] ([],[]) None patt 
  with 
      InternalisationError (loc,e) ->
	user_err_loc (loc,"internalize",explain_internalisation_error e)


let intern_ltac isarity ltacvars sigma env c =
  intern_gen isarity sigma env ~ltacvars:ltacvars c

(*********************************************************************)
(* Functions to parse and interpret constructions *)

let interp_gen kind sigma env 
               ?(impls=([],[])) ?(allow_patvar=false) ?(ltacvars=([],[]))
               c =
  Default.understand_gen kind sigma env 
    (intern_gen (kind=IsType) ~impls ~allow_patvar ~ltacvars sigma env c)

let interp_constr sigma env c =
  interp_gen (OfType None) sigma env c 

let interp_type sigma env ?(impls=([],[])) c =
  interp_gen IsType sigma env ~impls c

let interp_casted_constr sigma env ?(impls=([],[])) c typ =
  interp_gen (OfType (Some typ)) sigma env ~impls c 

let interp_open_constr sigma env c =
  Default.understand_tcc sigma env (intern_constr sigma env c)

let interp_constr_judgment sigma env c =
  Default.understand_judgment sigma env (intern_constr sigma env c)


let interp_constr_evars_gen evdref env ?(impls=([],[])) kind c =
  Default.understand_tcc_evars evdref env kind
    (intern_gen (kind=IsType) ~impls (Evd.evars_of !evdref) env c)

let interp_casted_constr_evars evdref env ?(impls=([],[])) c typ =
  interp_constr_evars_gen evdref env ~impls (OfType (Some typ)) c

let interp_type_evars evdref env ?(impls=([],[])) c =
  interp_constr_evars_gen evdref env IsType ~impls c

let interp_constr_judgment_evars evdref env c =
  Default.understand_judgment_tcc evdref env
    (intern_constr (Evd.evars_of !evdref) env c)

type ltac_sign = identifier list * unbound_ltac_var_map

let interp_constrpattern sigma env c =
  pattern_of_rawconstr (intern_gen false sigma env ~allow_patvar:true c)

let interp_aconstr impls vars a =
  let env = Global.env () in
  (* [vl] is intended to remember the scope of the free variables of [a] *)
  let vl = List.map (fun id -> (id,ref None)) vars in
  let c = internalise Evd.empty (Global.env()) (extract_ids env, None, [])
    false (([],[]),Environ.named_context env,vl,([],impls)) a in
  (* Translate and check that [c] has all its free variables bound in [vars] *)
  let a = aconstr_of_rawconstr vars c in
  (* Returns [a] and the ordered list of variables with their scopes *)
  (* Variables occurring in binders have no relevant scope since bound *)
  List.map
    (fun (id,r) -> (id,match !r with None -> None,[] | Some (a,l) -> a,l)) vl,
  a

(* Interpret binders and contexts  *)

let interp_binder sigma env na t =
  let t = intern_gen true sigma env t in
  let t' = locate_if_isevar (loc_of_rawconstr t) na t in
  Default.understand_type sigma env t'

let interp_binder_evars evdref env na t =
  let t = intern_gen true (Evd.evars_of !evdref) env t in
  let t' = locate_if_isevar (loc_of_rawconstr t) na t in
  Default.understand_tcc_evars evdref env IsType t'

open Environ
open Term

let interp_context sigma env params = 
  List.fold_left
    (fun (env,params) d -> match d with
      | LocalRawAssum ([_,na],(CHole _ as t)) ->
	  let t = interp_binder sigma env na t in
	  let d = (na,None,t) in
	  (push_rel d env, d::params)
      | LocalRawAssum (nal,t) ->
	  let t = interp_type sigma env t in
	  let ctx = list_map_i (fun i (_,na) -> (na,None,lift i t)) 0 nal in
	  let ctx = List.rev ctx in
	  (push_rel_context ctx env, ctx@params)
      | LocalRawDef ((_,na),c) ->
	  let c = interp_constr_judgment sigma env c in
	  let d = (na, Some c.uj_val, c.uj_type) in
	  (push_rel d env,d::params))
    (env,[]) params

let interp_context_evars evdref env params =
  List.fold_left
    (fun (env,params) d -> match d with
      | LocalRawAssum ([_,na],(CHole _ as t)) ->
	  let t = interp_binder_evars evdref env na t in
	  let d = (na,None,t) in
	  (push_rel d env, d::params)
      | LocalRawAssum (nal,t) ->
	  let t = interp_type_evars evdref env t in
	  let ctx = list_map_i (fun i (_,na) -> (na,None,lift i t)) 0 nal in
	  let ctx = List.rev ctx in
	  (push_rel_context ctx env, ctx@params)
      | LocalRawDef ((_,na),c) ->
	  let c = interp_constr_judgment_evars evdref env c in
	  let d = (na, Some c.uj_val, c.uj_type) in
	  (push_rel d env,d::params))
    (env,[]) params

(**********************************************************************)
(* Locating reference, possibly via an abbreviation *)

let locate_reference qid =
  match Nametab.extended_locate qid with
    | TrueGlobal ref -> ref
    | SyntacticDef kn -> 
	match Syntax_def.search_syntactic_definition dummy_loc kn with
	  | Rawterm.RRef (_,ref) -> ref
	  | _ -> raise Not_found

let is_global id =
  try 
    let _ = locate_reference (make_short_qualid id) in true
  with Not_found -> 
    false

let global_reference id = 
  constr_of_global (locate_reference (make_short_qualid id))

let construct_reference ctx id =
  try
    Term.mkVar (let _ = Sign.lookup_named id ctx in id)
  with Not_found ->
    global_reference id

let global_reference_in_absolute_module dir id = 
  constr_of_global (Nametab.absolute_reference (Libnames.make_path dir id))

