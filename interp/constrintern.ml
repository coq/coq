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
open Topconstr
open Nametab
open Symbols

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
  let s = if n1 > 1 then "s" else "" in
  str "Expecting " ++ int n1 ++ str " pattern" ++ str s ++ str " but found "
    ++ int n2

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
  let dir = Lib.file_part ref in
  if dir <> None then
    let dp = string_of_dirpath (out_some dir) in
    dump_string (Printf.sprintf "R%d %s.%s\n" (fst (unloc loc)) dp id)

let loc_of_notation f loc args ntn =
  if args=[] or ntn.[0] <> '_' then fst (unloc loc)
  else snd (unloc (f (List.hd args)))

let ntn_loc = loc_of_notation constr_loc
let patntn_loc = loc_of_notation cases_pattern_loc

let dump_notation_location =
  fun pos ntn ((path,df),sc) ->
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

let make_current_scope (scopt,scopes) = option_cons scopt scopes

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

let intern_var (env,_,_ as genv) (ltacvars,vars2,vars3,_,impls) loc id =
  let (vars1,unbndltacvars) = ltacvars in
  (* Is [id] an inductive type potentially with implicit *)
  try
    let l,impl,argsc = List.assoc id impls in
    let l = List.map 
      (fun id -> CRef (Ident (loc,id)), Some (loc,ExplByName id)) l in
    RVar (loc,id), impl, argsc,
    (if !Options.v7 & !interning_grammar then [] else l)
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
	  pr_id id ++ str " ist not bound to a term")
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

let find_appl_head_data (_,_,_,_,impls) = function
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
      (* For old ast syntax compatibility *)
      if (string_of_id id).[0] = '$' then RVar (loc,id),[],[],[] else
      (* End old ast syntax compatibility *)
      (* Pour traduction des implicites d'inductifs et points-fixes *)
      try RVar (loc,id), List.assoc id !temporary_implicits_in, [], []
      with Not_found ->
      (* Fin pour traduction *)
      try intern_var env lvar loc id
      with Not_found -> 
      try find_appl_head_data lvar (intern_qualid loc (make_short_qualid id))
      with e ->
	(* Extra allowance for non globalizing functions *)
	if !interning_grammar then RVar (loc,id), [], [], []
	else raise e

let interp_reference vars r =
  let (r,_,_,_) = intern_reference (Idset.empty,None,[]) (vars,[],[],[],[]) r 
  in r

let apply_scope_env (ids,_,scopes as env) = function
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

(* Expanding notations *)

let decode_patlist_value = function
  | CPatCstr (_,_,l) -> l
  | _ -> anomaly "Ill-formed list argument of notation"

let rec subst_pat_iterator y t = function
  | PatVar (_,id) as x ->
      if id = Name y then t else x
  | PatCstr (loc,id,l,alias) ->
      PatCstr (loc,id,List.map (subst_pat_iterator y t) l,alias)

let subst_cases_pattern loc aliases intern subst scopes a =
  let rec aux aliases subst = function
  | AVar id ->
      begin
	(* subst remembers the delimiters stack in the interpretation *)
	(* of the notations *)
	try 
	  let (a,(scopt,subscopes)) = List.assoc id subst in
	  intern (subscopes@scopes) ([],[]) scopt a
	with Not_found -> 
	  if id = ldots_var then [[],[]], PatVar (loc,Name id) else
	  anomaly ("Unbound pattern notation variable: "^(string_of_id id))
	  (*
	  (* Happens for local notation joint with inductive/fixpoint defs *)
	  if aliases <> ([],[]) then
	    anomaly "Pattern notation without constructors";
	  [[id],[]], PatVar (loc,Name id)
	  *)
      end
  | ARef (ConstructRef c) ->
      [aliases], PatCstr (loc,c, [], alias_of aliases)
  | AApp (ARef (ConstructRef (ind,_ as c)),args) ->
      let nparams = (snd (Global.lookup_inductive ind)).Declarations.mind_nparams in
      let _,args = list_chop nparams args in
      let (idsl,pl) = List.split (List.map (aux ([],[]) subst) args) in
      aliases::List.flatten idsl, PatCstr (loc,c,pl,alias_of aliases)
  | AList (x,_,iter,terminator,lassoc) ->
      (try 
        (* All elements of the list are in scopes (scopt,subscopes) *)
	let (a,(scopt,subscopes)) = List.assoc x subst in
        let idslt,termin = aux ([],[]) subst terminator in
        let l = decode_patlist_value a in
        let idsl,v =
	  List.fold_right (fun a (allidsl,t) -> 
            let idsl,u = aux ([],[]) ((x,(a,(scopt,subscopes)))::subst) iter in
            idsl::allidsl, subst_pat_iterator ldots_var t u)
            (if lassoc then List.rev l else l) ([idslt],termin) in
        aliases::List.flatten idsl, v
      with Not_found -> 
          anomaly "Inconsistent substitution of recursive notation")
  | t -> user_err_loc (loc,"",str "Invalid notation for pattern")
  in aux aliases subst a

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
        let (_,mib) = Inductive.lookup_mind_specif (Global.env()) (fst c) in
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
              unf (reference_of_constr v)
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
        warn (str "pattern " ++ pr_reference ref ++
              str " is understood as a pattern variable");
        VarPat (find_pattern_variable ref)

let mustbe_constructor loc ref = 
  try find_constructor ref
  with (Environ.NotEvaluableConst _ | Not_found) ->
    raise (InternalisationError (loc,NotAConstructor ref))

let rec intern_cases_pattern scopes aliases tmp_scope = function
  | CPatAlias (loc, p, id) ->
      let aliases' = merge_aliases aliases id in
      intern_cases_pattern scopes aliases' tmp_scope p
  | CPatCstr (loc, head, pl) ->
      let c,pl0 = mustbe_constructor loc head in
      let argscs =
	simple_adjust_scopes (find_arguments_scope (ConstructRef c), pl) in
      let (idsl,pl') =
	List.split (List.map2 (intern_cases_pattern scopes ([],[])) argscs pl)
      in
      (aliases::(List.flatten idsl), PatCstr (loc,c,pl0@pl',alias_of aliases))
  | CPatNotation (loc,"- _",[CPatNumeral(_,Bignat.POS p)]) ->
      let scopes = option_cons tmp_scope scopes in
      ([aliases],
      Symbols.interp_numeral_as_pattern loc (Bignat.NEG p)
        (alias_of aliases) scopes)
  | CPatNotation (_,"( _ )",[a]) ->
      intern_cases_pattern scopes aliases tmp_scope a
  | CPatNotation (loc, ntn, args) ->
      let ntn,args = contract_pat_notation ntn args in
      let scopes = option_cons tmp_scope scopes in
      let ((ids,c),df) = Symbols.interp_notation loc ntn scopes in
      if !dump then dump_notation_location (patntn_loc loc args ntn) ntn df;
      let subst = List.map2 (fun (id,scl) a -> (id,(a,scl))) ids args in
      subst_cases_pattern loc aliases intern_cases_pattern subst scopes c
  | CPatNumeral (loc, n) ->
      let scopes = option_cons tmp_scope scopes in
      ([aliases],
      Symbols.interp_numeral_as_pattern loc n (alias_of aliases) scopes)
  | CPatDelimiters (loc, key, e) ->
      intern_cases_pattern (find_delimiters_scope loc key::scopes)
        aliases None e
  | CPatAtom (loc, Some head) ->
      (match maybe_constructor head with
	 | ConstrPat (c,args) ->
	     ([aliases], PatCstr (loc,c,args,alias_of aliases))
	 | VarPat id ->
	     let aliases = merge_aliases aliases id in
	     ([aliases], PatVar (loc,alias_of aliases)))
  | CPatAtom (loc, None) ->
      ([aliases], PatVar (loc,alias_of aliases))

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
      with Not_found -> RHole (loc, BinderType na))
  | x -> x

let check_hidden_implicit_parameters id (_,_,_,indnames,_) =
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
  | RRef (loc, ref), Some nth ->
      (try
	let n = Recordops.find_projection_nparams ref in
	if nargs < nth then 
	  user_err_loc (loc,"",str "Projection has not enough parameters");
      with Not_found -> 
	user_err_loc
	(loc,"",pr_global_env Idset.empty ref ++ str " is not a registered projection"))
  | _, Some _ -> user_err_loc (loc_of_rawconstr r, "", str "Not a projection")
  | _, None -> ()

let get_implicit_name n imps =
  if !Options.v7 then None
  else Some (Impargs.name_of_implicit (List.nth imps (n-1)))

let set_hole_implicit i = function
  | RRef (loc,r) -> (loc,ImplicitArg (r,i))
  | RVar (loc,id) -> (loc,ImplicitArg (VarRef id,i))
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

let coerce_to_id = function
  | CRef (Ident (_,id)) -> id 
  | c ->
      user_err_loc (constr_loc c, "subst_rawconstr",
        str"This expression should be a simple identifier")

let traverse_binder subst id (ids,tmpsc,scopes as env) =
  try
    (* Binders bound in the notation are consider first-order object *)
    (* and binders not bound in the notation do not capture variables *)
    (* outside the notation *)
    let id' = coerce_to_id (fst (List.assoc id subst)) in
    id', (Idset.add id' ids,tmpsc,scopes)
  with Not_found ->
    id, env

let decode_constrlist_value = function
  | CAppExpl (_,_,l) -> l
  | _ -> anomaly "Ill-formed list argument of notation"

let rec subst_iterator y t = function
  | RVar (_,id) as x -> if id = y then t else x
  | x -> map_rawconstr (subst_iterator y t) x

let rec subst_aconstr_in_rawconstr loc interp subst (ids,_,scopes as env) =
  function
  | AVar id ->
      begin
	(* subst remembers the delimiters stack in the interpretation *)
	(* of the notations *)
	try 
	  let (a,(scopt,subscopes)) = List.assoc id subst in
	  interp (ids,scopt,subscopes@scopes) a
	with Not_found -> 
	  (* Happens for local notation joint with inductive/fixpoint defs *)
	  RVar (loc,id)
      end
  | AList (x,_,iter,terminator,lassoc) ->
      (try 
        (* All elements of the list are in scopes (scopt,subscopes) *)
	let (a,(scopt,subscopes)) = List.assoc x subst in
        let termin = 
          subst_aconstr_in_rawconstr loc interp subst (ids,None,scopes) 
            terminator in
        let l = decode_constrlist_value a in
	List.fold_right (fun a t -> 
          subst_iterator ldots_var t
            (subst_aconstr_in_rawconstr loc interp 
              ((x,(a,(scopt,subscopes)))::subst)
              (ids,None,scopes) iter))
            (if lassoc then List.rev l else l) termin
      with Not_found -> 
          anomaly "Inconsistent substitution of recursive notation")
  | t ->
      rawconstr_of_aconstr_with_binders loc (traverse_binder subst)
      (subst_aconstr_in_rawconstr loc interp subst) (ids,None,scopes) t

let intern_notation intern (_,tmp_scope,scopes as env) loc ntn args =
  let ntn,args = contract_notation ntn args in
  let scopes = option_cons tmp_scope scopes in
  let ((ids,c),df) = Symbols.interp_notation loc ntn scopes in
  if !dump then dump_notation_location (ntn_loc loc args ntn) ntn df;
  let subst = List.map2 (fun (id,scl) a -> (id,(a,scl))) ids args in
  subst_aconstr_in_rawconstr loc intern subst env c

let set_type_scope (ids,tmp_scope,scopes) =
  (ids,Some Symbols.type_scope,scopes)

let reset_tmp_scope (ids,tmp_scope,scopes) =
  (ids,None,scopes)

(**********************************************************************)
(* Main loop                                                          *)

let internalise sigma env allow_soapp lvar c =
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
	  try
	    (list_index iddef lf) -1
          with Not_found ->
	    raise (InternalisationError (locid,UnboundFixName (false,iddef)))
	in
	let ids' = List.fold_right Idset.add lf ids in
        let idl = Array.map
          (fun (id,n,bl,ty,bd) ->
            let ((ids'',_,_),rbl) =
              List.fold_left intern_local_binder (env,[]) bl in
	    let ids''' = List.fold_right Idset.add lf ids'' in
            (List.rev rbl,
             intern_type (ids'',tmp_scope,scopes) ty,
             intern (ids''',None,scopes) bd)) dl in
	RRec (loc,RFix (Array.map (fun (_,n,_,_,_) -> n) dl,n),
              Array.of_list lf,
              Array.map (fun (bl,_,_) -> bl) idl,
              Array.map (fun (_,ty,_) -> ty) idl,
              Array.map (fun (_,_,bd) -> bd) idl)
    | CCoFix (loc, (locid,iddef), dl) ->
        let lf = List.map (fun (id,_,_,_) -> id) dl in
        let dl = Array.of_list dl in
	let n =
          try 
	    (list_index iddef lf) -1
          with Not_found ->
	    raise (InternalisationError (locid,UnboundFixName (true,iddef)))
	in
	let ids' = List.fold_right Idset.add lf ids in
        let idl = Array.map
          (fun (id,bl,ty,bd) ->
            let ((ids'',_,_),rbl) =
              List.fold_left intern_local_binder (env,[]) bl in
	    let ids''' = List.fold_right Idset.add lf ids'' in
            (List.rev rbl,
             intern_type (ids'',tmp_scope,scopes) ty,
             intern (ids''',None,scopes) bd)) dl in
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
    | CNotation (loc,"- _",[CNumeral(_,Bignat.POS p)]) ->
        let scopes = option_cons tmp_scope scopes in
        Symbols.interp_numeral loc (Bignat.NEG p) scopes
    | CNotation (_,"( _ )",[a]) -> intern env a
    | CNotation (loc,ntn,args) ->
        intern_notation intern env loc ntn args
    | CNumeral (loc, n) ->
	let scopes = option_cons tmp_scope scopes in
	Symbols.interp_numeral loc n scopes
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
	let args = intern_impargs c env impargs args_scopes (merge_impargs l args) in
	check_projection isproj (List.length args) c;
	(match c with 
          (* Now compact "(f args') args" *)
	  | RApp (loc', f', args') -> RApp (join_loc loc' loc, f',args'@args)
	  | _ -> RApp (loc, c, args))
    | CCases (loc, (po,rtnpo), tms, eqns) ->
        let tms,env' = List.fold_right
          (fun citm (inds,env) ->
	    let (tm,ind),nal = intern_case_item env citm in
	    (tm,ref ind)::inds,List.fold_left (push_name_env lvar) env nal)
	  tms ([],env) in
        let rtnpo = option_app (intern_type env') rtnpo in
	RCases (loc, (option_app (intern_type env) po, ref rtnpo), tms,
		List.map (intern_eqn (List.length tms) env) eqns)
    | COrderedCase (loc, tag, po, c, cl) ->
	let env = reset_tmp_scope env in
	ROrderedCase (loc, tag, option_app (intern_type env) po,
	          intern env c,
		  Array.of_list (List.map (intern env) cl),ref None)
    | CLetTuple (loc, nal, (na,po), b, c) ->
	let env' = reset_tmp_scope env in
        let ((b',(na',_)),ids) = intern_case_item env' (b,(na,None)) in
        let env'' = List.fold_left (push_name_env lvar) env ids in
        let p' = option_app (intern_type env'') po in
        RLetTuple (loc, nal, (na', p'), b',
                   intern (List.fold_left (push_name_env lvar) env nal) c)
    | CIf (loc, c, (na,po), b1, b2) ->
	let env' = reset_tmp_scope env in
        let ((c',(na',_)),ids) = intern_case_item env' (c,(na,None)) in
        let env'' = List.fold_left (push_name_env lvar) env ids in
        let p' = option_app (intern_type env'') po in
        RIf (loc, c', (na', p'), intern env b1, intern env b2)
    | CHole loc -> 
	RHole (loc, QuestionMark)
    | CPatVar (loc, n) when allow_soapp ->
	RPatVar (loc, n)
    | CPatVar (loc, (false,n)) when Options.do_translate () ->
	RVar (loc, n)
    | CPatVar (loc, (false,n as x)) ->
        if List.mem n (fst (let (a,_,_,_,_) = lvar in a)) & !Options.v7 then
	  RVar (loc, n)
	else
          error_unbound_patvar loc n
    | CPatVar (loc, _) ->
	raise (InternalisationError (loc,NegativeMetavariable))
    | CEvar (loc, n) ->
	REvar (loc, n, None)
    | CSort (loc, s) ->
	RSort(loc,s)
    | CCast (loc, c1, c2) ->
	RCast (loc,intern env c1,intern_type env c2)

    | CDynamic (loc,d) -> RDynamic (loc,d)

  and intern_type (ids,_,scopes) =
    intern (ids,Some Symbols.type_scope,scopes)

  and intern_local_binder ((ids,ts,sc as env),bl) = function
      LocalRawAssum(nal,ty) ->
        let (loc,na) = List.hd nal in
        (* TODO: fail if several names with different implicit types *)
        let ty = locate_if_isevar loc na (intern_type env ty) in
        List.fold_left
          (fun ((ids,ts,sc),bl) (_,na) ->
            ((name_fold Idset.add na ids,ts,sc), (na,None,ty)::bl))
          (env,bl) nal
    | LocalRawDef((loc,na),def) ->
        ((name_fold Idset.add na ids,ts,sc),
         (na,Some(intern env def),RHole(loc,BinderType na))::bl)

  and intern_eqn n (ids,tmp_scope,scopes as env) (loc,lhs,rhs) =
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
	(loc, eqn_ids,pl,intern (env_ids,tmp_scope,scopes) rhs)

  and intern_case_item (vars,_,scopes as env) (tm,(na,t)) =
    let tm' = intern env tm in
    let ids,typ = match t with
    | Some t -> 
	let tids = names_of_cases_indtype t in
	let tids = List.fold_right Idset.add tids Idset.empty in
	let t = intern_type (tids,None,scopes) t in
	begin match t with
	  | RRef (loc,IndRef ind) -> [],Some (loc,ind,[])
	  | RApp (loc,RRef (_,IndRef ind),l) ->
	      let nal = List.map (function
		| RHole _ -> Anonymous
		| RVar (_,id) -> Name id
		| c ->
		    user_err_loc (loc_of_rawconstr c,"",str "Not a name")) l in
	      nal, Some (loc,ind,nal)
	  | _ -> error_bad_inductive_type (loc_of_rawconstr t)
	end
    | None -> 
	[], None in
    let na = match tm', na with
      | RVar (_,id), None when Idset.mem id vars & not !Options.v7 -> Name id
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
	  if rargs=[] & eargs=[] &
	    not (List.for_all is_status_implicit impl') then
	    (* Less regular arguments than expected: don't complete *)
	    (* with implicit arguments *)
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

let interp_rawconstr_gen_with_implicits isarity sigma env (indpars,impls) allow_soapp ltacvar c =
  let tmp_scope = if isarity then Some Symbols.type_scope else None in
  internalise sigma (extract_ids env, tmp_scope,[])
    allow_soapp (ltacvar,Environ.named_context env, [], indpars, impls) c

let interp_rawconstr_gen isarity sigma env allow_soapp ltacvar c =
  interp_rawconstr_gen_with_implicits isarity sigma env ([],[]) allow_soapp ltacvar c

let interp_rawconstr sigma env c =
  interp_rawconstr_gen false sigma env false ([],[]) c

let interp_rawtype sigma env c =
  interp_rawconstr_gen true sigma env false ([],[]) c

let interp_rawtype_with_implicits sigma env impls c =
  interp_rawconstr_gen_with_implicits true sigma env impls false ([],[]) c

let interp_rawconstr_with_implicits sigma env vars impls c =
  interp_rawconstr_gen_with_implicits false sigma env ([],impls) false
    (vars,[]) c

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
  let c = interp_rawconstr_gen false sigma env false
    (List.map fst ltacvars,unbndltacvars) c in
  let typs = retype_list sigma env ltacvars in
  understand_gen sigma env typs exptyp c

(*Interprets a casted constr according to two lists of instantiations
  (variables and metas)*)
let interp_openconstr_gen sigma env (ltacvars,unbndltacvars) c exptyp =
  let c = interp_rawconstr_gen false sigma env false
    (List.map fst ltacvars,unbndltacvars) c in
  let typs = retype_list sigma env ltacvars in
  understand_gen_tcc sigma env typs exptyp c

let interp_casted_constr sigma env c typ = 
  understand_gen sigma env [] (Some typ) (interp_rawconstr sigma env c)

let interp_casted_constr_with_implicits sigma env impls c typ =
  understand_gen sigma env [] (Some typ) 
    (interp_rawconstr_with_implicits sigma env [] impls c)

let interp_constrpattern_gen sigma env ltacvar c =
  let c = interp_rawconstr_gen false sigma env true (ltacvar,[]) c in
  pattern_of_rawconstr c

let interp_constrpattern sigma env c =
  interp_constrpattern_gen sigma env [] c

let interp_aconstr impls vars a =
  let env = Global.env () in
  (* [vl] is intended to remember the scope of the free variables of [a] *)
  let vl = List.map (fun id -> (id,ref None)) vars in
  let c = internalise Evd.empty (extract_ids env, None, [])
    false (([],[]),Environ.named_context env,vl,[],impls) a in
  (* Translate and check that [c] has all its free variables bound in [vars] *)
  let a = aconstr_of_rawconstr vars c in
  (* Returns [a] and the ordered list of variables with their scopes *)
  (* Variables occurring in binders have no relevant scope since bound *)
  List.map
    (fun (id,r) -> (id,match !r with None -> None,[] | Some (a,l) -> a,l)) vl,
  a

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
  constr_of_reference (locate_reference (make_short_qualid id))

let construct_reference ctx id =
  try
    Term.mkVar (let _ = Sign.lookup_named id ctx in id)
  with Not_found ->
    global_reference id

let global_reference_in_absolute_module dir id = 
  constr_of_reference (Nametab.absolute_reference (Libnames.make_path dir id))

