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
open Pp
open Bignat
open Names
open Nametab
open Libnames
open Summary
open Rawterm
open Topconstr
open Ppextend
(*i*)

(*s A scope is a set of notations; it includes

  - a set of ML interpreters/parsers for positive (e.g. 0, 1, 15, ...) and
    negative numbers (e.g. -0, -2, -13, ...). These interpreters may
    fail if a number has no interpretation in the scope (e.g. there is
    no interpretation for negative numbers in [nat]); interpreters both for
    terms and patterns can be set; these interpreters are in permanent table
    [numeral_interpreter_tab]
  - a set of ML printers for expressions denoting numbers parsable in 
    this scope (permanently declared in [Esyntax.primitive_printer_tab])
  - a set of interpretations for infix (more generally distfix) notations
  - an optional pair of delimiters which, when occurring in a syntactic
    expression, set this scope to be the current scope
*)

(**********************************************************************)
(* Scope of symbols *)

type level = precedence * precedence list
type delimiters = string * string
type scope = {
  notations: (aconstr * (level * string)) Stringmap.t;
  delimiters: delimiters option
}
type scopes = scope_name list

(* Scopes table: scope_name -> symbol_interpretation *)
let scope_map = ref Stringmap.empty

let empty_scope = {
  notations = Stringmap.empty;
  delimiters = None
}

let default_scope = "core_scope"

let _ = Stringmap.add default_scope empty_scope !scope_map

(**********************************************************************)
(* The global stack of scopes                                         *)

let scope_stack = ref [default_scope]

let current_scopes () = !scope_stack

(* TODO: push nat_scope, z_scope, ... in scopes summary *)

(**********************************************************************)
(* Operations on scopes *)

let declare_scope scope =
  try let _ = Stringmap.find scope !scope_map in ()
  with Not_found ->
(*    Options.if_verbose message ("Creating scope "^scope);*)
    scope_map := Stringmap.add scope empty_scope !scope_map

let find_scope scope =
  try Stringmap.find scope !scope_map
  with Not_found -> error ("Scope "^scope^" is not declared")

let check_scope sc = let _ = find_scope sc in ()

(**********************************************************************)
(* Delimiters *)

let declare_delimiters scope dlm =
  let sc = find_scope scope in
  if sc.delimiters <> None && Options.is_verbose () then
    warning ("Overwriting previous delimiters in "^scope);
  let sc = { sc with delimiters = Some dlm } in
  scope_map := Stringmap.add scope sc !scope_map   

let find_delimiters scope = (find_scope scope).delimiters

(* Uninterpretation tables *)

type interpretation = identifier list * aconstr
type interp_rule = scope_name * notation * interpretation * int option

(* We define keys for rawterm and aconstr to split the syntax entries
   according to the key of the pattern (adapted from Chet Murthy by HH) *)

type key =
  | RefKey of global_reference
  | Oth

(* Scopes table : interpretation -> scope_name *)
let notations_key_table = ref Gmapl.empty
let numeral_key_table = Hashtbl.create 7

let rawconstr_key = function
  | RApp (_,RRef (_,ref),_) -> RefKey ref
  | RRef (_,ref) -> RefKey ref
  | _ -> Oth

let aconstr_key = function
  | AApp (ARef ref,args) -> RefKey ref, Some (List.length args)
  | ARef ref -> RefKey ref, Some 0
  | _ -> Oth, None

let pattern_key = function
  | PatCstr (_,cstr,_,_) -> RefKey (ConstructRef cstr)
  | _ -> Oth

(**********************************************************************)
(* Interpreting numbers (not in summary because functional objects)   *)

type num_interpreter =
    (loc -> bigint -> rawconstr)
    * (loc -> bigint -> name -> cases_pattern) option

type num_uninterpreter =
    rawconstr list * (rawconstr -> bigint option)
    * (cases_pattern -> bigint option) option

type required_module = string list 

let numeral_interpreter_tab =
  (Hashtbl.create 7 : (scope_name,required_module*num_interpreter) Hashtbl.t)

let declare_numeral_interpreter sc dir interp (patl,uninterp,uninterpc) =
  declare_scope sc;
  Hashtbl.add numeral_interpreter_tab sc (dir,interp);
  List.iter
    (fun pat -> Hashtbl.add numeral_key_table (rawconstr_key pat)
      (sc,uninterp,uninterpc))
    patl

let check_required_module loc sc d =
  let d' = List.map id_of_string d in
  let dir = make_dirpath (List.rev d') in
  if not (Library.library_is_loaded dir) then
    user_err_loc (loc,"numeral_interpreter",
    str ("Cannot interpret numbers in "^sc^" without requiring first module "
    ^(list_last d)))

let lookup_numeral_interpreter loc sc =
  try
    let (dir,interpreter) = Hashtbl.find numeral_interpreter_tab sc in
    check_required_module loc sc dir;
    interpreter
  with Not_found -> 
    error ("No interpretation for numerals in scope "^sc)

(* Look if some notation or numeral printer in [scope] can be used in
   the scope stack [scopes], and if yes, using delimiters or not *)

let find_with_delimiters scope =
  match (Stringmap.find scope !scope_map).delimiters with
    | Some _ -> Some (Some scope)
    | None -> None

let rec find_without_delimiters find ntn_scope = function
  | scope :: scopes -> 
      (* Is the expected ntn/numpr attached to the most recently open scope? *)
      if scope = ntn_scope then
	Some None
      else
	(* If the most recently open scope has a notation/numeral printer
    	   but not the expected one then we need delimiters *)
	if find scope then
	  find_with_delimiters ntn_scope
	else
	  find_without_delimiters find ntn_scope scopes
  | [] ->
      (* Can we switch to [scope]? Yes if it has defined delimiters *)
      find_with_delimiters ntn_scope

(* The mapping between notations and their interpretation *)

let declare_interpretation ntn scope pat =
  let sc = find_scope scope in
  if Stringmap.mem ntn sc.notations && Options.is_verbose () then
    warning ("Notation "^ntn^" is already used in scope "^scope);
  let sc = { sc with notations = Stringmap.add ntn pat sc.notations } in
  scope_map := Stringmap.add scope sc !scope_map

let declare_uninterpretation ntn scope metas c =
  let (key,n) = aconstr_key c in
  notations_key_table :=
    Gmapl.add key (scope,ntn,(metas,c),n) !notations_key_table

let declare_notation ntn scope (metas,c) prec df onlyparse =
  declare_interpretation ntn scope (c,(prec,df));
  if not onlyparse then declare_uninterpretation ntn scope metas c

let rec find_interpretation f = function
  | scope::scopes ->
      (try f (find_scope scope)
       with Not_found -> find_interpretation f scopes)
  | [] -> raise Not_found

let rec interp_notation ntn scopes =
  let f scope = fst (Stringmap.find ntn scope.notations) in
  try find_interpretation f scopes
  with Not_found -> anomaly ("Unknown interpretation for notation "^ntn)

let uninterp_notations c =
  Gmapl.find (rawconstr_key c) !notations_key_table

let availability_of_notation (ntn_scope,ntn) scopes =
  match 
    let f scope =
      Stringmap.mem ntn (Stringmap.find scope !scope_map).notations in
    find_without_delimiters f ntn_scope scopes
  with
    | None -> None
    | Some None -> Some None
    | Some (Some dlm) -> Some (Some ntn_scope)

let rec interp_numeral loc n = function
  | scope :: scopes ->
      (try fst (lookup_numeral_interpreter loc scope) loc n
       with Not_found -> interp_numeral loc n scopes)
  | [] ->
      user_err_loc (loc,"interp_numeral",
      str "No interpretation for numeral " ++ pr_bigint n)

let rec interp_numeral_as_pattern loc n name = function
  | scope :: scopes ->
      (try 
	match snd (lookup_numeral_interpreter loc scope) with
	  | None -> raise Not_found
	  | Some g -> g loc n name
	with Not_found -> interp_numeral_as_pattern loc n name scopes)
  | [] ->
      user_err_loc (loc,"interp_numeral_as_pattern",
      str "No interpretation for numeral " ++ pr_bigint n)

let uninterp_numeral c =
  try 
    let (sc,numpr,_) = Hashtbl.find numeral_key_table (rawconstr_key c) in
    match numpr c with
      | None -> raise No_match
      | Some n -> (sc,n)
  with Not_found -> raise No_match

let uninterp_cases_numeral c =
  try 
    match Hashtbl.find numeral_key_table (pattern_key c) with
      | (_,_,None) -> raise No_match
      | (sc,_,Some numpr) ->
	  match numpr c with
	    | None -> raise No_match
	    | Some n -> (sc,n)
  with Not_found -> raise No_match

let availability_of_numeral printer_scope scopes =
  match 
    let f scope = Hashtbl.mem numeral_interpreter_tab scope in
    find_without_delimiters f printer_scope scopes
  with
    | None -> None
    | Some x -> Some x

(* Miscellaneous *)

let exists_notation_in_scope scope prec ntn r =
  try
    let sc = Stringmap.find scope !scope_map in
    let (r',(prec',_)) = Stringmap.find ntn sc.notations in
    r' = r & prec = prec'
  with Not_found -> false

let exists_notation_prec prec nt sc =
  try fst (snd (Stringmap.find nt sc.notations)) = prec with Not_found -> false

let exists_notation prec nt =
  Stringmap.fold (fun scn sc b -> b or exists_notation_prec prec nt sc)
    !scope_map false 

(* Exportation of scopes *)
let cache_scope (_,sc) =
  check_scope sc;
  scope_stack := sc :: !scope_stack

let subst_scope (_,subst,sc) = sc

open Libobject

let (inScope,outScope) = 
  declare_object {(default_object "SCOPE") with
      cache_function = cache_scope;
      open_function = (fun i o -> if i=1 then cache_scope o);
      subst_function = subst_scope;
      classify_function = (fun (_,o) -> Substitute o);
      export_function = (fun x -> Some x) }

let open_scope sc = Lib.add_anonymous_leaf (inScope sc)

(* Special scopes associated to arguments of a global reference *)

let arguments_scope = ref Refmap.empty

let cache_arguments_scope (_,(r,scl)) =
  List.iter (option_iter check_scope) scl;
  arguments_scope := Refmap.add r scl !arguments_scope

let subst_arguments_scope (_,subst,(r,scl)) = (subst_global subst r,scl)

let (inArgumentsScope,outArgumentsScope) = 
  declare_object {(default_object "ARGUMENTS-SCOPE") with
      cache_function = cache_arguments_scope;
      open_function = (fun i o -> if i=1 then cache_arguments_scope o);
      subst_function = subst_arguments_scope;
      classify_function = (fun (_,o) -> Substitute o);
      export_function = (fun x -> Some x) }

let declare_arguments_scope r scl =
  Lib.add_anonymous_leaf (inArgumentsScope (r,scl))

let find_arguments_scope r =
  try Refmap.find r !arguments_scope
  with Not_found -> []

(* Printing *)

let pr_delimiters_info = function
  | None -> str "No delimiters"
  | Some (l,r) -> str "Delimiters are " ++ str l ++ str " and " ++ str r

let rec rawconstr_of_aconstr () x =
  map_aconstr_with_binders_loc dummy_loc (fun id () -> (id,())) 
    rawconstr_of_aconstr () x

let pr_notation_info prraw ntn c =
  str ntn ++ str " stands for " ++ prraw (rawconstr_of_aconstr () c)

let pr_named_scope prraw scope sc =
  str "Scope " ++ str scope ++ fnl ()
  ++ pr_delimiters_info sc.delimiters ++ fnl ()
  ++ Stringmap.fold
       (fun ntn (r,(_,df)) strm -> pr_notation_info prraw df r ++ fnl () ++ strm)
       sc.notations (mt ())

let pr_scope prraw scope = pr_named_scope prraw scope (find_scope scope)

let pr_scopes prraw =
 Stringmap.fold 
   (fun scope sc strm -> pr_named_scope prraw scope sc ++ fnl () ++ strm)
   !scope_map (mt ())

(**********************************************************************)
(* Mapping notations to concrete syntax *)

type unparsing_rule = unparsing list * precedence

(* Concrete syntax for symbolic-extension table *)
let printing_rules = 
  ref (Stringmap.empty : unparsing_rule Stringmap.t)

let declare_notation_printing_rule ntn unpl =
  printing_rules := Stringmap.add ntn unpl !printing_rules

let find_notation_printing_rule ntn =
  try Stringmap.find ntn !printing_rules
  with Not_found -> anomaly ("No printing rule found for "^ntn)

(**********************************************************************)
(* Synchronisation with reset *)

let freeze () =
 (!scope_map, !scope_stack, !arguments_scope,
  !notations_key_table, !printing_rules)

let unfreeze (scm,scs,asc,fkm,pprules) =
  scope_map := scm;
  scope_stack := scs;
  arguments_scope := asc;
  notations_key_table := fkm;
  printing_rules := pprules

let init () =
(*
  scope_map := Strinmap.empty;
  scope_stack := Stringmap.empty
  arguments_scope := Refmap.empty
*)
  notations_key_table := Gmapl.empty;
  printing_rules := Stringmap.empty

let _ = 
  declare_summary "symbols"
    { freeze_function = freeze;
      unfreeze_function = unfreeze;
      init_function = init;
      survive_section = false }
