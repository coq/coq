open Util
open Pp
open Names
open Nametab
open Summary
open Rawterm
open Bignat

(* A scope is a set of notations; it includes

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

let pr_bigint = function
  | POS n -> str (Bignat.to_string n)
  | NEG n -> str "-" ++ str (Bignat.to_string n)

(**********************************************************************)
(* Scope of symbols *)

type notation = string
type scope_name = string
type delimiters = string * string
type scope = {
  notations: rawconstr Stringmap.t;
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

let scope_stack = ref [default_scope]

let current_scopes () = !scope_stack

(* TODO: push nat_scope, z_scope, ... in scopes summary *)

(**********************************************************************)
(* Interpreting numbers (not in summary because functional objects)   *)

type numeral_interpreter_name = string
type numeral_interpreter =
    (loc -> bigint -> rawconstr)
    * (loc -> bigint -> name -> cases_pattern) option

let numeral_interpreter_tab =
  (Hashtbl.create 17 : (numeral_interpreter_name,numeral_interpreter)Hashtbl.t)

let declare_numeral_interpreter sc t =
  Hashtbl.add numeral_interpreter_tab sc t

let lookup_numeral_interpreter s =
  try 
    Hashtbl.find numeral_interpreter_tab s
  with Not_found -> 
    error ("No interpretation for numerals in scope "^s)

(* For loading without opening *)
let declare_scope scope =
  try let _ = Stringmap.find scope !scope_map in ()
  with Not_found ->
(*    Options.if_verbose message ("Creating scope "^scope);*)
    scope_map := Stringmap.add scope empty_scope !scope_map

let find_scope scope =
  try Stringmap.find scope !scope_map
  with Not_found -> error ("Scope "^scope^" is not declared")

let check_scope sc = let _ = find_scope sc in ()

let declare_delimiters scope dlm =
  let sc = find_scope scope in
  if sc.delimiters <> None && Options.is_verbose () then
    warning ("Overwriting previous delimiters in "^scope);
  let sc = { sc with delimiters = Some dlm } in
  scope_map := Stringmap.add scope sc !scope_map   

(* The mapping between notations and production *)

let declare_notation nt c scope =
  let sc = find_scope scope in
  if Stringmap.mem nt sc.notations && Options.is_verbose () then
    warning ("Notation "^nt^" is already used in scope "^scope);
  let sc = { sc with notations = Stringmap.add nt c sc.notations } in
  scope_map := Stringmap.add scope sc !scope_map

open Coqast

let rec subst_meta_rawconstr subst = function
  | RMeta (_,n) -> List.nth subst (n-1)
  | t -> map_rawconstr (subst_meta_rawconstr subst) t

let rec find_interpretation f = function
  | scope::scopes ->
      (try f (find_scope scope)
       with Not_found -> find_interpretation f scopes)
  | [] -> raise Not_found

let rec interp_notation ntn scopes args =
  let f scope =
    let c = Stringmap.find ntn scope.notations in
    subst_meta_rawconstr args c in
  try find_interpretation f scopes
  with Not_found -> anomaly ("Unknown interpretation for notation "^ntn)

let find_notation_with_delimiters scope =
  match (Stringmap.find scope !scope_map).delimiters with
    | Some dlm -> Some (Some dlm)
    | None -> None

let rec find_notation_without_delimiters pat_scope pat = function
  | scope::scopes ->
      (* Is the expected printer attached to the most recently open scope? *)
      if scope = pat_scope then
	Some None
      else
	(* If the most recently open scope has a printer for this pattern
    	   but not the expected one then we need delimiters *)
	if Stringmap.mem pat (Stringmap.find scope !scope_map).notations then
	  find_notation_with_delimiters pat_scope
	else
	  find_notation_without_delimiters pat_scope pat scopes
  | [] ->
      find_notation_with_delimiters pat_scope

let find_notation pat_scope pat scopes =
  match 
    find_notation_without_delimiters pat_scope pat scopes
  with
    | None -> None
    | Some None -> Some (None,scopes)
    | Some x -> Some (x,pat_scope::scopes)

let exists_notation_in_scope scope ntn =
  try Stringmap.mem ntn (Stringmap.find scope !scope_map).notations
  with Not_found -> false

let exists_notation nt =
  Stringmap.fold (fun scn sc b -> Stringmap.mem nt sc.notations or b)
    !scope_map false 

(* TO DO
let print_scope sc =
  try
    let sc = Stringmap.find scope !scope_map in
    Stringmap.fold (fun ntn c s -> s ++ str ntn ++ Printer.pr_rawterm c)
      sc.notations in
  with Not_found -> str "Unknown scope"
*)

(* We have to print delimiters; look for the more recent defined one *)
(* Do we need to print delimiters? To know it, we look for a numeral *)
(* printer available in the current stack of scopes *)
let find_numeral_with_delimiters scope =
  match (Stringmap.find scope !scope_map).delimiters with
    | Some dlm -> Some (Some dlm)
    | None -> None

let rec find_numeral_without_delimiters printer_scope = function
  | scope :: scopes -> 
      (* Is the expected printer attached to the most recently open scope? *)
      if scope = printer_scope then
	Some None
      else
	(* If the most recently open scope has a printer for numerals
    	   but not the expected one then we need delimiters *)
	if not (Hashtbl.mem numeral_interpreter_tab scope) then
	  find_numeral_without_delimiters printer_scope scopes
	else
	  find_numeral_with_delimiters printer_scope
  | [] ->
      (* Can we switch to [scope]? Yes if it has defined delimiters *)
      find_numeral_with_delimiters printer_scope

let find_numeral_printer printer_scope scopes =
  match 
    find_numeral_without_delimiters printer_scope scopes
  with
    | None -> None
    | Some None -> Some (None,scopes)
    | Some x -> Some (x,printer_scope::scopes)

(* This is the map associating the scope a numeral printer belongs to *)
(*
let numeral_printer_map = ref (Stringmap.empty : scope_name Stringmap.t)
*)

let rec interp_numeral loc n = function
  | scope :: scopes ->
      (try fst (lookup_numeral_interpreter scope) loc n
       with Not_found -> interp_numeral loc n scopes)
  | [] ->
      user_err_loc (loc,"interp_numeral",
      str "No interpretation for numeral " ++ pr_bigint n)

let rec interp_numeral_as_pattern loc n name = function
  | scope :: scopes ->
      (try 
	match snd (lookup_numeral_interpreter scope) with
	  | None -> raise Not_found
	  | Some g -> g loc n name
	with Not_found -> interp_numeral_as_pattern loc n name scopes)
  | [] ->
      user_err_loc (loc,"interp_numeral_as_pattern",
      str "No interpretation for numeral " ++ pr_bigint n)

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

open Libnames

module RefOrdered =
  struct
    type t = global_reference
    let compare = Pervasives.compare
  end

module Refmap = Map.Make(RefOrdered)

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


(* Synchronisation with reset *)

let freeze () = (!scope_map, !scope_stack, !arguments_scope)

let unfreeze (scm,scs,asc) =
  scope_map := scm;
  scope_stack := scs;
  arguments_scope := asc

let init () = ()
(*
  scope_map := Strinmap.empty;
  scope_stack := Stringmap.empty
*)

let _ = 
  declare_summary "symbols"
    { freeze_function = freeze;
      unfreeze_function = unfreeze;
      init_function = init;
      survive_section = false }
