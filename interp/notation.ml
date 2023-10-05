(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(*i*)
open CErrors
open Util
open Pp
open Names
open Libnames
open Globnames
open Libobject
open Constrexpr
open Notation_term
open Glob_term
open Glob_ops
open NumTok
open Notationextern
open PrimNotations

(*i*)

let notation_cat = Libobject.create_category "notations"


(*s A scope is a set of notations; it includes

  - a set of ML interpreters/parsers for positive (e.g. 0, 1, 15, ...) and
    negative numbers (e.g. -0, -2, -13, ...). These interpreters may
    fail if a number has no interpretation in the scope (e.g. there is
    no interpretation for negative numbers in [nat]); interpreters both for
    terms and patterns can be set; these interpreters are in permanent table
    [number_interpreter_tab]
  - a set of ML printers for expressions denoting numbers parsable in
    this scope
  - a set of interpretations for infix (more generally distfix) notations
  - an optional pair of delimiters which, when occurring in a syntactic
    expression, set this scope to be the current scope
*)

let pr_notation (from,ntn) = qstring ntn ++ match from with InConstrEntry -> mt () | InCustomEntry s -> str " in custom " ++ Nametab.CustomEntries.pr s

module NotationOrd =
  struct
    type t = notation
    let compare = Notationextern.notation_compare
  end

module NotationSet = Set.Make(NotationOrd)
module NotationMap = CMap.Make(NotationOrd)

module SpecificNotationOrd =
  struct
    type t = specific_notation
    let compare = Notationextern.specific_notation_compare
  end

module SpecificNotationSet = Set.Make(SpecificNotationOrd)
module SpecificNotationMap = CMap.Make(SpecificNotationOrd)

(**********************************************************************)
(* Scope of symbols *)

type delimiters = string
type notation_location = (DirPath.t * DirPath.t * Loc.t option) * string

type notation_data = {
  not_interp : interpretation;
  not_location : notation_location;
  not_user_warns : UserWarn.t option;
}

type activation = bool

type extra_printing_notation_data =
  (activation * notation_data) list

type parsing_notation_data =
  | NoParsingData
  | OnlyParsingData of activation * notation_data
  | ParsingAndPrintingData of
      activation (* for parsing*) *
      activation (* for printing *) *
      notation_data (* common data for both *)

type scope = {
  notations: (parsing_notation_data * extra_printing_notation_data) NotationMap.t;
  delimiters: delimiters option
}

(* Scopes table: scope_name -> symbol_interpretation *)
let scope_map = ref String.Map.empty

(* Delimiter table : delimiter -> scope_name *)
let delimiters_map = ref String.Map.empty

let empty_scope = {
  notations = NotationMap.empty;
  delimiters = None
}

let default_scope = "" (* empty name, not available from outside *)

let init_scope_map () =
  scope_map := String.Map.add default_scope empty_scope !scope_map

(**********************************************************************)
(* Operations on scopes *)

let warn_scope_start_ =
  CWarnings.create
    ~name:"scope-underscore-start" ~category:CWarnings.CoreCategories.syntax
    ~default:CWarnings.AsError
    (fun () -> strbrk "Scope names should not start with an underscore.")

let warn_undeclared_scope =
  CWarnings.create ~name:"undeclared-scope" ~category:Deprecation.Version.v8_10
                   (fun (scope) ->
                    strbrk "Declaring a scope implicitly is deprecated; use in advance an explicit "
                    ++ str "\"Declare Scope " ++ str scope ++ str ".\".")

let declare_scope scope =
  if scope <> "" && scope.[0] = '_' then warn_scope_start_ ();
  try let _ = String.Map.find scope !scope_map in ()
  with Not_found ->
    scope_map := String.Map.add scope empty_scope !scope_map

let error_unknown_scope ~info sc =
  user_err ~info
    (str "Scope " ++ str sc ++ str " is not declared.")

let find_scope ?(tolerant=false) scope =
  try String.Map.find scope !scope_map
  with Not_found as exn ->
    let _, info = Exninfo.capture exn in
    if tolerant then
      (* tolerant mode to be turn off after deprecation phase *)
      begin
        warn_undeclared_scope scope;
        scope_map := String.Map.add scope empty_scope !scope_map;
        empty_scope
      end
    else
      error_unknown_scope ~info scope

let check_scope ?(tolerant=false) scope =
  let _ = find_scope ~tolerant scope in ()

let ensure_scope scope = check_scope ~tolerant:true scope

let find_scope scope = find_scope scope

let scope_delimiters scope = scope.delimiters

(* [sc] might be here a [scope_name] or a [delimiter]
   (now allowed after Open Scope) *)

let normalize_scope sc =
  try let _ = String.Map.find sc !scope_map in sc
  with Not_found ->
    try
      let sc = String.Map.find sc !delimiters_map in
      let _ = String.Map.find sc !scope_map in sc
    with Not_found as exn ->
      let _, info = Exninfo.capture exn in
      error_unknown_scope ~info sc

(**********************************************************************)
(* The global stack of scopes                                         *)

type scope_item = OpenScopeItem of scope_name | LonelyNotationItem of notation
type scopes = scope_item list

let scope_item_eq s1 s2 = match s1, s2 with
| OpenScopeItem s1, OpenScopeItem s2 -> String.equal s1 s2
| LonelyNotationItem s1, LonelyNotationItem s2 -> notation_eq s1 s2
| OpenScopeItem _, LonelyNotationItem _
| LonelyNotationItem _, OpenScopeItem _ -> false

let scope_stack = ref []

let current_scopes () = !scope_stack

let scope_is_open_in_scopes sc l =
  List.exists (function OpenScopeItem sc' -> String.equal sc sc' | _ -> false) l

let scope_is_open sc = scope_is_open_in_scopes sc (!scope_stack)

(* TODO: push nat_scope, z_scope, ... in scopes summary *)

let open_scope sc = scope_stack := OpenScopeItem sc :: !scope_stack
let close_scope sc = scope_stack := List.remove scope_item_eq (OpenScopeItem sc) !scope_stack

let empty_scope_stack = []

let push_scope sc scopes = OpenScopeItem sc :: scopes

let push_scopes = List.fold_right push_scope

let make_current_scopes (tmp_scopes,scopes) =
  push_scopes tmp_scopes (push_scopes scopes !scope_stack)

(**********************************************************************)
(* Delimiters *)

let warn_scope_delimiter_start_ =
  CWarnings.create
    ~name:"scope-delimiter-underscore-start"
    ~category:CWarnings.CoreCategories.syntax
    ~default:CWarnings.AsError
    (fun () -> strbrk "Scope delimiters should not start with an underscore.")

let warn_hiding_key =  CWarnings.create ~name:"hiding-delimiting-key" ~category:CWarnings.CoreCategories.parsing
    Pp.(fun (key,oldscope) -> str "Hiding binding of key " ++ str key ++ str " to " ++ str oldscope)

let declare_delimiters scope key =
  if key <> "" && key.[0] = '_' then warn_scope_delimiter_start_ ();
  let sc = find_scope scope in
  let newsc = { sc with delimiters = Some key } in
  begin match sc.delimiters with
    | None -> scope_map := String.Map.add scope newsc !scope_map
    | Some oldkey when String.equal oldkey key -> ()
    | Some oldkey -> scope_map := String.Map.add scope newsc !scope_map
  end;
  try
    let oldscope = String.Map.find key !delimiters_map in
    if String.equal oldscope scope then ()
    else begin
      warn_hiding_key (key,oldscope);
      delimiters_map := String.Map.add key scope !delimiters_map
    end
  with Not_found -> delimiters_map := String.Map.add key scope !delimiters_map

let remove_delimiters scope =
  let sc = find_scope scope in
  let newsc = { sc with delimiters = None } in
  match sc.delimiters with
    | None -> CErrors.user_err  (str "No bound key for scope " ++ str scope ++ str ".")
    | Some key ->
       scope_map := String.Map.add scope newsc !scope_map;
       try
         let _ = ignore (String.Map.find key !delimiters_map) in
         delimiters_map := String.Map.remove key !delimiters_map
       with Not_found as exn ->
         let _, info = Exninfo.capture exn in
         (* XXX info *)
         CErrors.anomaly ~info (str "A delimiter for scope [scope] should exist")

let find_delimiters_scope ?loc key =
  try String.Map.find key !delimiters_map
  with Not_found ->
    user_err ?loc
      (str "Unknown scope delimiting key " ++ str key ++ str ".")

(** Dealing with precedences *)

let entry_relative_level_le child = function
  | LevelLt parent -> child < parent
  | LevelLe parent -> child <= parent
  | LevelSome -> true

let notation_level_map = Summary.ref ~stage:Summary.Stage.Synterp ~name:"notation_level_map" NotationMap.empty

let declare_notation_level ntn level =
  let open Summary.Ref in
  if NotationMap.mem ntn !notation_level_map then
    anomaly (str "Notation " ++ pr_notation ntn ++ str " is already assigned a level.");
  notation_level_map := NotationMap.add ntn level !notation_level_map

type required_module = full_path * string list

(* Table from scope_name to backtrack-able informations about interpreters
   (in particular interpreter unique id). *)
let prim_token_interp_infos =
  ref (String.Map.empty : (required_module * prim_token_interp_info) String.Map.t)

module GlobRefMap = Environ.QGlobRef.Map

(* Table from global_reference to backtrack-able informations about
   prim_token uninterpretation (in particular uninterpreter unique id). *)
let prim_token_uninterp_infos =
  ref (GlobRefMap.empty : ((scope_name * (prim_token_interp_info * bool)) list) GlobRefMap.t)

type prim_token_infos = {
  pt_local : bool; (** Is this interpretation local? *)
  pt_scope : scope_name; (** Concerned scope *)
  pt_interp_info : prim_token_interp_info; (** Unique id "pointing" to (un)interp functions, OR a number notation object describing (un)interp functions *)
  pt_required : required_module; (** Module that should be loaded first *)
  pt_refs : GlobRef.t list; (** Entry points during uninterpretation *)
  pt_in_match : bool (** Is this prim token legal in match patterns ? *)
}

let cache_prim_token_interpretation infos =
  let env = Global.env () in
  let ptii = infos.pt_interp_info in
  let sc = infos.pt_scope in
  check_scope ~tolerant:true sc;
  prim_token_interp_infos :=
    String.Map.add sc (infos.pt_required,ptii) !prim_token_interp_infos;
  let add_uninterp r =
    let l = try GlobRefMap.find env r !prim_token_uninterp_infos with Not_found -> [] in
    prim_token_uninterp_infos :=
      GlobRefMap.add env r ((sc,(ptii,infos.pt_in_match)) :: l)
        !prim_token_uninterp_infos in
  List.iter add_uninterp infos.pt_refs

let subst_prim_token_interpretation (subs,infos) =
  { infos with
    pt_refs = List.map (subst_global_reference subs) infos.pt_refs }

let classify_prim_token_interpretation infos =
    if infos.pt_local then Dispose else Substitute

let inPrimTokenInterp : prim_token_infos -> obj =
  declare_object {(default_object "PRIM-TOKEN-INTERP") with
     open_function  = simple_open ~cat:notation_cat cache_prim_token_interpretation;
     cache_function = cache_prim_token_interpretation;
     subst_function = subst_prim_token_interpretation;
     classify_function = classify_prim_token_interpretation}

let enable_prim_token_interpretation infos =
  Lib.add_leaf (inPrimTokenInterp infos)

(** Compatibility.
    Avoid the next two functions, they will now store unnecessary
    objects in the library segment. Instead, combine
    [register_*_interpretation] and [enable_prim_token_interpretation]
    (the latter inside a [Mltop.declare_cache_obj]).
*)

let glob_prim_constr_key c = match DAst.get c with
  | GRef (ref, _) -> Some (canonical_gr ref)
  | GApp (c, _) ->
    begin match DAst.get c with
    | GRef (ref, _) -> Some (canonical_gr ref)
    | _ -> None
    end
  | GProj ((cst,_), _, _) -> Some (canonical_gr (GlobRef.ConstRef cst))
  | _ -> None

let check_required_module ?loc sc (sp,d) =
  try let _ = Nametab.global_of_path sp in ()
  with Not_found as exn ->
    let _, info = Exninfo.capture exn in
    match d with
    | [] ->
      user_err ?loc ~info
        (str "Cannot interpret in " ++ str sc ++ str " because " ++ pr_path sp ++
         str " could not be found in the current environment.")
    | _ ->
      user_err ?loc ~info
        (str "Cannot interpret in " ++ str sc ++ str " without requiring first module " ++
         str (List.last d) ++ str ".")

(* Look if some notation or number printer in [scope] can be used in
   the scope stack [scopes], and if yes, using delimiters or not *)

let find_with_delimiters = function
  | LastLonelyNotation -> None
  | NotationInScope scope ->
      match (String.Map.find scope !scope_map).delimiters with
        | Some key -> Some (Some scope, Some key)
        | None -> None
        | exception Not_found -> None

let rec find_without_delimiters find (ntn_scope,ntn) = function
  | OpenScopeItem scope :: scopes ->
      (* Is the expected ntn/numpr attached to the most recently open scope? *)
      begin match ntn_scope with
      | NotationInScope scope' when String.equal scope scope' ->
        Some (None,None)
      | _ ->
        (* If the most recently open scope has a notation/number printer
           but not the expected one then we need delimiters *)
        if find scope then
          find_with_delimiters ntn_scope
        else
          find_without_delimiters find (ntn_scope,ntn) scopes
      end
  | LonelyNotationItem ntn' :: scopes ->
      begin match ntn with
      | Some ntn'' when notation_eq ntn' ntn'' ->
        begin match ntn_scope with
        | LastLonelyNotation ->
          (* If the first notation with same string in the visibility stack
             is the one we want to print, then it can be used without
             risking a collision *)
           Some (None, None)
        | NotationInScope _ ->
          (* A lonely notation is liable to hide the scoped notation
             to print, we check if the lonely notation is active to
             know if the delimiter of the scoped notationis needed *)
          if find default_scope then
            find_with_delimiters ntn_scope
          else
            find_without_delimiters find (ntn_scope,ntn) scopes
        end
      | _ ->
        (* A lonely notation which does not interfere with the notation to use *)
        find_without_delimiters find (ntn_scope,ntn) scopes
      end
  | [] ->
      (* Can we switch to [scope]? Yes if it has defined delimiters *)
      find_with_delimiters ntn_scope

(* The mapping between notations and their interpretation *)

let pr_optional_scope = function
  | LastLonelyNotation -> mt ()
  | NotationInScope scope -> spc () ++ strbrk "in scope" ++ spc () ++ str scope

let warning_overridden_name = "notation-overridden"

let w_nota_overridden =
  CWarnings.create_warning
    ~from:[CWarnings.CoreCategories.parsing] ~name:warning_overridden_name ()

let warn_notation_overridden =
  CWarnings.create_in w_nota_overridden
    (fun (scope,ntn) ->
       str "Notation" ++ spc () ++ pr_notation ntn ++ spc ()
       ++ strbrk "was already used" ++ pr_optional_scope scope ++ str ".")

let warn_deprecation_overridden =
  CWarnings.create_in w_nota_overridden
    (fun ((scope,ntn),old,now) ->
       match old, now with
       | None, None -> assert false
       | None, Some _ ->
         (str "Notation" ++ spc () ++ pr_notation ntn ++ pr_optional_scope scope ++ spc ()
          ++ strbrk "is now marked as deprecated" ++ str ".")
       | Some _, None ->
         (str "Cancelling previous deprecation of notation" ++ spc () ++
          pr_notation ntn ++ pr_optional_scope scope ++ str ".")
       | Some _, Some _ ->
         (str "Amending deprecation of notation" ++ spc () ++
          pr_notation ntn ++ pr_optional_scope scope ++ str "."))

let warn_override_if_needed (scopt,ntn) overridden data old_data =
  if overridden then warn_notation_overridden (scopt,ntn)
  else
    if data.not_user_warns <> old_data.not_user_warns then
      warn_deprecation_overridden ((scopt,ntn),old_data.not_user_warns,data.not_user_warns)

let check_parsing_override (scopt,ntn) data = function
  | OnlyParsingData (_,old_data) ->
    let overridden = not (interpretation_eq data.not_interp old_data.not_interp) in
    warn_override_if_needed (scopt,ntn) overridden data old_data;
    None
  | ParsingAndPrintingData (_,on_printing,old_data) ->
    let overridden = not (interpretation_eq data.not_interp old_data.not_interp) in
    warn_override_if_needed (scopt,ntn) overridden data old_data;
    if on_printing then Some old_data.not_interp else None
  | NoParsingData -> None

let check_printing_override (scopt,ntn) data parsingdata printingdata =
  let parsing_update = match parsingdata with
  | OnlyParsingData _ | NoParsingData -> parsingdata
  | ParsingAndPrintingData (_,on_printing,old_data) ->
    let overridden = not (interpretation_eq data.not_interp old_data.not_interp) in
    warn_override_if_needed (scopt,ntn) overridden data old_data;
    if overridden then NoParsingData else parsingdata in
  let exists = List.exists (fun (on_printing,old_data) ->
    let exists = interpretation_eq data.not_interp old_data.not_interp in
    if exists && data.not_user_warns <> old_data.not_user_warns then
      warn_deprecation_overridden ((scopt,ntn),old_data.not_user_warns,data.not_user_warns);
    exists) printingdata in
  parsing_update, exists


let update_notation_data (scopt,ntn) use data table =
  let (parsingdata,printingdata) =
    try NotationMap.find ntn table with Not_found -> (NoParsingData, []) in
  match use with
  | OnlyParsing ->
    let printing_update = check_parsing_override (scopt,ntn) data parsingdata in
    NotationMap.add ntn (OnlyParsingData (true,data), printingdata) table, printing_update
  | ParsingAndPrinting ->
    let printing_update = check_parsing_override (scopt,ntn) data parsingdata in
    NotationMap.add ntn (ParsingAndPrintingData (true,true,data), printingdata) table, printing_update
  | OnlyPrinting ->
    let parsingdata, exists = check_printing_override (scopt,ntn) data parsingdata printingdata in
    let printingdata = if exists then printingdata else (true,data) :: printingdata in
    NotationMap.add ntn (parsingdata, printingdata) table, None

let find_one_interpretation ntn find = function
  | OpenScopeItem scope ->
    (try let n = find scope in Some (n,Some scope)
     with Not_found -> None)
  | LonelyNotationItem ntn' when notation_eq ntn' ntn ->
    (try let n = find default_scope in Some (n,None)
     with Not_found ->
       (* e.g. because single notation only for constr, not cases_pattern *)
       None)
  | LonelyNotationItem _ -> None

let find_interpretation ntn find scopes =
  match List.find_map (find_one_interpretation ntn find) scopes with
  | Some v -> v
  | None -> raise Not_found

let find_notation ntn sc =
  match fst (NotationMap.find ntn (find_scope sc).notations) with
  | OnlyParsingData (true,data) | ParsingAndPrintingData (true,_,data) -> data
  | _ -> raise Not_found

let notation_of_prim_token = function
  | Constrexpr.Number (SPlus,n) -> InConstrEntry, NumTok.Unsigned.sprint n
  | Constrexpr.Number (SMinus,n) -> InConstrEntry, "- "^NumTok.Unsigned.sprint n
  | String s -> InConstrEntry, String.quote_coq_string s

let find_prim_token check_allowed ?loc p sc =
  (* Try for a user-defined numerical notation *)
  try
    let n = find_notation (notation_of_prim_token p) sc in
    let (_,c) = n.not_interp in
    let pat = Notation_ops.glob_constr_of_notation_constr ?loc c in
    check_allowed pat;
    pat
  with Not_found ->
  (* Try for a primitive numerical notation *)
  let (spdir,info) = String.Map.find sc !prim_token_interp_infos in
  check_required_module ?loc sc spdir;
  let pat = PrimNotations.do_interp ?loc info p in
  check_allowed pat;
  pat

let interp_prim_token_gen ?loc g p local_scopes =
  let scopes = make_current_scopes local_scopes in
  let p_as_ntn = try notation_of_prim_token p with Not_found -> InConstrEntry,"" in
  try
    let pat, sc = find_interpretation p_as_ntn (find_prim_token ?loc g p) scopes in
    pat
  with Not_found as exn ->
    let _, info = Exninfo.capture exn in
    user_err ?loc ~info
    ((match p with
      | Number _ ->
         str "No interpretation for number " ++ pr_notation (notation_of_prim_token p)
      | String s -> str "No interpretation for string " ++ qs s) ++ str ".")

let interp_prim_token ?loc =
  interp_prim_token_gen ?loc (fun _ -> ())

let interp_prim_token_cases_pattern_expr ?loc check_allowed p =
  interp_prim_token_gen ?loc check_allowed p

let warn_notation =
  UserWarn.create_depr_and_user_warnings ~object_name:"Notation" ~warning_name_base:"notation"
    pr_notation ()

exception UnknownInterp of notation * scopes

let explain_unknown_interp ntn scopes =
  let find_inactive sc =
    match fst (NotationMap.find ntn (find_scope sc).notations) with
    | OnlyParsingData (active,_) | ParsingAndPrintingData (active,_,_) -> assert (not active)
    | NoParsingData -> raise Not_found
  in
  let inactive_in_scope = List.filter_map (fun sc ->
      Option.map snd @@ find_one_interpretation ntn find_inactive sc)
      scopes
  in
  let unused_scope_map = List.fold_left (fun scope_map -> function
      | OpenScopeItem sc -> String.Map.remove sc scope_map
      | LonelyNotationItem ntn' ->
        if notation_eq ntn ntn' then String.Map.remove default_scope scope_map
        else scope_map)
      !scope_map scopes
  in
  let out_of_scope = String.Map.fold (fun sc data acc ->
      match fst (NotationMap.find ntn data.notations) with
      | OnlyParsingData _ | ParsingAndPrintingData _ ->
        let sc = if String.equal sc default_scope then None else Some sc in
        sc :: acc
      | NoParsingData | exception Not_found -> acc)
      unused_scope_map []
  in
  let pr_scope = function
    | None -> str "the default scope"
    | Some sc -> str sc
  in
  let out_of_scope =
    if (CList.is_empty out_of_scope) then mt()
    else
      spc() ++ str "This notation is available in " ++
      pr_enum pr_scope out_of_scope ++ str "."
  in
  let inactive_in_scope =
    if CList.is_empty inactive_in_scope then mt()
    else
      spc() ++ str "This notation is currently disabled in " ++
      pr_enum pr_scope inactive_in_scope ++ str "."
  in
  str "Unknown interpretation for notation " ++ pr_notation ntn ++ str "." ++
  inactive_in_scope ++ out_of_scope

let () = CErrors.register_handler @@ function
  | UnknownInterp (ntn,scopes) -> Some (explain_unknown_interp ntn scopes)
  | _ -> None

let interp_notation ?loc ntn local_scopes =
  let scopes = make_current_scopes local_scopes in
  try
    let (n,sc) = find_interpretation ntn (find_notation ntn) scopes in
    Option.iter (fun d -> warn_notation ?loc ntn d) n.not_user_warns;
    n.not_interp, (n.not_location, sc)
  with Not_found as exn ->
    let _, info = Exninfo.capture exn in
    let info = Option.cata (Loc.add_loc info) info loc in
    Exninfo.iraise (UnknownInterp (ntn,scopes), info)

let has_active_parsing_rule_in_scope ntn sc =
  try
    match NotationMap.find ntn (String.Map.find sc !scope_map).notations with
    | OnlyParsingData (active,_),_ | ParsingAndPrintingData (active,_,_),_ -> active
    | _ -> false
  with Not_found -> false

let is_printing_active_in_scope (scope,ntn) pat =
  let sc = match scope with NotationInScope sc -> sc | LastLonelyNotation -> default_scope in
  let is_active extra =
    try
      let (_,(active,_)) = List.extract_first (fun (active,d) -> interpretation_eq d.not_interp pat) extra in
      active
    with Not_found -> false in
  try
    match NotationMap.find ntn (String.Map.find sc !scope_map).notations with
    | ParsingAndPrintingData (_,active,d), extra ->
       if interpretation_eq d.not_interp pat then active
       else is_active extra
    | _, extra -> is_active extra
  with Not_found -> false

let is_printing_inactive_rule rule pat =
  match rule with
  | NotationRule (scope,ntn) ->
    not (is_printing_active_in_scope (scope,ntn) pat)
  | AbbrevRule kn ->
    match Abbreviation.find_opt kn with
    | None -> true
    | Some d -> not @@ Abbreviation.enabled d

let availability_of_notation (ntn_scope,ntn) scopes =
  find_without_delimiters (has_active_parsing_rule_in_scope ntn) (ntn_scope,Some ntn) (make_current_scopes scopes)

(* We support coercions from a custom entry at some level to an entry
   at some level (possibly the same), and from and to the constr entry. E.g.:

   Notation "[ expr ]" := expr (expr custom group at level 1).
   Notation "( x )" := x (in custom group at level 0, x at level 1).
   Notation "{ x }" := x (in custom group at level 0, x constr).

   Supporting any level is maybe overkill in that coercions are
   commonly from the lowest level of the source entry to the highest
   level of the target entry. *)

type entry_coercion = (notation_with_optional_scope * notation) list

module EntryCoercionOrd =
 struct
  type t = notation_entry * notation_entry
  let compare (e1,e2) (e1',e2') =
    let c = Notationextern.notation_entry_compare e1 e1' in
    if c <> 0 then c
    else Notationextern.notation_entry_compare e2 e2'
 end

module EntryCoercionMap = Map.Make(EntryCoercionOrd)

(* We index coercions by pairs of entry names to avoid a full linear search *)
let entry_coercion_map : (((entry_level * entry_relative_level) * entry_coercion) list EntryCoercionMap.t) ref =
  ref EntryCoercionMap.empty

let sublevel_ord lev lev' =
  match lev, lev' with
  | _, LevelSome -> true
  | LevelSome, _ -> false
  | LevelLt n, LevelLt n' | LevelLe n, LevelLe n' -> n <= n'
  | LevelLt n, LevelLe n' -> n < n'
  | LevelLe n, LevelLt n' -> n <= n'-1

let is_coercion
    { notation_entry = e1; notation_level = n1 }
    { notation_subentry = e2; notation_relative_level = n2 } =
  not (notation_entry_eq e1 e2) ||
  match n2 with
  | LevelLt n2 | LevelLe n2 -> n1 < n2
  | LevelSome -> true (* unless n2 is the entry top level but we shall know it only dynamically *)

let included
    { notation_entry = e1; notation_level = n1 }
    { notation_subentry = e2; notation_relative_level = n2 } =
  notation_entry_eq e1 e2 && entry_relative_level_le n1 n2

let rec search nfrom nto = function
  | [] -> raise Not_found
  | ((pfrom,pto),coe)::l ->
    if entry_relative_level_le pfrom nfrom && entry_relative_level_le nto pto then coe else search nfrom nto l

let availability_of_entry_coercion ?(non_included=false)
    ({ notation_subentry = entry; notation_relative_level = sublev } as entry_sublev)
    ({ notation_entry = entry'; notation_level = lev' } as entry_lev) =
  if included entry_lev entry_sublev && not non_included then
    (* [entry] is by default included in [relative_entry] *)
    Some []
  else
    try Some (search sublev lev' (EntryCoercionMap.find (entry,entry') !entry_coercion_map))
    with Not_found -> None

let better_path ((lev1,sublev2),path) ((lev1',sublev2'),path') =
  (* better = shorter and lower source and higher target *)
  lev1 <= lev1' && sublevel_ord sublev2' sublev2 && List.length path <= List.length path'

let rec insert_coercion_path path = function
  | [] -> [path]
  | path'::paths as allpaths ->
      (* If better or equal we keep the more recent one *)
      if better_path path path' then path::paths
      else if better_path path' path then allpaths
      else path'::insert_coercion_path path paths

let declare_entry_coercion ntn entry_level entry_relative_level' =
  let { notation_entry = entry; notation_level = lev } = entry_level in
  let { notation_subentry = entry'; notation_relative_level = sublev' } = entry_relative_level' in
  (* Transitive closure *)
  let toaddleft =
    EntryCoercionMap.fold (fun (entry'',entry''') paths l ->
        List.fold_right (fun ((lev'',sublev'''),path) l ->
            if included entry_level
                { notation_subentry = entry'''; notation_relative_level = sublev'''; notation_position = None } &&
               not (included { notation_entry = entry''; notation_level = lev'' } entry_relative_level')
        then ((entry'',entry'),((lev'',sublev'),path@[ntn]))::l else l) paths l)
      !entry_coercion_map [] in
  let toaddright =
    EntryCoercionMap.fold (fun (entry'',entry''') paths l ->
        List.fold_right (fun ((lev'',sublev'''),path) l ->
        if included { notation_entry = entry''; notation_level = lev'' } entry_relative_level' &&
           not (included entry_level
                  { notation_subentry = entry'''; notation_relative_level = sublev'''; notation_position = None })
        then ((entry,entry'''),((lev,sublev'''),ntn::path))::l else l) paths l)
      !entry_coercion_map [] in
  entry_coercion_map :=
    List.fold_right (fun (pair,path) ->
        let olds = try EntryCoercionMap.find pair !entry_coercion_map with Not_found -> [] in
        EntryCoercionMap.add pair (insert_coercion_path path olds))
      (((entry,entry'),((lev,sublev'),[ntn]))::toaddright@toaddleft)
      !entry_coercion_map

(* Hard-wired coercion in constr corresponding to "( x )" *)
let _ = entry_coercion_map := (EntryCoercionMap.add (InConstrEntry,InConstrEntry) [(0,LevelSome),[]] !entry_coercion_map)

let entry_has_global_map = ref CustomName.Map.empty

let declare_custom_entry_has_global s n =
  try
    let p = CustomName.Map.find s !entry_has_global_map in
    user_err (str "Custom entry " ++ Nametab.CustomEntries.pr s ++
              str " has already a rule for global references at level " ++ int p ++ str ".")
  with Not_found ->
    entry_has_global_map := CustomName.Map.add s n !entry_has_global_map

let entry_has_global { notation_subentry = entry; notation_relative_level = n } =
  match entry with
  | InConstrEntry -> true
  | InCustomEntry s ->
     try entry_relative_level_le (CustomName.Map.find s !entry_has_global_map) n with Not_found -> false

let entry_has_ident_map = ref CustomName.Map.empty

let declare_custom_entry_has_ident s n =
  try
    let p = CustomName.Map.find s !entry_has_ident_map in
    user_err (str "Custom entry " ++ Nametab.CustomEntries.pr s ++
              str " has already a rule for global references at level " ++ int p ++ str ".")
  with Not_found ->
    entry_has_ident_map := CustomName.Map.add s n !entry_has_ident_map

let entry_has_ident { notation_subentry = entry; notation_relative_level = n } =
  match entry with
  | InConstrEntry -> true
  | InCustomEntry s ->
     try entry_relative_level_le (CustomName.Map.find s !entry_has_ident_map) n with Not_found -> false

let app_level = 10

let prec_less child = function
  | LevelLt parent -> child < parent
  | LevelLe parent -> child <= parent
  | LevelSome -> true

let may_capture_cont_after child parent =
  match child with
  | None -> false
  | Some lev_after -> prec_less lev_after parent

type entry_coercion_kind =
  | IsEntryCoercion of notation_entry_level * notation_entry_relative_level
  | IsEntryGlobal of CustomName.t * int
  | IsEntryIdent of CustomName.t * int

let declare_notation (scopt,ntn) pat df ~use coe user_warns =
  (* Register the interpretation *)
  let scope = match scopt with NotationInScope s -> s | LastLonelyNotation -> default_scope in
  let sc = find_scope scope in
  let notdata = {
    not_interp = pat;
    not_location = df;
    not_user_warns = user_warns;
  } in
  let notation_update,printing_update = update_notation_data (scopt,ntn) use notdata sc.notations in
  let sc = { sc with notations = notation_update } in
  scope_map := String.Map.add scope sc !scope_map;
  (* Register visibility of lonely notations *)
  begin match scopt with
  | LastLonelyNotation -> scope_stack := LonelyNotationItem ntn :: !scope_stack
  | NotationInScope _ -> ()
  end;
  (* Declare a possible coercion *)
  if use <> OnlyParsing then begin match coe with
   | Some (IsEntryCoercion (entry,subentry)) -> declare_entry_coercion (scopt,ntn) entry subentry
   | Some (IsEntryGlobal (entry,n)) -> declare_custom_entry_has_global entry n
   | Some (IsEntryIdent (entry,n)) -> declare_custom_entry_has_ident entry n
   | None ->
     (* Update the uninterpretation cache *)
     begin match printing_update with
     | Some pat -> remove_uninterpretation (Global.env ()) (NotationRule (scopt,ntn)) pat
     | None -> ()
     end;
     declare_uninterpretation (Global.env ()) (NotationRule (scopt,ntn)) pat
  end

let availability_of_prim_token n printer_scope local_scopes =
  let f scope =
    match String.Map.find_opt scope !prim_token_interp_infos with
    | None -> false
    | Some (_, uid) -> PrimNotations.can_interp uid n
  in
  let scopes = make_current_scopes local_scopes in
  Option.map snd (find_without_delimiters f (NotationInScope printer_scope,None) scopes)

let rec find_uninterpretation need_delim def find = function
  | [] ->
      CList.find_map_exn
        (fun (sc,_,_) -> try Some (find need_delim sc) with Not_found -> None)
        def
  | OpenScopeItem scope :: scopes ->
      (try find need_delim scope
       with Not_found -> find_uninterpretation need_delim def find scopes)  (* TODO: here we should also update the need_delim list with all regular notations in scope [scope] that could shadow a number notation *)
  | LonelyNotationItem ntn::scopes ->
      find_uninterpretation (ntn::need_delim) def find scopes

let uninterp_prim_token ~print_float c local_scopes =
  match glob_prim_constr_key c with
  | None -> raise Notation_ops.No_match
  | Some r ->
     let uninterp (sc,(info,_)) =
       match PrimNotations.do_uninterp ~print_float info c with
       | None -> None
       | Some n -> Some (sc,n)
     in
     let add_key (sc,n) =
       Option.map (fun k -> sc,n,k) (availability_of_prim_token n sc local_scopes) in
     let l =
       try GlobRefMap.find (Global.env ()) r !prim_token_uninterp_infos
       with Not_found -> raise Notation_ops.No_match in
     let l = List.map_filter uninterp l in
     let l = List.map_filter add_key l in
     let find need_delim sc =
       let _,n,k = List.find (fun (sc',_,_) -> String.equal sc' sc) l in
       if k <> None then n,k else
         let hidden =
           List.exists
             (fun n' -> notation_eq n' (notation_of_prim_token n))
             need_delim in
         if not hidden then n,k else
           match (String.Map.find sc !scope_map).delimiters with
           | Some k -> n,Some k
           | None -> raise Not_found
     in
     let scopes = make_current_scopes local_scopes in
     try find_uninterpretation [] l find scopes
     with Not_found -> match l with (_,n,k)::_ -> n,k | [] -> raise Notation_ops.No_match

let uninterp_prim_token_cases_pattern ~print_float c local_scopes =
  match glob_constr_of_closed_cases_pattern (Global.env()) c with
  | exception Not_found -> raise Notation_ops.No_match
  | na,c -> let (sc,n) = uninterp_prim_token ~print_float c local_scopes in (na,sc,n)

(* Miscellaneous *)

let isNVar_or_NHole = function NVar _ | NHole _ -> true | _ -> false

(**********************************************************************)
(* Mapping classes to scopes *)

open Coercionops

type scope_class = cl_typ

let scope_class_compare : scope_class -> scope_class -> int =
  cl_typ_ord

let compute_scope_class env sigma t =
  let (cl,_,_) = find_class_type env sigma t in
  cl

module ScopeClassOrd =
struct
  type t = scope_class
  let compare = scope_class_compare
end

module ScopeClassMap = Map.Make(ScopeClassOrd)

(* pairs of Top and Bottom additions (Boolean is for locality) *)
type scope_class_map =
  ((scope_name * bool) list * (scope_name * bool) list) ScopeClassMap.t

let initial_scope_class_map : scope_class_map =
  ScopeClassMap.empty

let scope_class_map = ref initial_scope_class_map

type add_scope_where = AddScopeTop | AddScopeBottom

let declare_scope_class islocal sc ?where cl =
  let map = match where with
    | None ->
      ScopeClassMap.add cl ([sc, islocal], []) !scope_class_map
    | Some where ->
      let add (scl1,scl2) = match where with AddScopeTop -> ((sc,islocal) :: scl1, scl2) | AddScopeBottom -> (scl1, scl2 @ [sc,islocal]) in
      let scl = try ScopeClassMap.find cl !scope_class_map with Not_found -> ([],[]) in
      ScopeClassMap.add cl (add scl) !scope_class_map in
  scope_class_map := map

let find_scope_class_blocks_opt map = function
  | None -> [], []
  | Some cl ->
    try
      let ltop, lbot = ScopeClassMap.find cl map in
      List.map fst ltop, List.map fst lbot
    with Not_found -> [], []

let find_scope_class_opt map cl =
  let ltop, lbot = find_scope_class_blocks_opt map cl in
  ltop @ lbot

(**********************************************************************)
(* Special scopes associated to arguments of a global reference *)

let compute_telescope env sigma typ =
  let open CClosure in
  let infos = Evarutil.create_clos_infos env sigma RedFlags.betaiotazeta in
  let tab = create_tab () in
  let rec apply_rec typ accu =
    let typ, stk = whd_stack infos tab typ [] in
    match fterm_of typ with
    | FProd (na, c1, c2, e) ->
      let c1 = EConstr.of_constr @@ term_of_fconstr ~info:infos ~tab c1 in
      let c2 = mk_clos (CClosure.usubs_lift e) c2 in
      apply_rec c2 ((EConstr.of_binder_annot na, c1) :: accu)
    | _ -> List.rev accu
    in
    apply_rec (CClosure.inject (EConstr.Unsafe.to_constr typ)) []

let compute_arguments_classes env sigma t =
  let telescope = compute_telescope env sigma t in
  let rec aux env = function
  | (na, t) :: decls ->
    let cl = try Some (compute_scope_class env sigma t) with Not_found -> None in
    let env = EConstr.push_rel (Context.Rel.Declaration.LocalAssum (na, t)) env in
    cl :: aux env decls
  | [] -> []
  in
  aux env telescope

let compute_arguments_scope_full env sigma map t =
  let cls = compute_arguments_classes env sigma t in
  let scs = List.map (find_scope_class_opt map) cls in
  scs, cls

let compute_arguments_scope env sigma t =
  fst (compute_arguments_scope_full env sigma !scope_class_map t)

let compute_type_scope env sigma t =
  find_scope_class_opt !scope_class_map (try Some (compute_scope_class env sigma t) with Not_found -> None)

let current_type_scope_names () =
   find_scope_class_opt !scope_class_map (Some CL_SORT)

let compute_glob_type_scope t =
  find_scope_class_opt !scope_class_map (try Some (find_class_glob_type t) with Not_found -> None)

let scope_class_of_class (x : cl_typ) : scope_class =
  x

(** Updating a scope list, thanks to a list of argument classes
    and the current Bind Scope base. When some current scope
    have been manually given, the corresponding argument class
    is emptied below, so this manual scope will be preserved. That is,
    cls and scl have this form:

         dynam. recomputed
         when out of sync     manual
           /----------\    /-----------\
    scl =  sc1 ... scn     sc1' ... scn'
    cls =  cl1 ... cln     empty list
           \----------/
        static. computed
       at cache/rebuild time
*)

let update_scope sco cl =
  let (sctop,scbot) = find_scope_class_blocks_opt !scope_class_map cl in
  let sco = List.filter (fun sc -> not (List.exists (String.equal sc) sctop || List.exists (String.equal sc) scbot)) sco in
  sctop@sco@scbot

let rec update_scopes cls scl = match cls, scl with
  | [], _ -> scl
  | _, [] -> List.map (update_scope []) cls
  | cl :: cls, sco :: scl -> update_scope sco cl :: update_scopes cls scl

let arguments_scope = ref GlobRefMap.empty

type arguments_scope_discharge_request =
  | ArgsScopeAuto
  | ArgsScopeManual
  | ArgsScopeNoDischarge

let load_arguments_scope _ (_,r,scl,cls,allscopes) =
  List.iter (List.iter check_scope) scl;
  (* force recomputation to take into account the possible extra "Bind
     Scope" of the current environment (e.g. so that after inlining of a
     parameter in a functor, it takes the current environment into account *)
  let initial_stamp = initial_scope_class_map in
  arguments_scope := GlobRefMap.add (Global.env ()) r (scl,cls,initial_stamp) !arguments_scope

let cache_arguments_scope o =
  load_arguments_scope 1 o

let subst_scope_class env subst cs =
  try Some (subst_cl_typ env subst cs) with Not_found -> None

let subst_arguments_scope (subst,(req,r,scl,cls,allscopes)) =
  let r' = fst (subst_global subst r) in
  let subst_cl ocl = match ocl with
    | None -> ocl
    | Some cl ->
        let env = Global.env () in
        match subst_scope_class env subst cl with
        | Some cl'  as ocl' when cl' != cl -> ocl'
        | _ -> ocl in
  let cls' = List.Smart.map subst_cl cls in
  (ArgsScopeNoDischarge,r',scl,cls',allscopes)

let discharge_available_scopes map =
  (* Remove local scopes *)
  ScopeClassMap.filter_map (fun cl (ltop, lbot) ->
      let ltop = List.filter (fun x -> not (snd x)) ltop in
      let lbot = List.filter (fun x -> not (snd x)) lbot in
      if List.is_empty ltop && List.is_empty lbot then None else Some (ltop, lbot)) map

let discharge_arguments_scope (req,r,scs,_cls,available_scopes) =
  if req == ArgsScopeNoDischarge || (isVarRef r && Global.is_in_section r) then None
  else
    let n =
      try
        Array.length (Global.section_instance r)
      with
        Not_found (* Not a ref defined in this section *) -> 0 in
    let available_scopes = discharge_available_scopes available_scopes in
    (* Hack: use list cls to encode an integer to pass to rebuild for Manual case *)
    (* since cls is anyway recomputed in rebuild *)
    let n_as_cls = List.make n None in
    Some (req,r,scs,n_as_cls,available_scopes)

let classify_arguments_scope (req,_,_,_,_) =
  if req == ArgsScopeNoDischarge then Dispose else Substitute

let rebuild_arguments_scope (req,r,scs,n_as_cls,available_scopes) =
  match req with
    | ArgsScopeNoDischarge -> assert false
    | ArgsScopeAuto ->
      let env = Global.env () in
      let sigma = Evd.from_env env in
      let typ = EConstr.of_constr @@ fst (Typeops.type_of_global_in_context env r) in
      let scs,cls = compute_arguments_scope_full env sigma available_scopes typ in
      (* Note: cls is fixed, but scs can be recomputed in find_arguments_scope *)
      (req,r,scs,cls,available_scopes)
    | ArgsScopeManual ->
      (* Add to the manually given scopes the one found automatically
         for the extra parameters of the section. Discard the classes
         of the manually given scopes to avoid further re-computations. *)
      let env = Global.env () in
      let sigma = Evd.from_env env in
      let n = List.length n_as_cls in
      let typ = EConstr.of_constr @@ fst (Typeops.type_of_global_in_context env r) in
      let scs',cls = compute_arguments_scope_full env sigma available_scopes typ in
      let scs1 = List.firstn n scs' in
      let cls1 = List.firstn n cls in
      (* Note: the extra cls1 is fixed, but its associated scs can be recomputed *)
      (* on the undefined part of cls, scs is however fixed *)
      (req,r,scs1@scs,cls1,available_scopes)

type arguments_scope_obj =
    arguments_scope_discharge_request * GlobRef.t *
    scope_name list list * scope_class option list *
    scope_class_map

let inArgumentsScope : arguments_scope_obj -> obj =
  declare_object {(default_object "ARGUMENTS-SCOPE") with
      cache_function = cache_arguments_scope;
      load_function = load_arguments_scope;
      subst_function = subst_arguments_scope;
      classify_function = classify_arguments_scope;
      discharge_function = discharge_arguments_scope;
      rebuild_function = rebuild_arguments_scope }

let is_local local ref = local || isVarRef ref && Global.is_in_section ref

let declare_arguments_scope_gen req r (scl,cls) =
  Lib.add_leaf (inArgumentsScope (req,r,scl,cls,!scope_class_map))

let declare_arguments_scope local r scl =
  let req = if is_local local r then ArgsScopeNoDischarge else ArgsScopeManual in
  (* We empty the list of argument classes to disable further scope
     re-computations and keep these manually given scopes. *)
  declare_arguments_scope_gen req r (scl,[])

let find_arguments_scope env r =
  try
    let (scl,cls,stamp) = GlobRefMap.find env r !arguments_scope in
    let cur_stamp = !scope_class_map in
    if stamp == cur_stamp then scl
    else
      (* Recent changes in the Bind Scope base, we re-compute the scopes *)
      let scl' = update_scopes cls scl in
      arguments_scope := GlobRefMap.add env r (scl',cls,cur_stamp) !arguments_scope;
      scl'
  with Not_found -> []

let declare_ref_arguments_scope ref =
  let env = Global.env () in (* FIXME? *)
  let sigma = Evd.from_env env in
  let typ = EConstr.of_constr @@ fst @@ Typeops.type_of_global_in_context env ref in
  (* cls is fixed but scs is only an initial value that can be modified in find_arguments_scope *)
  let (scs,cls as o) = compute_arguments_scope_full env sigma !scope_class_map typ in
  declare_arguments_scope_gen ArgsScopeAuto ref o

(********************************)
(* Encoding notations as string *)

type symbol =
  | Terminal of string
  | NonTerminal of Id.t
  | SProdList of Id.t * symbol list
  | Break of int

let rec symbol_eq s1 s2 = match s1, s2 with
  | Terminal s1, Terminal s2 -> String.equal s1 s2
  | NonTerminal id1, NonTerminal id2 -> Id.equal id1 id2
  | SProdList (id1, l1), SProdList (id2, l2) ->
    Id.equal id1 id2 && List.equal symbol_eq l1 l2
  | Break i1, Break i2 -> Int.equal i1 i2
  | _ -> false

let rec string_of_symbol = function
  | NonTerminal _ -> ["_"]
  | Terminal "_" -> ["'_'"]
  (* Symbols starting with a double quote without denoting a string are single quoted *)
  | Terminal s when s.[0] = '"' && (String.length s = 1 || s.[String.length s - 1] <> '"') -> ["'" ^ s ^ "'"]
  | Terminal s -> [s]
  | SProdList (_,l) ->
     let l = List.flatten (List.map string_of_symbol l) in "_"::l@".."::l@["_"]
  | Break _ -> []

let make_notation_key from symbols =
  (from,String.concat " " (List.flatten (List.map string_of_symbol symbols)))

let decompose_notation_pure_key s =
  let len = String.length s in
  let rec find_string_end n =
    let next =
      try String.index_from s (n+1) '"'
      with Not_found -> assert false
    in
    if next = len - 1 then next+1
    else if s.[next+1] = '"' then (* skip doubled double quotes: *) find_string_end (next+2)
    else next+1 in
  let rec decomp_ntn dirs n =
    if n>=len then List.rev dirs else
    let pos =
      if s.[n] = '"' then find_string_end n
      else
      try
        String.index_from s n ' '
      with Not_found -> len
    in
    let tok =
      match String.sub s n (pos-n) with
      | "_" -> NonTerminal (Id.of_string "_")
      | s -> Terminal (String.drop_simple_quotes s) in
    decomp_ntn (tok::dirs) (pos+1)
  in
    decomp_ntn [] 0

let decompose_notation_key (from,s) =
  from, decompose_notation_pure_key s

let is_prim_token_constant_in_constr (entry, symbs) =
  match entry, List.filter (function Break _ -> false | _ -> true) symbs with
  (* Is this a numeral? *)
  | InConstrEntry, ([Terminal "-"; Terminal x] | [Terminal x]) when NumTok.Unsigned.parse_string x <> None -> true
  (* Is this a string constant? *)
  | InConstrEntry, [Terminal x] when let n = String.length x in n > 1 && x.[0] = '"' && x.[n-1] = '"' -> true
  | _ -> false

let level_of_notation ntn =
  let open Summary.Ref in
  if is_prim_token_constant_in_constr (decompose_notation_key ntn) then
    (* A primitive notation *)
    ({ notation_entry = fst ntn; notation_level = 0}, []) (* TODO: string notations*)
  else
    NotationMap.find ntn !notation_level_map

(************)
(* Printing *)

let pr_delimiters_info = function
  | None -> str "No delimiting key"
  | Some key -> str "Delimiting key is " ++ str key

let classes_of_scope sc =
  let map = !scope_class_map in
  ScopeClassMap.fold (fun cl (scltop,sclbot) l ->
      if List.exists (fun (sc',_) -> String.equal sc sc') scltop ||
         List.exists (fun (sc',_) -> String.equal sc sc') sclbot
      then cl::l else l) map []

let pr_scope_class = pr_class

let pr_scope_classes sc =
  let l = classes_of_scope sc in
  match l with
  | [] -> mt ()
  | _ :: ll ->
    let opt_s = match ll with [] -> mt () | _ -> str "es" in
    hov 0 (str "Bound to class" ++ opt_s ++
      spc() ++ prlist_with_sep spc pr_scope_class l)

let pr_notation_status on_parsing on_printing =
  let disabled b = if b then [] else ["disabled"] in
  let l = match on_parsing, on_printing with
  | Some on, None -> "only parsing" :: disabled on
  | None, Some on -> "only printing" :: disabled on
  | Some false, Some false -> ["disabled"]
  | Some true, Some false -> ["disabled for printing"]
  | Some false, Some true -> ["disabled for parsing"]
  | Some true, Some true -> []
  | None, None -> assert false in
  match l with
  | [] -> mt ()
  | l -> str "(" ++ prlist_with_sep pr_comma str l ++ str ")"

let pr_non_empty spc pp =
  if pp = mt () then mt () else spc ++ pp

let pr_notation_data prglob (on_parsing,on_printing,{ not_interp  = (_, r); not_location = (_, df) }) =
  hov 0 (Notation_ops.pr_notation_info prglob df r ++ pr_non_empty (brk(1,2)) (pr_notation_status on_parsing on_printing))

let extract_notation_data (main,extra) =
  let main = match main with
  | NoParsingData -> []
  | ParsingAndPrintingData (on_parsing, on_printing, d) ->
    [Some on_parsing, Some on_printing, d]
  | OnlyParsingData (on_parsing, d) ->
    [Some on_parsing, None, d] in
  let extra = List.map (fun (on_printing, d) -> (None, Some on_printing, d)) extra in
  main @ extra

let pr_named_scope prglob (scope,sc) =
 (if String.equal scope default_scope then
   match NotationMap.cardinal sc.notations with
     | 0 -> str "No lonely notation"
     | n -> str (String.plural n "Lonely notation")
  else
    str "Scope " ++ str scope ++ fnl () ++ pr_delimiters_info sc.delimiters)
  ++ pr_non_empty (fnl ()) (pr_scope_classes scope)
  ++ prlist (fun a -> fnl () ++ pr_notation_data prglob a)
       (NotationMap.fold (fun ntn data l -> extract_notation_data data @ l) sc.notations [])

let pr_scope prglob scope = pr_named_scope prglob (scope, find_scope scope)

let pr_scopes prglob =
 let l = String.Map.bindings !scope_map in
 prlist_with_sep (fun () -> fnl () ++ fnl ()) (pr_named_scope prglob) l

let rec find_default ntn = function
  | [] -> None
  | OpenScopeItem scope :: scopes ->
    if has_active_parsing_rule_in_scope ntn scope then Some scope
    else find_default ntn scopes
  | LonelyNotationItem ntn' :: scopes ->
    if notation_eq ntn ntn' then Some default_scope
    else find_default ntn scopes

let factorize_entries = function
  | [] -> []
  | (ntn,sc',c)::l ->
      let (ntn,l_of_ntn,rest) =
        List.fold_left
          (fun (a',l,rest) (a,sc,c) ->
            if notation_eq a a' then (a',(sc,c)::l,rest) else (a,[sc,c],(a',l)::rest))
          (ntn,[sc',c],[]) l in
      (ntn,l_of_ntn)::rest

type symbol_token = WhiteSpace of int | String of string

let split_notation_string str =
  let push_token beg i l =
    if Int.equal beg i then l else
      let s = String.sub str beg (i - beg) in
      String s :: l
  in
  let push_whitespace beg i l =
    if Int.equal beg i then l else WhiteSpace (i-beg) :: l
  in
  let rec loop beg i =
    if i < String.length str then
      if str.[i] == ' ' then
        push_token beg i (loop_on_whitespace (i+1) (i+1))
      else if beg = i && str.[i] = '"' then
        loop_on_string i (i+1)
      else
        loop beg (i+1)
    else
      push_token beg i []
  and loop_on_whitespace beg i =
    if i < String.length str then
      if str.[i] != ' ' then
        push_whitespace beg i (loop i i)
      else
        loop_on_whitespace beg (i+1)
    else
      push_whitespace beg i []
  and loop_on_string beg i =
    (* we accept any string, possibly with spaces, single quotes, and
       doubled double quotes inside, but necessarily ended with a unique
       double quote followed either by a space or the end of the
       notation string *)
    if i < String.length str then
      if str.[i] = '"' then
        if i+1 < String.length str then
          if str.[i+1] = '"' then (* double quote in the string: *) loop_on_string beg (i+2)
          else if str.[i+1] = ' ' then (* end of the string: *) push_token beg (i+1) (loop_on_whitespace (i+2) (i+2))
          else user_err (Pp.str "End of quoted string not followed by a space in notation.")
        else push_token beg (i+1) []
      else loop_on_string beg (i+1)
    else user_err (Pp.str "Unterminated string in notation.")
    (* we accept any sequences of non-space symbols starting with a
       single quote, up to the next space or end of notation string;
       double quotes and single quotes not followed by a space or the
       end of notation string are allowed;
       note that if the resulting sequence ends with a single quote,
       the two extreme single quotes will eventually be removed *)
  in
  loop 0 0

let rec raw_analyze_notation_tokens = function
  | []    -> []
  | String ".." :: sl -> NonTerminal Notation_ops.ldots_var :: raw_analyze_notation_tokens sl
  | String "_" :: _ -> user_err Pp.(str "_ must be quoted.")
  | String x :: sl when Id.is_valid x ->
      NonTerminal (Names.Id.of_string x) :: raw_analyze_notation_tokens sl
  | String s :: sl ->
      Terminal (String.drop_simple_quotes s) :: raw_analyze_notation_tokens sl
  | WhiteSpace n :: sl ->
      Break n :: raw_analyze_notation_tokens sl

let rec raw_analyze_anonymous_notation_tokens = function
  | []    -> []
  | String ".." :: sl -> NonTerminal Notation_ops.ldots_var :: raw_analyze_anonymous_notation_tokens sl
  | String "_" :: sl -> NonTerminal (Id.of_string "dummy") :: raw_analyze_anonymous_notation_tokens sl
  | String s :: sl ->
      Terminal (String.drop_simple_quotes s) :: raw_analyze_anonymous_notation_tokens sl
  | WhiteSpace n :: sl -> raw_analyze_anonymous_notation_tokens sl

(* Interpret notations with a recursive component *)

type notation_symbols = {
  recvars : (Id.t * Id.t) list; (* pairs (x,y) as in [ x ; .. ; y ] *)
  mainvars : Id.t list; (* variables non involved in a recursive pattern *)
  symbols : symbol list; (* the decomposition of the notation into terminals and nonterminals *)
}

let out_nt = function NonTerminal x -> x | _ -> assert false

let msg_expected_form_of_recursive_notation =
  "In the notation, the special symbol \"..\" must occur in\na configuration of the form \"x symbs .. symbs y\"."

let rec find_pattern nt xl = function
  | Break n as x :: l, Break n' :: l' when Int.equal n n' ->
      find_pattern nt (x::xl) (l,l')
  | Terminal s as x :: l, Terminal s' :: l' when String.equal s s' ->
      find_pattern nt (x::xl) (l,l')
  | [], NonTerminal x' :: l' ->
      (out_nt nt,x',List.rev xl),l'
  | _, Break s :: _ | Break s :: _, _ ->
      user_err Pp.(str ("A break occurs on one side of \"..\" but not on the other side."))
  | _, Terminal s :: _ | Terminal s :: _, _ ->
      user_err
        (str "The token \"" ++ str s ++ str "\" occurs on one side of \"..\" but not on the other side.")
  | _, [] ->
      user_err Pp.(str msg_expected_form_of_recursive_notation)
  | ((SProdList _ | NonTerminal _) :: _), _ | _, (SProdList _ :: _) ->
      anomaly (Pp.str "Only Terminal or Break expected on left, non-SProdList on right.")

let rec interp_list_parser hd = function
  | [] -> [], List.rev hd
  | NonTerminal id :: tl when Id.equal id Notation_ops.ldots_var ->
      if List.is_empty hd then user_err Pp.(str msg_expected_form_of_recursive_notation);
      let hd = List.rev hd in
      let ((x,y,sl),tl') = find_pattern (List.hd hd) [] (List.tl hd,tl) in
      let xyl,tl'' = interp_list_parser [] tl' in
      (* We remember each pair of variable denoting a recursive part to *)
      (* remove the second copy of it afterwards *)
      (x,y)::xyl, SProdList (x,sl) :: tl''
  | (Terminal _ | Break _) as s :: tl ->
      if List.is_empty hd then
        let yl,tl' = interp_list_parser [] tl in
        yl, s :: tl'
      else
        interp_list_parser (s::hd) tl
  | NonTerminal _ as x :: tl ->
      let xyl,tl' = interp_list_parser [x] tl in
      xyl, List.rev_append hd tl'
  | SProdList _ :: _ -> anomaly (Pp.str "Unexpected SProdList in interp_list_parser.")

let get_notation_vars l =
  List.map_filter (function NonTerminal id | SProdList (id,_) -> Some id | _ -> None) l

let decompose_raw_notation ntn =
  let l = split_notation_string ntn in
  let symbols = raw_analyze_notation_tokens l in
  let recvars, symbols = interp_list_parser [] symbols in
  let mainvars = get_notation_vars symbols in
  {recvars; mainvars; symbols}

let interpret_notation_string ntn =
  (* We collect the possible interpretations of a notation string depending on whether it is
    in "x 'U' y" or "_ U _" format *)
  let toks = split_notation_string ntn in
  let toks =
    if
      List.exists (function String "_" -> true | _ -> false) toks ||
      List.for_all (function String id -> Id.is_valid id | _ -> false) toks
    then
      (* Only "_ U _" format *)
      raw_analyze_anonymous_notation_tokens toks
    else
      (* Includes the case of only a subset of tokens or an "x 'U' y"-style format *)
      raw_analyze_notation_tokens toks
  in
  let _,toks = interp_list_parser [] toks in
  let _,ntn' = make_notation_key None toks in
  ntn'

(* Tell if a non-recursive notation is an instance of a recursive one *)
let is_approximation ntn ntn' =
  let rec aux toks1 toks2 = match (toks1, toks2) with
    | Terminal s1 :: toks1, Terminal s2 :: toks2 -> String.equal s1 s2 && aux toks1 toks2
    | NonTerminal _ :: toks1, NonTerminal _ :: toks2 -> aux toks1 toks2
    | SProdList (_,l1) :: toks1, SProdList (_, l2) :: toks2 -> aux l1 l2 && aux toks1 toks2
    | NonTerminal _ :: toks1, SProdList (_,l2) :: toks2 -> aux' toks1 l2 l2 toks2 || aux toks1 toks2
    | [], [] -> true
    | (Break _ :: _, _) | (_, Break _ :: _) -> assert false
    | (Terminal _ | NonTerminal _ | SProdList _) :: _, _ -> false
    | [], _ -> false
  and aux' toks1 l2 l2full toks2 = match (toks1, l2) with
    | Terminal s1 :: toks1, Terminal s2 :: l2 when String.equal s1 s2 -> aux' toks1 l2 l2full toks2
    | NonTerminal _ :: toks1, [] -> aux' toks1 l2full l2full toks2 || aux toks1 toks2
    | _ -> false
  in
  let _,toks = interp_list_parser [] (raw_analyze_anonymous_notation_tokens (split_notation_string ntn)) in
  let _,toks' = interp_list_parser [] (raw_analyze_anonymous_notation_tokens (split_notation_string ntn')) in
  aux toks toks'

let match_notation_key strict ntn ntn' =
  if String.contains ntn ' ' then
    if String.string_contains ~where:ntn' ~what:".." then is_approximation ntn ntn'
    else String.equal ntn ntn'
  else
    let toks = decompose_notation_pure_key ntn' in
    let get_terminals = function Terminal ntn -> Some ntn | _ -> None in
    let trms = List.map_filter get_terminals toks in
    if strict then String.List.equal [ntn] trms
    else String.List.mem ntn trms

let browse_notation strict ntn map =
  let ntn = interpret_notation_string ntn in
  let find (from,ntn') = match_notation_key strict ntn ntn' in
  let l =
    String.Map.fold
      (fun scope_name sc ->
        NotationMap.fold (fun ntn data l ->
          if find ntn
          then List.map (fun d -> (ntn,scope_name,d)) (extract_notation_data data) @ l
          else l) sc.notations)
      map [] in
  List.sort (fun x y -> String.compare (snd (pi1 x)) (snd (pi1 y))) l

let global_reference_of_notation ~head test (ntn,sc,(on_parsing,on_printing,{not_interp = (_,c as interp); not_location = (_, df)})) =
  match c with
  | NRef (ref,_) when test ref -> Some (on_parsing,on_printing,ntn,df,sc,interp,ref)
  | NApp (NRef (ref,_), l) when head || List.for_all isNVar_or_NHole l && test ref ->
      Some (on_parsing,on_printing,ntn,df,sc,interp,ref)
  | _ -> None

type notation_as_reference_error =
  | AmbiguousNotationAsReference of notation_key
  | NotationNotReference of Environ.env * Evd.evar_map * notation_key * (notation_key * notation_constr) list

exception NotationAsReferenceError of notation_as_reference_error

let error_ambiguous_notation ?loc ntn =
  Loc.raise ?loc (NotationAsReferenceError (AmbiguousNotationAsReference ntn))

let error_notation_not_reference ?loc ntn ntns =
  let ntns = List.map (fun (_,_,(_,_,{ not_interp  = (_, r); not_location = (_, df) })) -> df, r) ntns in
  let env = Global.env () in let sigma = Evd.from_env env in
  Loc.raise ?loc (NotationAsReferenceError (NotationNotReference (env, sigma, ntn, ntns)))

let interp_notation_as_global_reference_expanded ?loc ~head test ntn sc =
  let scopes = match sc with
  | Some sc ->
    let scope = find_delimiters_scope sc in
    String.Map.singleton scope (find_scope scope)
  | None -> !scope_map in
  let ntns = browse_notation true ntn scopes in
  let refs = List.map (global_reference_of_notation ~head test) ntns in
  let make_scope sc = if String.equal sc default_scope then LastLonelyNotation else NotationInScope sc in
  match Option.List.flatten refs with
  | [Some true,_ (* why not if the only one? *),ntn,df,sc,interp,ref] -> (ntn,df,make_scope sc,interp,ref)
  | [] -> error_notation_not_reference ?loc ntn ntns
  | refs ->
      let f (on_parsing,_,ntn,df,sc,_,ref) =
        let def = find_default ntn !scope_stack in
        match def with
        | None -> false
        | Some sc' -> on_parsing = Some true && String.equal sc sc'
      in
      match List.filter f refs with
      | [_,_,ntn,df,sc,interp,ref] -> (ntn,df,make_scope sc,interp,ref)
      | [] -> error_notation_not_reference ?loc ntn ntns
      | _ -> error_ambiguous_notation ?loc ntn

let interp_notation_as_global_reference ?loc ~head test ntn sc =
  let _,_,_,_,ref = interp_notation_as_global_reference_expanded ?loc ~head test ntn sc in ref

let pr_id_infos (id, ((level,(tmp_scopes, scopes)), under_binders, kind)) =
  let scopes = List.map (fun x -> "_"^x) tmp_scopes @ scopes in
  match scopes with
  | [] -> None
  | _ ->
    (* IDK how to insert delimiters in the constr for printing
       so instead use "in constr" modifier even though it's ignored
       (#20297)
       Also not sure if we can ever see multiple scopes but if we do we produce invalid syntax.

       This is why we print comment syntax "(* x in scope foo *)" instead of "(x in scope foo)". *)
    let pp =
      Id.print id ++ str " in " ++ str (CString.lplural scopes "scope") ++ spc() ++
      prlist_with_sep spc str scopes
    in
    Some pp


let notation_gram_locs = Summary.ref ~stage:Synterp ~name:"ntn-gram-locs" NotationMap.empty

let declare_ntn_gram_loc ntn (loc : Loc.t option) =
  let open Summary.Ref in
  match loc with
  | None -> ()
  | Some loc ->
    notation_gram_locs :=
      NotationMap.update ntn (fun old ->
          let old = Option.default [] old in
          Some (loc :: old))
        !notation_gram_locs

let get_ntn_gram_locs ntn decl_loc =
  let open Summary.Ref in
  let list = NotationMap.find ntn !notation_gram_locs in
  (match decl_loc with
     None -> list
     (* Filter out the implicit [Reserve Notation] that every [Notation] performs. *)
   | Some decl_loc -> List.filter (fun x -> x <> decl_loc) list)

let pr_ids_infos ids =
  let pp = List.filter_map pr_id_infos ids in
  match pp with
  | [] -> mt()
  | _ -> spc() ++ surround (str "*" ++ spc() ++ prlist_with_sep pr_comma (fun x -> x) pp ++ spc() ++ str "*")

let locate_notation prglob ntn scope =
  let ntns = factorize_entries (browse_notation false ntn !scope_map) in
  let scopes = Option.fold_right push_scope scope !scope_stack in
  match ntns with
  | [] -> str "Unknown notation"
  | _ ->
    prlist_with_sep fnl (fun (ntn,l) ->
      let scope = find_default ntn scopes in
      prlist_with_sep fnl
        (fun (sc,(on_parsing,on_printing,{ not_interp  = (ids, r); not_location = ((libpath,secpath,loc), df) })) ->
          let full_path = DirPath.make (DirPath.repr secpath @ DirPath.repr libpath) in
          hov 2 (
            str "Notation" ++ spc() ++
            Notation_ops.pr_notation_info prglob df r ++
            pr_ids_infos ids ++
            (if String.equal sc default_scope then mt ()
             else (spc() ++ str ": " ++ str sc)) ++
            (if Option.equal String.equal (Some sc) scope
             then spc() ++ str "(default interpretation)" else mt ()) ++
            pr_non_empty (spc()) (pr_notation_status on_parsing on_printing) ++
            spc() ++ surround (str "defined in " ++  (match loc with
                Some loc -> Loc.pr_use_dp loc
              | None -> DirPath.print full_path)) ++
            List.fold_right (fun rloc x -> x ++ spc() ++ surround (str "reserved in " ++ Loc.pr_use_dp rloc)) (get_ntn_gram_locs ntn loc) (Pp.mt ())
          ))
        l) ntns

let collect_notation_in_scope scope sc known =
  assert (not (String.equal scope default_scope));
  NotationMap.fold
    (fun ntn d (l,known as acc) ->
      if List.mem_f notation_eq ntn known then acc else (extract_notation_data d @ l,ntn::known))
    sc.notations ([],known)

let collect_notations stack =
  fst (List.fold_left
    (fun (all,knownntn as acc) -> function
      | OpenScopeItem scope ->
          if String.List.mem_assoc scope all then acc
          else
            let (l,knownntn) =
              collect_notation_in_scope scope (find_scope scope) knownntn in
            ((scope,l)::all,knownntn)
      | LonelyNotationItem ntn ->
          if List.mem_f notation_eq ntn knownntn then (all,knownntn)
          else
          try
            let datas = extract_notation_data
              (NotationMap.find ntn (find_scope default_scope).notations) in
            let all' = match all with
              | (s,lonelyntn)::rest when String.equal s default_scope ->
                  (s,datas@lonelyntn)::rest
              | _ ->
                  (default_scope,datas)::all in
            (all',ntn::knownntn)
          with Not_found -> (* e.g. if only printing *) (all,knownntn))
    ([],[]) stack)

let pr_visible_in_scope prglob (scope,ntns) =
  let strm =
    List.fold_right
      (fun d strm -> pr_notation_data prglob d ++ fnl () ++ strm)
      ntns (mt ()) in
  (if String.equal scope default_scope then
     str (String.plural (List.length ntns) "Lonely notation")
   else
     str "Visible in scope " ++ str scope)
  ++ fnl () ++ strm

let pr_scope_stack prglob stack =
  prlist_with_sep fnl (pr_visible_in_scope prglob) (collect_notations stack)

let pr_visibility prglob = function
  | Some scope -> pr_scope_stack prglob (push_scope scope !scope_stack)
  | None -> pr_scope_stack prglob !scope_stack

(* Enabling/disabling notations *)

let toggle_main_notation ~on ~use found test ntn_data main =
  let found d = found := (Inl (d.not_location, ntn_data), d.not_interp) :: !found in
  match main, use with
  | OnlyParsingData (is_on,d), OnlyPrinting when test d.not_interp ->
    user_err (strbrk "Unexpected only printing for an only parsing notation.")
  | OnlyParsingData (is_on,d) as x, (OnlyParsing | ParsingAndPrinting) when test d.not_interp ->
    if is_on <> on then begin found d; OnlyParsingData (on, d) end else x
  | ParsingAndPrintingData (is_parsing_on,is_printing_on,d) as x, _ when test d.not_interp ->
     let parsing_changed = match use with
       | OnlyPrinting -> false
       | OnlyParsing | ParsingAndPrinting -> is_parsing_on <> on in
     let printing_changed = match use with
       | OnlyParsing -> false
       | OnlyPrinting | ParsingAndPrinting -> is_printing_on <> on in
     if parsing_changed || printing_changed then
       let () = found d in
       ParsingAndPrintingData (is_parsing_on <> parsing_changed,is_printing_on <> printing_changed,d)
     else
       x
  | (NoParsingData | OnlyParsingData _ | ParsingAndPrintingData _), _ -> main

let toggle_extra_only_printing_notation ~on ~use found test ntn_data (is_on,d as x) =
  let found d = found := (Inl (d.not_location, ntn_data), d.not_interp) :: !found in
  match use with
  | OnlyParsing ->
    user_err (strbrk "Unexpected only parsing for an only printing notation.")
  | OnlyPrinting | ParsingAndPrinting ->
    if test d.not_interp then
      if is_on <> on then let () = found d in (on,d) else x
    else
      x

let toggle_notation_data ~on ~use found test ntn_data (main,extra as data) =
  let main' = toggle_main_notation ~on ~use found test ntn_data main in
  let extra' = List.Smart.map (toggle_extra_only_printing_notation ~on ~use found test ntn_data) extra in
  if main' == main && extra' == extra then data else (main',extra')

type 'a notation_query_pattern_gen = {
    notation_entry_pattern : notation_entry list;
    interp_rule_key_pattern : (notation_key, 'a) Util.union option;
    use_pattern : notation_use;
    scope_pattern : notation_with_optional_scope option;
    interpretation_pattern : interpretation option;
  }

type notation_query_pattern = qualid notation_query_pattern_gen

let match_notation_interpretation notation_interpretation pat =
  match notation_interpretation with
  | None -> true
  | Some pat' -> Notation_ops.finer_interpretation_than pat pat'

let match_notation_entry notation_entry_pattern notation_entry =
  List.is_empty notation_entry_pattern ||
  List.mem_f notation_entry_eq notation_entry notation_entry_pattern

let match_notation_rule interp_rule_key_pattern notation_key =
  match interp_rule_key_pattern with
  | None -> true
  | Some (Inl ntn) -> match_notation_key false ntn notation_key
  | Some (Inr _) -> false

let toggle_notations_by_interpretation ~on found ntn_pattern ntn_data (main,extra as data) =
  let use = ntn_pattern.use_pattern in
  let test = match_notation_interpretation ntn_pattern.interpretation_pattern in
  toggle_notation_data ~on ~use found test ntn_data data

let toggle_notations_in_scope ~on found inscope ntn_pattern ntns =
  match ntn_pattern.notation_entry_pattern, ntn_pattern.interp_rule_key_pattern with
  | _, Some (Inr kn) -> ntns (* This is the table of notations, not of abbreviations *)
  | _ :: _ as ntn_entries, Some (Inl ntn) ->
    (* shortcut *)
    List.fold_right (fun ntn_entry ntns ->
      try
        NotationMap.add (ntn_entry, ntn)
          (toggle_notations_by_interpretation ~on found ntn_pattern
             (inscope,(ntn_entry,ntn))
             (NotationMap.find (ntn_entry, ntn) ntns))
          ntns
      with Not_found -> ntns)
        ntn_entries ntns
    (* Deal with full notations *)
  | ntn_entries, ntn_rule -> (* This is the table of notations, not of abbreviations *)
    NotationMap.mapi (fun (ntn_entry,ntn_key' as ntn') data ->
        if match_notation_entry ntn_entries ntn_entry && match_notation_rule ntn_rule ntn_key' then
          toggle_notations_by_interpretation ~on found ntn_pattern
            (inscope,ntn')
            data
        else
          data) ntns

let warn_abbreviation_not_bound_to_entry =
  CWarnings.create ~name:"conflicting-abbreviation-entry" ~category:CWarnings.CoreCategories.syntax
                   (fun () ->
                    strbrk "Activation of abbreviations does not expect mentioning a grammar entry.")

let warn_abbreviation_not_bound_to_scope =
  CWarnings.create ~name:"conflicting-abbreviation-scope" ~category:CWarnings.CoreCategories.syntax
                   (fun () ->
                    strbrk "Activation of abbreviations does not expect mentioning a scope.")

let toggle_abbreviations ~on found ntn_pattern =
  try
    let qid =
      match ntn_pattern.interp_rule_key_pattern, ntn_pattern.notation_entry_pattern, ntn_pattern.scope_pattern with
      | Some (Inr qid), [], None -> Some qid
      | Some (Inr qid), entries, inscope ->
        if not (List.is_empty entries) then warn_abbreviation_not_bound_to_entry ();
        if Option.has_some inscope then warn_abbreviation_not_bound_to_scope ();
        raise Exit
      | Some (Inl _), _, _ | None, _::_, _ | None, _, Some _ -> raise Exit (* Not about abbreviation, shortcut *)
      | None, [], None -> None
    in
    let test _ abbrev =
      let sp = Abbreviation.full_path abbrev in
      let a = Abbreviation.interp abbrev in
      let res = match_notation_interpretation ntn_pattern.interpretation_pattern a in
      let res' = match qid with
        | Some qid -> Libnames.is_qualid_suffix_of_full_path qid sp
        | None -> true in
      let res'' = res && res' in
      if res'' then found := (Inr sp, a) :: !found; res'' in
    Abbreviation.toggle_if ~on ~use:ntn_pattern.use_pattern test
  with Exit -> ()

let warn_nothing_to_enable_or_disable =
  CWarnings.create ~name:"no-notation-to-enable-or-disable"
    ~category:CWarnings.CoreCategories.syntax
    (fun () -> strbrk "Found no matching notation to enable or disable.")

let toggle_notations ~on ~all ?(verbose=true) prglob ntn_pattern =
  let found = ref [] in
  (* Deal with (parsing) notations *)
  begin
    match ntn_pattern.scope_pattern with
    | None ->
      scope_map := String.Map.mapi (fun sc {notations;delimiters} ->
                      let inscope = if String.equal sc default_scope then LastLonelyNotation else NotationInScope sc in
                      {notations = toggle_notations_in_scope ~on found inscope ntn_pattern notations;delimiters}) !scope_map;
    | Some inscope ->
      (* shortcut when a scope is given *)
      let sc = match inscope with NotationInScope sc -> sc | LastLonelyNotation -> default_scope in
      scope_map := String.Map.add sc (let {notations;delimiters} = find_scope sc in {notations = toggle_notations_in_scope ~on found inscope ntn_pattern notations;delimiters}) !scope_map
  end;
  (* Deal with abbreviations *)
  toggle_abbreviations ~on found ntn_pattern;
  match !found with
  | [] -> warn_nothing_to_enable_or_disable ()
  | _::_::_ when not all ->
    user_err (strbrk "More than one interpretation bound to this notation, confirm with the \"all\" modifier.")
  | _ ->
     if verbose then Feedback.msg_info
       (str "The following notations have been " ++
          str (if on then "enabled" else "disabled") ++
          (match ntn_pattern.use_pattern with
           | OnlyParsing -> str " for parsing"
           | OnlyPrinting -> str " for printing"
           | ParsingAndPrinting -> mt ()) ++
          str ":" ++ fnl () ++
          prlist_with_sep fnl (fun (kind, (vars,a as i)) ->
            match kind with
            | Inl (l, (sc, (entry, _))) ->
              let sc = match sc with NotationInScope sc -> sc | LastLonelyNotation -> default_scope in
              let data = { not_interp = i; not_location = l; not_user_warns = None } in
              hov 0
                (str "Notation " ++ pr_notation_data prglob (Some true,Some true,data) ++
                 (match entry with
                  | InCustomEntry s ->
                    str " (in custom " ++ Nametab.CustomEntries.pr s ++ str ")"
                  | InConstrEntry -> mt ()) ++
                 (if String.equal sc default_scope then mt () else (brk (1,2) ++ str ": " ++ str sc)))
            | Inr sp ->
              hov 0 (str "Notation " ++ Libnames.pr_path sp ++ prlist (fun (a,_) -> spc () ++ Id.print a) vars ++
              spc () ++ str ":=" ++ spc () ++ prglob (Notation_ops.glob_constr_of_notation_constr a)))
            !found)

(**********************************************************************)
(* Synchronisation with reset *)

let freeze () =
 (!scope_map, !scope_stack, !arguments_scope,
  !delimiters_map, !scope_class_map,
  !prim_token_interp_infos, !prim_token_uninterp_infos,
  !entry_coercion_map, !entry_has_global_map,
  !entry_has_ident_map)

let unfreeze (scm,scs,asc,dlm,clsc,ptii,ptui,coe,globs,ids) =
  scope_map := scm;
  scope_stack := scs;
  delimiters_map := dlm;
  arguments_scope := asc;
  scope_class_map := clsc;
  prim_token_interp_infos := ptii;
  prim_token_uninterp_infos := ptui;
  entry_coercion_map := coe;
  entry_has_global_map := globs;
  entry_has_ident_map := ids

let init () =
  init_scope_map ();
  delimiters_map := String.Map.empty;
  scope_class_map := initial_scope_class_map;
  prim_token_interp_infos := String.Map.empty;
  prim_token_uninterp_infos := GlobRefMap.empty

let _ =
  Summary.declare_summary "symbols"
    { stage = Summary.Stage.Interp;
      Summary.freeze_function = freeze;
      Summary.unfreeze_function = unfreeze;
      Summary.init_function = init }

let with_notation_protection f x =
  let open Memprof_coq.Resource_bind in
  let& () = Util.protect_state ~freeze ~unfreeze in
  with_notation_uninterpretation_protection f x
