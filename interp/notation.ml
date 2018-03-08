(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
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
open Constr
open Libnames
open Globnames
open Constrexpr
open Notation_term
open Glob_term
open Glob_ops
open Ppextend
open Context.Named.Declaration

(*i*)

(*s A scope is a set of notations; it includes

  - a set of ML interpreters/parsers for positive (e.g. 0, 1, 15, ...) and
    negative numbers (e.g. -0, -2, -13, ...). These interpreters may
    fail if a number has no interpretation in the scope (e.g. there is
    no interpretation for negative numbers in [nat]); interpreters both for
    terms and patterns can be set; these interpreters are in permanent table
    [numeral_interpreter_tab]
  - a set of ML printers for expressions denoting numbers parsable in
    this scope
  - a set of interpretations for infix (more generally distfix) notations
  - an optional pair of delimiters which, when occurring in a syntactic
    expression, set this scope to be the current scope
*)

(**********************************************************************)
(* Scope of symbols *)

type delimiters = string
type notation_location = (DirPath.t * DirPath.t) * string

type notation_data = {
  not_interp : interpretation;
  not_location : notation_location;
  not_onlyprinting : bool;
}

module NotationOrd =
  struct
    type t = notation
    let compare = Pervasives.compare
  end

module NotationMap = CMap.Make(NotationOrd)
module NotationSet = Set.Make(NotationOrd)

type scope = {
  notations: notation_data NotationMap.t;
  delimiters: delimiters option
}

(* Uninterpreted notation map: notation -> level * DirPath.t *)
let notation_level_map = ref NotationMap.empty

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
(* Equality *)

open Extend

let notation_entry_eq s1 s2 = match (s1,s2) with
| InConstrEntry, InConstrEntry -> true
| InCustomEntry s1, InCustomEntry s2 -> String.equal s1 s2
| (InConstrEntry | InCustomEntry _), _ -> false

let notation_eq (from1,ntn1) (from2,ntn2) =
  notation_entry_eq from1 from2 && String.equal ntn1 ntn2

let parenRelation_eq t1 t2 = match t1, t2 with
| L, L | E, E | Any, Any -> true
| Prec l1, Prec l2 -> Int.equal l1 l2
| _ -> false

let production_position_eq pp1 pp2 = match (pp1,pp2) with
| BorderProd (side1,assoc1), BorderProd (side2,assoc2) -> side1 = side2 && assoc1 = assoc2
| InternalProd, InternalProd -> true
| (BorderProd _ | InternalProd), _ -> false

let production_level_eq l1 l2 = match (l1,l2) with
| NextLevel, NextLevel -> true
| NumLevel n1, NumLevel n2 -> Int.equal n1 n2
| (NextLevel | NumLevel _), _ -> false

let constr_entry_key_eq eq v1 v2 = match v1, v2 with
| ETName, ETName -> true
| ETReference, ETReference -> true
| ETBigint, ETBigint -> true
| ETBinder b1, ETBinder b2 -> b1 == b2
| ETConstr (s1,bko1,lev1), ETConstr (s2,bko2,lev2) ->
   notation_entry_eq s1 s2 && eq lev1 lev2 && Option.equal (=) bko1 bko2
| ETPattern (b1,n1), ETPattern (b2,n2) -> b1 = b2 && Option.equal Int.equal n1 n2
| (ETName | ETReference | ETBigint | ETBinder _ | ETConstr _ | ETPattern _), _ -> false

let level_eq_gen strict (s1, l1, t1, u1) (s2, l2, t2, u2) =
  let tolerability_eq (i1, r1) (i2, r2) = Int.equal i1 i2 && parenRelation_eq r1 r2 in
  let prod_eq (l1,pp1) (l2,pp2) =
    if strict then production_level_eq l1 l2 && production_position_eq pp1 pp2
    else production_level_eq l1 l2 in
  notation_entry_eq s1 s2 && Int.equal l1 l2 && List.equal tolerability_eq t1 t2
  && List.equal (constr_entry_key_eq prod_eq) u1 u2

let level_eq = level_eq_gen false

(**********************************************************************)
(* Operations on scopes *)

let declare_scope scope =
  try let _ = String.Map.find scope !scope_map in ()
  with Not_found ->
(*    Flags.if_warn message ("Creating scope "^scope);*)
    scope_map := String.Map.add scope empty_scope !scope_map

let error_unknown_scope sc =
  user_err ~hdr:"Notation"
    (str "Scope " ++ str sc ++ str " is not declared.")

let find_scope scope =
  try String.Map.find scope !scope_map
  with Not_found -> error_unknown_scope scope

let check_scope sc = let _ = find_scope sc in ()

(* [sc] might be here a [scope_name] or a [delimiter]
   (now allowed after Open Scope) *)

let normalize_scope sc =
  try let _ = String.Map.find sc !scope_map in sc
  with Not_found ->
    try
      let sc = String.Map.find sc !delimiters_map in
      let _ = String.Map.find sc !scope_map in sc
    with Not_found -> error_unknown_scope sc

(**********************************************************************)
(* The global stack of scopes                                         *)

type scope_elem = Scope of scope_name | SingleNotation of notation
type scopes = scope_elem list

let scope_eq s1 s2 = match s1, s2 with
| Scope s1, Scope s2 -> String.equal s1 s2
| SingleNotation s1, SingleNotation s2 -> notation_eq s1 s2
| Scope _, SingleNotation _
| SingleNotation _, Scope _ -> false

(* Scopes for interpretation *)

let scope_stack = ref []

let current_scopes () = !scope_stack

let scope_is_open_in_scopes sc l =
  List.exists (function Scope sc' -> String.equal sc sc' | _ -> false) l

let scope_is_open sc = scope_is_open_in_scopes sc (!scope_stack)

(* Uninterpretation tables *)

type interp_rule =
  | NotationRule of scope_name option * notation
  | SynDefRule of KerName.t

type notation_rule_core = interp_rule * interpretation * int option
type notation_rule = notation_rule_core * delimiters option

(* Scopes for uninterpretation: includes abbreviations (i.e. syntactic definitions) and  *)

type uninterp_scope_elem =
  | UninterpScope of scope_name
  | UninterpSingle of notation_rule_core

let uninterp_scope_eq_weak s1 s2 = match s1, s2 with
| UninterpScope s1, UninterpScope s2 -> String.equal s1 s2
| UninterpSingle s1, UninterpSingle s2 -> false
| (UninterpSingle _ | UninterpScope _), _ -> false

module ScopeOrd =
  struct
    type t = scope_name option
    let compare = Pervasives.compare
  end

module ScopeMap = CMap.Make(ScopeOrd)

let uninterp_scope_stack = ref []

let push_uninterp_scope sc scopes = UninterpScope sc :: scopes

let push_uninterp_scopes = List.fold_right push_uninterp_scope

let make_current_uninterp_scopes (tmp_scope,scopes) =
  Option.fold_right push_uninterp_scope tmp_scope
    (push_uninterp_scopes scopes !uninterp_scope_stack)

(* TODO: push nat_scope, z_scope, ... in scopes summary *)

(* Exportation of scopes *)
let open_scope i (_,(local,op,sc)) =
  if Int.equal i 1 then begin
    scope_stack :=
      if op then Scope sc :: !scope_stack
      else List.except scope_eq (Scope sc) !scope_stack;
    uninterp_scope_stack :=
      if op then UninterpScope sc :: !uninterp_scope_stack
      else List.except uninterp_scope_eq_weak (UninterpScope sc) !uninterp_scope_stack
    end

let cache_scope o =
  open_scope 1 o

let subst_scope (subst,sc) = sc

open Libobject

let discharge_scope (_,(local,_,_ as o)) =
  if local then None else Some o

let classify_scope (local,_,_ as o) =
  if local then Dispose else Substitute o

let inScope : bool * bool * scope_name -> obj =
  declare_object {(default_object "SCOPE") with
      cache_function = cache_scope;
      open_function = open_scope;
      subst_function = subst_scope;
      discharge_function = discharge_scope;
      classify_function = classify_scope }

let open_close_scope (local,opening,sc) =
  Lib.add_anonymous_leaf (inScope (local,opening,normalize_scope sc))

let empty_scope_stack = []

let push_scope sc scopes = Scope sc :: scopes

let push_scopes = List.fold_right push_scope

let make_current_scopes (tmp_scope,scopes) =
  Option.fold_right push_scope tmp_scope (push_scopes scopes !scope_stack)

(**********************************************************************)
(* Delimiters *)

let declare_delimiters scope key =
  let sc = find_scope scope in
  let newsc = { sc with delimiters = Some key } in
  begin match sc.delimiters with
    | None -> scope_map := String.Map.add scope newsc !scope_map
    | Some oldkey when String.equal oldkey key -> ()
    | Some oldkey ->
        (** FIXME: implement multikey scopes? *)
	Flags.if_verbose Feedback.msg_info
	  (str "Overwriting previous delimiting key " ++ str oldkey ++ str " in scope " ++ str scope);
	scope_map := String.Map.add scope newsc !scope_map
  end;
  try
    let oldscope = String.Map.find key !delimiters_map in
    if String.equal oldscope scope then ()
    else begin
      Flags.if_verbose Feedback.msg_info (str "Hiding binding of key " ++ str key ++ str " to " ++ str oldscope);
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
       with Not_found ->
         assert false (* A delimiter for scope [scope] should exist *)

let find_delimiters_scope ?loc key =
  try String.Map.find key !delimiters_map
  with Not_found ->
    user_err ?loc ~hdr:"find_delimiters"
      (str "Unknown scope delimiting key " ++ str key ++ str ".")

(* We define keys for glob_constr and aconstr to split the syntax entries
   according to the key of the pattern (adapted from Chet Murthy by HH) *)

type key =
  | RefKey of global_reference
  | LambdaKey
  | ProdKey
  | Oth

let key_compare k1 k2 = match k1, k2 with
| RefKey gr1, RefKey gr2 -> RefOrdered.compare gr1 gr2
| RefKey _, _ -> -1
| _, RefKey _ -> 1
| k1, k2 -> Pervasives.compare k1 k2

module KeyOrd = struct type t = key let compare = key_compare end
module KeyMap = Map.Make(KeyOrd)

let keymap_add key sc interp map =
  let oldkeymap = try ScopeMap.find sc map with Not_found -> KeyMap.empty in
  let oldscmap = try KeyMap.find key oldkeymap with Not_found -> [] in
  let newscmap = KeyMap.add key (interp :: oldscmap) oldkeymap in
  ScopeMap.add sc newscmap map

let keymap_extract keys sc map =
  let keymap, map =
    try ScopeMap.find sc map, ScopeMap.remove sc map
    with Not_found -> KeyMap.empty, map in
  let add_scope rule = (rule,None) in
  List.map_append (fun key -> try List.map add_scope (KeyMap.find key keymap) with Not_found -> []) keys, map

let find_with_delimiters = function
  | None -> None
  | Some scope ->
      match (String.Map.find scope !scope_map).delimiters with
        | Some key -> Some (Some key)
        | None -> None

let keymap_extract_remainder keys map =
  ScopeMap.fold (fun sc keymap acc ->
      match find_with_delimiters sc with
      | None -> acc
      | Some delim ->
         let add_scope rule = (rule,delim) in
         let l = List.map_append (fun key -> try List.map add_scope (KeyMap.find key keymap) with Not_found -> []) keys in
      l @ acc) map []

(* Scopes table : interpretation -> scope_name *)
let notations_key_table = ref (ScopeMap.empty : notation_rule_core list KeyMap.t ScopeMap.t)

let prim_token_key_table = ref (KeyMap.empty : (string * (any_glob_constr -> prim_token option) * bool) KeyMap.t)

let glob_prim_constr_key c = match DAst.get c with
  | GRef (ref, _) -> RefKey (canonical_gr ref)
  | GApp (c, _) ->
    begin match DAst.get c with
    | GRef (ref, _) -> RefKey (canonical_gr ref)
    | _ -> Oth
    end
  | GLambda _ -> LambdaKey
  | GProd _ -> ProdKey
  | _ -> Oth

let glob_constr_keys c = match DAst.get c with
  | GRef (ref,_) -> [RefKey (canonical_gr ref)]
  | GApp (c, _) ->
    begin match DAst.get c with
    | GRef (ref, _) -> [RefKey (canonical_gr ref); Oth]
    | _ -> [Oth]
    end
  | GLambda _ -> [LambdaKey]
  | GProd _ -> [ProdKey]
  | _ -> [Oth]

let cases_pattern_key c = match DAst.get c with
  | PatCstr (ref,_,_) -> RefKey (canonical_gr (ConstructRef ref))
  | _ -> Oth

let notation_constr_key = function (* Rem: NApp(NRef ref,[]) stands for @ref *)
  | NApp (NRef ref,args) -> RefKey(canonical_gr ref), Some (List.length args)
  | NList (_,_,NApp (NRef ref,args),_,_)
  | NBinderList (_,_,NApp (NRef ref,args),_,_) ->
      RefKey (canonical_gr ref), Some (List.length args)
  | NRef ref -> RefKey(canonical_gr ref), None
  | NApp (_,args) -> Oth, Some (List.length args)
  | NLambda _ | NBinderList (_,_,NLambda _,_,_) | NList (_,_,NLambda _,_,_) -> LambdaKey, None
  | NProd _ | NBinderList (_,_,NProd _,_,_) | NList (_,_,NProd _,_,_) -> ProdKey, None
  | _ -> Oth, None

(**********************************************************************)
(* Interpreting numbers (not in summary because functional objects)   *)

type required_module = full_path * string list

type 'a prim_token_interpreter =
    ?loc:Loc.t -> 'a -> glob_constr

type cases_pattern_status = bool (* true = use prim token in patterns *)

type 'a prim_token_uninterpreter =
    glob_constr list * (any_glob_constr -> 'a option) * cases_pattern_status

type internal_prim_token_interpreter =
    ?loc:Loc.t -> prim_token -> required_module * (unit -> glob_constr)

let prim_token_interpreter_tab =
  (Hashtbl.create 7 : (scope_name, internal_prim_token_interpreter) Hashtbl.t)

let add_prim_token_interpreter sc interp =
  try
    let cont = Hashtbl.find prim_token_interpreter_tab sc in
    Hashtbl.replace prim_token_interpreter_tab sc (interp cont)
  with Not_found ->
    let cont = (fun ?loc _p -> raise Not_found) in
    Hashtbl.add prim_token_interpreter_tab sc (interp cont)

let declare_prim_token_interpreter sc interp (patl,uninterp,b) =
  declare_scope sc;
  add_prim_token_interpreter sc interp;
  List.iter (fun pat ->
      prim_token_key_table := KeyMap.add
        (glob_prim_constr_key pat) (sc,uninterp,b) !prim_token_key_table)
    patl

let mkNumeral n =
  if Bigint.is_pos_or_zero n then Numeral (Bigint.to_string n, true)
  else Numeral (Bigint.to_string (Bigint.neg n), false)

let ofNumeral n s =
  if s then Bigint.of_string n else Bigint.neg (Bigint.of_string n)

let mkString = function
| None -> None
| Some s -> if Unicode.is_utf8 s then Some (String s) else None

let delay dir int ?loc x = (dir, (fun () -> int ?loc x))

type rawnum = Constrexpr.raw_natural_number * Constrexpr.sign

let declare_rawnumeral_interpreter sc dir interp (patl,uninterp,inpat) =
  declare_prim_token_interpreter sc
    (fun cont ?loc -> function Numeral (n,s) -> delay dir interp ?loc (n,s)
                            | p -> cont ?loc p)
    (patl, (fun r -> match uninterp r with
                     | None -> None
                     | Some (n,s) -> Some (Numeral (n,s))), inpat)

let declare_numeral_interpreter sc dir interp (patl,uninterp,inpat) =
  let interp' ?loc (n,s) = interp ?loc (ofNumeral n s) in
  declare_prim_token_interpreter sc
    (fun cont ?loc -> function Numeral (n,s) -> delay dir interp' ?loc (n,s)
                            | p -> cont ?loc p)
    (patl, (fun r -> Option.map mkNumeral (uninterp r)), inpat)

let declare_string_interpreter sc dir interp (patl,uninterp,inpat) =
  declare_prim_token_interpreter sc
    (fun cont ?loc -> function String s -> delay dir interp ?loc s | p -> cont ?loc p)
    (patl, (fun r -> mkString (uninterp r)), inpat)

let check_required_module ?loc sc (sp,d) =
  try let _ = Nametab.global_of_path sp in ()
  with Not_found ->
    user_err ?loc ~hdr:"prim_token_interpreter"
    (str "Cannot interpret in " ++ str sc ++ str " without requiring first module " ++ str (List.last d) ++ str ".")

(* Look if some notation or numeral printer in [scope] can be used in
   the scope stack [scopes], and if yes, using delimiters or not *)

let rec find_without_delimiters find (ntn_scope,ntn) = function
  | UninterpScope scope :: scopes ->
      (* Is the expected ntn/numpr attached to the most recently open scope? *)
      begin match ntn_scope with
      | Some scope' when String.equal scope scope' ->
        Some None
      | _ ->
	(* If the most recently open scope has a notation/numeral printer
    	   but not the expected one then we need delimiters *)
	if find scope then
	  find_with_delimiters ntn_scope
	else
	  find_without_delimiters find (ntn_scope,ntn) scopes
      end
  | UninterpSingle (NotationRule (_,ntn'),_,_) :: scopes ->
      begin match ntn_scope, ntn with
      | None, Some ntn when notation_eq ntn ntn' ->
        Some None
      | _ ->
	find_without_delimiters find (ntn_scope,ntn) scopes
      end
  | UninterpSingle (SynDefRule _,_,_) :: scopes -> find_without_delimiters find (ntn_scope,ntn) scopes
  | [] ->
      (* Can we switch to [scope]? Yes if it has defined delimiters *)
      find_with_delimiters ntn_scope

(* Uninterpreted notation levels *)

let pr_notation (from,ntn) = qstring ntn ++ match from with InConstrEntry -> mt () | InCustomEntry s -> str " in custom " ++ str s

let declare_notation_level ntn level =
  if NotationMap.mem ntn !notation_level_map then
    anomaly (str "Notation " ++ pr_notation ntn ++ str " is already assigned a level.");
  notation_level_map := NotationMap.add ntn level !notation_level_map

let level_of_notation ntn =
  NotationMap.find ntn !notation_level_map

(* The mapping between notations and their interpretation *)

let warn_notation_overridden =
  CWarnings.create ~name:"notation-overridden" ~category:"parsing"
                   (fun (ntn,which_scope) ->
                    str "Notation" ++ spc () ++ pr_notation ntn ++ spc ()
                    ++ strbrk "was already used" ++ which_scope ++ str ".")

let declare_notation_interpretation ntn scopt pat df ~onlyprint =
  let scope = match scopt with Some s -> s | None -> default_scope in
  let sc = find_scope scope in
  let () =
    if NotationMap.mem ntn sc.notations then
    let which_scope = match scopt with
    | None -> mt ()
    | Some _ -> spc () ++ strbrk "in scope" ++ spc () ++ str scope in
    warn_notation_overridden (ntn,which_scope)
  in
  let notdata = {
    not_interp = pat;
    not_location = df;
    not_onlyprinting = onlyprint;
  } in
  let sc = { sc with notations = NotationMap.add ntn notdata sc.notations } in
  let () = scope_map := String.Map.add scope sc !scope_map in
  begin match scopt with
  | None -> scope_stack := SingleNotation ntn :: !scope_stack
  | Some _ -> ()
  end

let scope_of_rule = function
  | NotationRule (None,_) | SynDefRule _ -> None
  | NotationRule (Some sc as sco,_) -> sco

let uninterp_scope_to_add pat n = function
  | NotationRule (None,_) | SynDefRule _ as rule -> Some (UninterpSingle (rule,pat,n))
  | NotationRule (Some sc,_) -> None

let declare_uninterpretation rule (metas,c as pat) =
  let (key,n) = notation_constr_key c in
  let sc = scope_of_rule rule in
  notations_key_table := keymap_add key sc (rule,pat,n) !notations_key_table;
  uninterp_scope_stack := Option.List.cons (uninterp_scope_to_add pat n rule) !uninterp_scope_stack

let rec find_interpretation ntn find = function
  | [] -> raise Not_found
  | Scope scope :: scopes ->
      (try let (pat,df) = find scope in pat,(df,Some scope)
       with Not_found -> find_interpretation ntn find scopes)
  | SingleNotation ntn'::scopes when notation_eq ntn' ntn ->
      (try let (pat,df) = find default_scope in pat,(df,None)
       with Not_found ->
         (* e.g. because single notation only for constr, not cases_pattern *)
         find_interpretation ntn find scopes)
  | SingleNotation _::scopes ->
      find_interpretation ntn find scopes

let find_notation ntn sc =
  let n = NotationMap.find ntn (find_scope sc).notations in
  let () = if n.not_onlyprinting then raise Not_found in
  (n.not_interp, n.not_location)

let notation_of_prim_token = function
  | Numeral (n,true) -> InConstrEntry, n
  | Numeral (n,false) -> InConstrEntry, "- "^n
  | String _ -> raise Not_found

let find_prim_token check_allowed ?loc p sc =
  (* Try for a user-defined numerical notation *)
  try
    let (_,c),df = find_notation (notation_of_prim_token p) sc in
    let pat = Notation_ops.glob_constr_of_notation_constr ?loc c in
    check_allowed pat;
    pat, df
  with Not_found ->
  (* Try for a primitive numerical notation *)
  let (spdir,interp) = Hashtbl.find prim_token_interpreter_tab sc ?loc p in
  check_required_module ?loc sc spdir;
  let pat = interp () in
  check_allowed pat;
  pat, ((dirpath (fst spdir),DirPath.empty),"")

let interp_prim_token_gen ?loc g p local_scopes =
  let scopes = make_current_scopes local_scopes in
  let p_as_ntn = try notation_of_prim_token p with Not_found -> InConstrEntry,"" in
  try find_interpretation p_as_ntn (find_prim_token ?loc g p) scopes
  with Not_found ->
    user_err ?loc ~hdr:"interp_prim_token"
    ((match p with
      | Numeral _ ->
         str "No interpretation for numeral " ++ pr_notation (notation_of_prim_token p)
      | String s -> str "No interpretation for string " ++ qs s) ++ str ".")

let interp_prim_token ?loc =
  interp_prim_token_gen ?loc (fun _ -> ())

let rec check_allowed_ref_in_pat looked_for = DAst.(with_val (function
  | GVar _ | GHole _ -> ()
  | GRef (g,_) -> looked_for g
  | GApp (f, l) ->
    begin match DAst.get f with
    | GRef (g, _) ->
      looked_for g; List.iter (check_allowed_ref_in_pat looked_for) l
    | _ -> raise Not_found
    end
  | _ -> raise Not_found))

let interp_prim_token_cases_pattern_expr ?loc looked_for p =
  interp_prim_token_gen ?loc (check_allowed_ref_in_pat looked_for) p

let interp_notation ?loc ntn local_scopes =
  let scopes = make_current_scopes local_scopes in
  try find_interpretation ntn (find_notation ntn) scopes
  with Not_found ->
    user_err ?loc 
    (str "Unknown interpretation for notation " ++ pr_notation ntn ++ str ".")

let extract_notations scopes keys =
  if keys == [] then [] (* shortcut *) else
  let rec aux scopes map =
  match scopes with
  | UninterpScope sc :: scopes ->
      let l, map = keymap_extract keys (Some sc) map in l @ aux scopes map
  | UninterpSingle rule :: scopes -> (rule,None) :: aux scopes map
  | [] -> keymap_extract_remainder keys map
  in aux scopes !notations_key_table

let uninterp_notations scopes c =
  let scopes = make_current_uninterp_scopes scopes in
  extract_notations scopes (glob_constr_keys c)

let uninterp_cases_pattern_notations scopes c =
  let scopes = make_current_uninterp_scopes scopes in
  extract_notations scopes [cases_pattern_key c]

let uninterp_ind_pattern_notations scopes ind =
  let scopes = make_current_uninterp_scopes scopes in
  extract_notations scopes [RefKey (canonical_gr (IndRef ind))]

type entry_coercion = notation list

module EntryCoercionOrd =
struct
  type t = notation_entry * notation_entry
  let compare = Pervasives.compare
end

module EntryCoercionMap = Map.Make(EntryCoercionOrd)

let entry_coercion_map = ref EntryCoercionMap.empty

let availability_of_entry_coercion entry entry' =
  if notation_entry_eq entry entry' then Some [] else
  try Some (EntryCoercionMap.find (entry,entry') !entry_coercion_map)
  with Not_found -> None

let declare_entry_coercion (entry,_ as ntn) entry' =
  let toaddleft =
    EntryCoercionMap.fold
      (fun (entry'',entry''') path l ->
        if notation_entry_eq entry entry''' &&
           not (notation_entry_eq entry' entry'')
        then ((entry'',entry'),path@[ntn])::l else l)
      !entry_coercion_map [] in
  let toaddright =
    EntryCoercionMap.fold
      (fun (entry'',entry''') path l ->
        if notation_entry_eq entry' entry'' &&
           not (notation_entry_eq entry entry''')
        then ((entry,entry''),ntn::path)::l else l)
      !entry_coercion_map [] in
  entry_coercion_map :=
    List.fold_right (fun (pair,path) ->
        EntryCoercionMap.add pair path) (((entry,entry'),[ntn])::toaddright@toaddleft)
                   !entry_coercion_map

let uninterp_prim_token c =
  try
    let (sc,numpr,_) =
      KeyMap.find (glob_prim_constr_key c) !prim_token_key_table in
    match numpr (AnyGlobConstr c) with
      | None -> raise Notation_ops.No_match
      | Some n -> (sc,n)
  with Not_found -> raise Notation_ops.No_match

let uninterp_prim_token_ind_pattern ind args =
  let ref = IndRef ind in
  try
    let k = RefKey (canonical_gr ref) in
    let (sc,numpr,b) = KeyMap.find k !prim_token_key_table in
    if not b then raise Notation_ops.No_match;
    let args' = List.map
      (fun x -> snd (glob_constr_of_closed_cases_pattern x)) args in
    let ref = DAst.make @@ GRef (ref,None) in
    match numpr (AnyGlobConstr (DAst.make @@ GApp (ref,args'))) with
      | None -> raise Notation_ops.No_match
      | Some n -> (sc,n)
  with Not_found -> raise Notation_ops.No_match

let uninterp_prim_token_cases_pattern c =
  try
    let k = cases_pattern_key c in
    let (sc,numpr,b) = KeyMap.find k !prim_token_key_table in
    if not b then raise Notation_ops.No_match;
    let na,c = glob_constr_of_closed_cases_pattern c in
    match numpr (AnyGlobConstr c) with
      | None -> raise Notation_ops.No_match
      | Some n -> (na,sc,n)
  with Not_found -> raise Notation_ops.No_match

let availability_of_prim_token n printer_scope local_scopes =
  let f scope =
    try ignore ((Hashtbl.find prim_token_interpreter_tab scope) n); true
    with Not_found -> false in
  let scopes = make_current_uninterp_scopes local_scopes in
  find_without_delimiters f (Some printer_scope,None) scopes

(* Miscellaneous *)

let pair_eq f g (x1, y1) (x2, y2) = f x1 x2 && g y1 y2

let notation_binder_source_eq s1 s2 = match s1, s2 with
| NtnParsedAsIdent,  NtnParsedAsIdent -> true
| NtnParsedAsPattern b1, NtnParsedAsPattern b2 -> b1 = b2
| NtnBinderParsedAsConstr bk1, NtnBinderParsedAsConstr bk2 -> bk1 = bk2
| (NtnParsedAsIdent | NtnParsedAsPattern _ | NtnBinderParsedAsConstr _), _ -> false

let ntpe_eq t1 t2 = match t1, t2 with
| NtnTypeConstr, NtnTypeConstr -> true
| NtnTypeBinder s1, NtnTypeBinder s2 -> notation_binder_source_eq s1 s2
| NtnTypeConstrList, NtnTypeConstrList -> true
| NtnTypeBinderList, NtnTypeBinderList -> true
| (NtnTypeConstr | NtnTypeBinder _ | NtnTypeConstrList | NtnTypeBinderList), _ -> false

let var_attributes_eq (_, ((entry1, sc1), tp1)) (_, ((entry2, sc2), tp2)) =
  notation_entry_eq entry1 entry2 &&
  pair_eq (Option.equal String.equal) (List.equal String.equal) sc1 sc2 &&
  ntpe_eq tp1 tp2

let interpretation_eq (vars1, t1) (vars2, t2) =
  List.equal var_attributes_eq vars1 vars2 &&
  Notation_ops.eq_notation_constr (List.map fst vars1, List.map fst vars2) t1 t2

let exists_notation_in_scope scopt ntn onlyprint r =
  let scope = match scopt with Some s -> s | None -> default_scope in
  try
    let sc = String.Map.find scope !scope_map in
    let n = NotationMap.find ntn sc.notations in
    onlyprint = n.not_onlyprinting && 
    interpretation_eq n.not_interp r
  with Not_found -> false

let exists_notation_interpretation_in_scope scopt ntn =
  let scope = match scopt with Some s -> s | None -> default_scope in
  try
    let sc = String.Map.find scope !scope_map in
    let _ = NotationMap.find ntn sc.notations in
    true
  with Not_found -> false

let isNVar_or_NHole = function NVar _ | NHole _ -> true | _ -> false

(**********************************************************************)
(* Mapping classes to scopes *)

open Classops

type scope_class = cl_typ

let scope_class_compare : scope_class -> scope_class -> int =
  cl_typ_ord

let compute_scope_class sigma t =
  let (cl,_,_) = find_class_type sigma t in
  cl

module ScopeClassOrd =
struct
  type t = scope_class
  let compare = scope_class_compare
end

module ScopeClassMap = Map.Make(ScopeClassOrd)

let initial_scope_class_map : scope_name ScopeClassMap.t =
  ScopeClassMap.empty

let scope_class_map = ref initial_scope_class_map

let declare_scope_class sc cl =
  scope_class_map := ScopeClassMap.add cl sc !scope_class_map

let find_scope_class cl =
  ScopeClassMap.find cl !scope_class_map

let find_scope_class_opt = function
  | None -> None
  | Some cl -> try Some (find_scope_class cl) with Not_found -> None

(**********************************************************************)
(* Special scopes associated to arguments of a global reference *)

let rec compute_arguments_classes sigma t =
  match EConstr.kind sigma (Reductionops.whd_betaiotazeta sigma t) with
    | Prod (_,t,u) ->
        let cl = try Some (compute_scope_class sigma t) with Not_found -> None in
        cl :: compute_arguments_classes sigma u
    | _ -> []

let compute_arguments_scope_full sigma t =
  let cls = compute_arguments_classes sigma t in
  let scs = List.map find_scope_class_opt cls in
  scs, cls

let compute_arguments_scope sigma t = fst (compute_arguments_scope_full sigma t)

let compute_type_scope sigma t =
  find_scope_class_opt (try Some (compute_scope_class sigma t) with Not_found -> None)

let current_type_scope_name () =
   find_scope_class_opt (Some CL_SORT)

let scope_class_of_class (x : cl_typ) : scope_class =
  x

(** Updating a scope list, thanks to a list of argument classes
    and the current Bind Scope base. When some current scope
    have been manually given, the corresponding argument class
    is emptied below, so this manual scope will be preserved. *)

let update_scope cl sco =
  match find_scope_class_opt cl with
  | None -> sco
  | sco' -> sco'

let rec update_scopes cls scl = match cls, scl with
  | [], _ -> scl
  | _, [] -> List.map find_scope_class_opt cls
  | cl :: cls, sco :: scl -> update_scope cl sco :: update_scopes cls scl

let arguments_scope = ref Refmap.empty

type arguments_scope_discharge_request =
  | ArgsScopeAuto
  | ArgsScopeManual
  | ArgsScopeNoDischarge

let load_arguments_scope _ (_,(_,r,n,scl,cls)) =
  List.iter (Option.iter check_scope) scl;
  let initial_stamp = ScopeClassMap.empty in
  arguments_scope := Refmap.add r (scl,cls,initial_stamp) !arguments_scope

let cache_arguments_scope o =
  load_arguments_scope 1 o

let subst_scope_class subst cs =
  try Some (subst_cl_typ subst cs) with Not_found -> None

let subst_arguments_scope (subst,(req,r,n,scl,cls)) =
  let r' = fst (subst_global subst r) in
  let subst_cl ocl = match ocl with
    | None -> ocl
    | Some cl ->
        match subst_scope_class subst cl with
        | Some cl'  as ocl' when cl' != cl -> ocl'
        | _ -> ocl in
  let cls' = List.smartmap subst_cl cls in
  (ArgsScopeNoDischarge,r',n,scl,cls')

let discharge_arguments_scope (_,(req,r,n,l,_)) =
  if req == ArgsScopeNoDischarge || (isVarRef r && Lib.is_in_section r) then None
  else
    let n =
      try
        let vars = Lib.variable_section_segment_of_reference r in
        vars |> List.map fst |> List.filter is_local_assum |> List.length
      with
        Not_found (* Not a ref defined in this section *) -> 0 in
    Some (req,Lib.discharge_global r,n,l,[])

let classify_arguments_scope (req,_,_,_,_ as obj) =
  if req == ArgsScopeNoDischarge then Dispose else Substitute obj

let rebuild_arguments_scope sigma (req,r,n,l,_) =
  match req with
    | ArgsScopeNoDischarge -> assert false
    | ArgsScopeAuto ->
      let env = Global.env () in (*FIXME?*)
      let typ = EConstr.of_constr @@ fst (Global.type_of_global_in_context env r) in
      let scs,cls = compute_arguments_scope_full sigma typ in
      (req,r,List.length scs,scs,cls)
    | ArgsScopeManual ->
      (* Add to the manually given scopes the one found automatically
         for the extra parameters of the section. Discard the classes
         of the manually given scopes to avoid further re-computations. *)
      let env = Global.env () in (*FIXME?*)
      let typ = EConstr.of_constr @@ fst (Global.type_of_global_in_context env r) in
      let l',cls = compute_arguments_scope_full sigma typ in
      let l1 = List.firstn n l' in
      let cls1 = List.firstn n cls in
      (req,r,0,l1@l,cls1)

type arguments_scope_obj =
    arguments_scope_discharge_request * global_reference *
    (* Used to communicate information from discharge to rebuild *)
    (* set to 0 otherwise *) int *
    scope_name option list * scope_class option list

let inArgumentsScope : arguments_scope_obj -> obj =
  declare_object {(default_object "ARGUMENTS-SCOPE") with
      cache_function = cache_arguments_scope;
      load_function = load_arguments_scope;
      subst_function = subst_arguments_scope;
      classify_function = classify_arguments_scope;
      discharge_function = discharge_arguments_scope;
      (* XXX: Should we pass the sigma here or not, see @herbelin's comment in 6511 *)
      rebuild_function = rebuild_arguments_scope Evd.empty }

let is_local local ref = local || isVarRef ref && Lib.is_in_section ref

let declare_arguments_scope_gen req r n (scl,cls) =
  Lib.add_anonymous_leaf (inArgumentsScope (req,r,n,scl,cls))

let declare_arguments_scope local r scl =
  let req = if is_local local r then ArgsScopeNoDischarge else ArgsScopeManual in
  (* We empty the list of argument classes to disable further scope
     re-computations and keep these manually given scopes. *)
  declare_arguments_scope_gen req r 0 (scl,[])

let find_arguments_scope r =
  try
    let (scl,cls,stamp) = Refmap.find r !arguments_scope in
    let cur_stamp = !scope_class_map in
    if stamp == cur_stamp then scl
    else
      (* Recent changes in the Bind Scope base, we re-compute the scopes *)
      let scl' = update_scopes cls scl in
      arguments_scope := Refmap.add r (scl',cls,cur_stamp) !arguments_scope;
      scl'
  with Not_found -> []

let declare_ref_arguments_scope sigma ref =
  let env = Global.env () in (* FIXME? *)
  let typ = EConstr.of_constr @@ fst @@ Global.type_of_global_in_context env ref in
  let (scs,cls as o) = compute_arguments_scope_full sigma typ in
  declare_arguments_scope_gen ArgsScopeAuto ref (List.length scs) o

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
  | Terminal s -> [s]
  | SProdList (_,l) ->
     let l = List.flatten (List.map string_of_symbol l) in "_"::l@".."::l@["_"]
  | Break _ -> []

let make_notation_key from symbols =
  (from,String.concat " " (List.flatten (List.map string_of_symbol symbols)))

let decompose_notation_key (from,s) =
  let len = String.length s in
  let rec decomp_ntn dirs n =
    if n>=len then List.rev dirs else
    let pos =
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
    from, decomp_ntn [] 0

(************)
(* Printing *)

let pr_delimiters_info = function
  | None -> str "No delimiting key"
  | Some key -> str "Delimiting key is " ++ str key

let classes_of_scope sc =
  ScopeClassMap.fold (fun cl sc' l -> if String.equal sc sc' then cl::l else l) !scope_class_map []

let pr_scope_class = pr_class

let pr_scope_classes sc =
  let l = classes_of_scope sc in
  match l with
  | [] -> mt ()
  | _ :: ll ->
    let opt_s = match ll with [] -> mt () | _ -> str "es" in
    hov 0 (str "Bound to class" ++ opt_s ++
      spc() ++ prlist_with_sep spc pr_scope_class l) ++ fnl()

let pr_notation_info prglob ntn c =
  str "\"" ++ str ntn ++ str "\" := " ++
  prglob (Notation_ops.glob_constr_of_notation_constr c)

let pr_named_scope prglob scope sc =
 (if String.equal scope default_scope then
   match NotationMap.cardinal sc.notations with
     | 0 -> str "No lonely notation"
     | n -> str "Lonely notation" ++ (if Int.equal n 1 then mt() else str"s")
  else
    str "Scope " ++ str scope ++ fnl () ++ pr_delimiters_info sc.delimiters)
  ++ fnl ()
  ++ pr_scope_classes scope
  ++ NotationMap.fold
       (fun ntn { not_interp  = (_, r); not_location = (_, df) } strm ->
	 pr_notation_info prglob df r ++ fnl () ++ strm)
       sc.notations (mt ())

let pr_scope prglob scope = pr_named_scope prglob scope (find_scope scope)

let pr_scopes prglob =
 String.Map.fold
   (fun scope sc strm -> pr_named_scope prglob scope sc ++ fnl () ++ strm)
   !scope_map (mt ())

let rec find_default ntn = function
  | [] -> None
  | Scope scope :: scopes ->
    if NotationMap.mem ntn (find_scope scope).notations then
      Some scope
    else find_default ntn scopes
  | SingleNotation ntn' :: scopes ->
    if notation_eq ntn ntn' then Some default_scope
    else find_default ntn scopes

let factorize_entries = function
  | [] -> []
  | (ntn,c)::l ->
      let (ntn,l_of_ntn,rest) =
	List.fold_left
          (fun (a',l,rest) (a,c) ->
            if notation_eq a a' then (a',c::l,rest) else (a,[c],(a',l)::rest))
	  (ntn,[c],[]) l in
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
      else
        loop beg (i+1)
    else
      push_token beg i []
  and loop_on_whitespace beg i =
    if i < String.length str then
      if str.[i] != ' ' then
        push_whitespace beg i (loop i (i+1))
      else
        loop_on_whitespace beg (i+1)
    else
      push_whitespace beg i []
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

let decompose_raw_notation ntn = raw_analyze_notation_tokens (split_notation_string ntn)

let possible_notations ntn =
  (* We collect the possible interpretations of a notation string depending on whether it is
    in "x 'U' y" or "_ U _" format *)
  let toks = split_notation_string ntn in
  if List.exists (function String "_" -> true | _ -> false) toks then
    (* Only "_ U _" format *)
    [ntn]
  else
    let _,ntn' = make_notation_key None (raw_analyze_notation_tokens toks) in
    if String.equal ntn ntn' then (* Only symbols *) [ntn] else [ntn;ntn']

let browse_notation strict ntn map =
  let ntns = possible_notations ntn in
  let find (from,ntn' as fullntn') ntn =
    if String.contains ntn ' ' then String.equal ntn ntn'
    else
      let _,toks = decompose_notation_key fullntn' in
      let get_terminals = function Terminal ntn -> Some ntn | _ -> None in
      let trms = List.map_filter get_terminals toks in
      if strict then String.List.equal [ntn] trms
      else String.List.mem ntn trms
  in
  let l =
    String.Map.fold
      (fun scope_name sc ->
        NotationMap.fold (fun ntn { not_interp  = (_, r); not_location = df } l ->
          if List.exists (find ntn) ntns then (ntn,(scope_name,r,df))::l else l) sc.notations)
      map [] in
  List.sort (fun x y -> String.compare (snd (fst x)) (snd (fst y))) l

let global_reference_of_notation test (ntn,(sc,c,_)) =
  match c with
  | NRef ref when test ref -> Some (ntn,sc,ref)
  | NApp (NRef ref, l) when List.for_all isNVar_or_NHole l && test ref ->
      Some (ntn,sc,ref)
  | _ -> None

let error_ambiguous_notation ?loc _ntn =
  user_err ?loc (str "Ambiguous notation.")

let error_notation_not_reference ?loc ntn =
  user_err ?loc 
   (str "Unable to interpret " ++ quote (str ntn) ++
    str " as a reference.")

let interp_notation_as_global_reference ?loc test ntn sc =
  let scopes = match sc with
  | Some sc ->
      let scope = find_scope (find_delimiters_scope sc) in
      String.Map.add sc scope String.Map.empty
  | None -> !scope_map in
  let ntns = browse_notation true ntn scopes in
  let refs = List.map (global_reference_of_notation test) ntns in
  match Option.List.flatten refs with
  | [_,_,ref] -> ref
  | [] -> error_notation_not_reference ?loc ntn
  | refs ->
      let f (ntn,sc,ref) =
        let def = find_default ntn !scope_stack in
        match def with
        | None -> false
        | Some sc' -> String.equal sc sc'
      in
      match List.filter f refs with
      | [_,_,ref] -> ref
      | [] -> error_notation_not_reference ?loc ntn
      | _ -> error_ambiguous_notation ?loc ntn

let locate_notation prglob ntn scope =
  let ntns = factorize_entries (browse_notation false ntn !scope_map) in
  let scopes = Option.fold_right push_scope scope !scope_stack in
  match ntns with
  | [] -> str "Unknown notation"
  | _ ->
    str "Notation" ++ fnl () ++
    prlist (fun (ntn,l) ->
      let scope = find_default ntn scopes in
      prlist
	(fun (sc,r,(_,df)) ->
	  hov 0 (
	    pr_notation_info prglob df r ++
	    (if String.equal sc default_scope then mt ()
             else (spc () ++ str ": " ++ str sc)) ++
	    (if Option.equal String.equal (Some sc) scope
             then spc () ++ str "(default interpretation)" else mt ())
	    ++ fnl ()))
	l) ntns

let collect_notation_in_scope scope sc known =
  assert (not (String.equal scope default_scope));
  NotationMap.fold
    (fun ntn { not_interp  = (_, r); not_location = (_, df) } (l,known as acc) ->
      if List.mem_f notation_eq ntn known then acc else ((df,r)::l,ntn::known))
    sc.notations ([],known)

let collect_notations stack =
  fst (List.fold_left
    (fun (all,knownntn as acc) -> function
      | Scope scope ->
	  if String.List.mem_assoc scope all then acc
	  else
	    let (l,knownntn) =
	      collect_notation_in_scope scope (find_scope scope) knownntn in
	    ((scope,l)::all,knownntn)
      | SingleNotation ntn ->
          if List.mem_f notation_eq ntn knownntn then (all,knownntn)
	  else
	    let { not_interp  = (_, r); not_location = (_, df) } =
              NotationMap.find ntn (find_scope default_scope).notations in
	    let all' = match all with
	      | (s,lonelyntn)::rest when String.equal s default_scope ->
		  (s,(df,r)::lonelyntn)::rest
	      | _ ->
		  (default_scope,[df,r])::all in
	    (all',ntn::knownntn))
    ([],[]) stack)

let pr_visible_in_scope prglob (scope,ntns) =
  let strm =
    List.fold_right
      (fun (df,r) strm -> pr_notation_info prglob df r ++ fnl () ++ strm)
      ntns (mt ()) in
  (if String.equal scope default_scope then
     str "Lonely notation" ++ (match ntns with [_] -> mt () | _ -> str "s")
   else
     str "Visible in scope " ++ str scope)
  ++ fnl () ++ strm

let pr_scope_stack prglob stack =
  List.fold_left
    (fun strm scntns -> strm ++ pr_visible_in_scope prglob scntns ++ fnl ())
    (mt ()) (collect_notations stack)

let pr_visibility prglob = function
  | Some scope -> pr_scope_stack prglob (push_scope scope !scope_stack)
  | None -> pr_scope_stack prglob !scope_stack

(**********************************************************************)
(* Mapping notations to concrete syntax *)

type unparsing_rule = unparsing list * precedence
type extra_unparsing_rules = (string * string) list
(* Concrete syntax for symbolic-extension table *)
let notation_rules =
  ref (NotationMap.empty : (unparsing_rule * extra_unparsing_rules * notation_grammar) NotationMap.t)

let declare_notation_rule ntn ~extra unpl gram =
  notation_rules := NotationMap.add ntn (unpl,extra,gram) !notation_rules

let find_notation_printing_rule ntn =
  try pi1 (NotationMap.find ntn !notation_rules)
  with Not_found -> anomaly (str "No printing rule found for " ++ pr_notation ntn ++ str ".")
let find_notation_extra_printing_rules ntn =
  try pi2 (NotationMap.find ntn !notation_rules)
  with Not_found -> []
let find_notation_parsing_rules ntn =
  try pi3 (NotationMap.find ntn !notation_rules)
  with Not_found -> anomaly (str "No parsing rule found for " ++ pr_notation ntn ++ str ".")

let get_defined_notations () =
  NotationSet.elements @@ NotationMap.domain !notation_rules

let add_notation_extra_printing_rule ntn k v =
  try
    notation_rules :=
      let p, pp, gr = NotationMap.find ntn !notation_rules in
      NotationMap.add ntn (p, (k,v) :: pp, gr) !notation_rules
  with Not_found ->
    user_err ~hdr:"add_notation_extra_printing_rule"
      (str "No such Notation.")

(**********************************************************************)
(* Synchronisation with reset *)

let freeze _ =
 (!scope_map, !notation_level_map, !scope_stack, !uninterp_scope_stack, !arguments_scope,
  !delimiters_map, !notations_key_table, !notation_rules,
  !scope_class_map)

let unfreeze (scm,nlm,scs,uscs,asc,dlm,fkm,pprules,clsc) =
  scope_map := scm;
  notation_level_map := nlm;
  scope_stack := scs;
  uninterp_scope_stack := uscs;
  delimiters_map := dlm;
  arguments_scope := asc;
  notations_key_table := fkm;
  notation_rules := pprules;
  scope_class_map := clsc

let init () =
  init_scope_map ();
  notation_level_map := NotationMap.empty;
  uninterp_scope_stack := [];
  delimiters_map := String.Map.empty;
  notations_key_table := ScopeMap.empty;
  notation_rules := NotationMap.empty;
  scope_class_map := initial_scope_class_map

let _ =
  Summary.declare_summary "symbols"
    { Summary.freeze_function = freeze;
      Summary.unfreeze_function = unfreeze;
      Summary.init_function = init }

let with_notation_protection f x =
  let fs = freeze false in
  try let a = f x in unfreeze fs; a
  with reraise ->
    let reraise = CErrors.push reraise in
    let () = unfreeze fs in
    iraise reraise
