(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
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
open Constr
open Libnames
open Globnames
open Constrexpr
open Notation_term
open Glob_term
open Glob_ops
open Context.Named.Declaration
open NumTok

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

let notation_entry_eq s1 s2 = match (s1,s2) with
| InConstrEntry, InConstrEntry -> true
| InCustomEntry s1, InCustomEntry s2 -> String.equal s1 s2
| (InConstrEntry | InCustomEntry _), _ -> false

let notation_entry_level_eq s1 s2 = match (s1,s2) with
| InConstrEntrySomeLevel, InConstrEntrySomeLevel -> true
| InCustomEntryLevel (s1,n1), InCustomEntryLevel (s2,n2) -> String.equal s1 s2 && n1 = n2
| (InConstrEntrySomeLevel | InCustomEntryLevel _), _ -> false

let notation_with_optional_scope_eq inscope1 inscope2 = match (inscope1,inscope2) with
 | LastLonelyNotation, LastLonelyNotation -> true
 | NotationInScope s1, NotationInScope s2 -> String.equal s1 s2
 | (LastLonelyNotation | NotationInScope _), _ -> false

let notation_eq (from1,ntn1) (from2,ntn2) =
  notation_entry_level_eq from1 from2 && String.equal ntn1 ntn2

let pr_notation (from,ntn) = qstring ntn ++ match from with InConstrEntrySomeLevel -> mt () | InCustomEntryLevel (s,n) -> str " in custom " ++ str s

module NotationOrd =
  struct
    type t = notation
    let compare = pervasives_compare
  end

module NotationSet = Set.Make(NotationOrd)
module NotationMap = CMap.Make(NotationOrd)

module SpecificNotationOrd =
  struct
    type t = specific_notation
    let compare = pervasives_compare
  end

module SpecificNotationSet = Set.Make(SpecificNotationOrd)
module SpecificNotationMap = CMap.Make(SpecificNotationOrd)

(**********************************************************************)
(* Scope of symbols *)

type delimiters = string
type notation_location = (DirPath.t * DirPath.t) * string

type notation_data = {
  not_interp : interpretation;
  not_location : notation_location;
  not_deprecation : Deprecation.t option;
}

type scope = {
  notations: notation_data NotationMap.t;
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

let warn_undeclared_scope =
  CWarnings.create ~name:"undeclared-scope" ~category:"deprecated"
                   (fun (scope) ->
                    strbrk "Declaring a scope implicitly is deprecated; use in advance an explicit "
                    ++ str "\"Declare Scope " ++ str scope ++ str ".\".")

let declare_scope scope =
  try let _ = String.Map.find scope !scope_map in ()
  with Not_found ->
    scope_map := String.Map.add scope empty_scope !scope_map

let error_unknown_scope ~info sc =
  user_err ~hdr:"Notation" ~info
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

let scope_eq s1 s2 = match s1, s2 with
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

(* Exportation of scopes *)
let open_scope i (_,(local,op,sc)) =
  if Int.equal i 1 then
    scope_stack :=
      if op then sc :: !scope_stack
      else List.except scope_eq sc !scope_stack

let cache_scope o =
  open_scope 1 o

let subst_scope (subst,sc) = sc

open Libobject

let discharge_scope (_,(local,_,_ as o)) =
  if local then None else Some o

let classify_scope (local,_,_ as o) =
  if local then Dispose else Substitute o

let inScope : bool * bool * scope_item -> obj =
  declare_object {(default_object "SCOPE") with
      cache_function = cache_scope;
      open_function = simple_open open_scope;
      subst_function = subst_scope;
      discharge_function = discharge_scope;
      classify_function = classify_scope }

let open_close_scope (local,opening,sc) =
  Lib.add_anonymous_leaf (inScope (local,opening,OpenScopeItem (normalize_scope sc)))

let empty_scope_stack = []

let push_scope sc scopes = OpenScopeItem sc :: scopes

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
        (* FIXME: implement multikey scopes? *)
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
       with Not_found as exn ->
         let _, info = Exninfo.capture exn in
         (* XXX info *)
         CErrors.anomaly ~info (str "A delimiter for scope [scope] should exist")

let find_delimiters_scope ?loc key =
  try String.Map.find key !delimiters_map
  with Not_found ->
    user_err ?loc ~hdr:"find_delimiters"
      (str "Unknown scope delimiting key " ++ str key ++ str ".")

(* Uninterpretation tables *)

type interp_rule =
  | NotationRule of specific_notation
  | SynDefRule of KerName.t

(* We define keys for glob_constr and aconstr to split the syntax entries
   according to the key of the pattern (adapted from Chet Murthy by HH) *)

type key =
  | RefKey of GlobRef.t
  | Oth

let key_compare k1 k2 = match k1, k2 with
| RefKey gr1, RefKey gr2 -> GlobRef.Ordered.compare gr1 gr2
| RefKey _, Oth -> -1
| Oth, RefKey _ -> 1
| Oth, Oth -> 0

module KeyOrd = struct type t = key let compare = key_compare end
module KeyMap = Map.Make(KeyOrd)

type notation_rule = interp_rule * interpretation * int option

let keymap_add key interp map =
  let old = try KeyMap.find key map with Not_found -> [] in
  KeyMap.add key (interp :: old) map

let keymap_find key map =
  try KeyMap.find key map
  with Not_found -> []

(* Scopes table : interpretation -> scope_name *)
let notations_key_table = ref (KeyMap.empty : notation_rule list KeyMap.t)

let glob_prim_constr_key c = match DAst.get c with
  | GRef (ref, _) -> Some (canonical_gr ref)
  | GApp (c, _) ->
    begin match DAst.get c with
    | GRef (ref, _) -> Some (canonical_gr ref)
    | _ -> None
    end
  | _ -> None

let glob_constr_keys c = match DAst.get c with
  | GApp (c, _) ->
    begin match DAst.get c with
    | GRef (ref, _) -> [RefKey (canonical_gr ref); Oth]
    | _ -> [Oth]
    end
  | GRef (ref,_) -> [RefKey (canonical_gr ref)]
  | _ -> [Oth]

let cases_pattern_key c = match DAst.get c with
  | PatCstr (ref,_,_) -> RefKey (canonical_gr (GlobRef.ConstructRef ref))
  | _ -> Oth

let notation_constr_key = function (* Rem: NApp(NRef ref,[]) stands for @ref *)
  | NApp (NRef ref,args) -> RefKey(canonical_gr ref), Some (List.length args)
  | NList (_,_,NApp (NRef ref,args),_,_)
  | NBinderList (_,_,NApp (NRef ref,args),_,_) ->
      RefKey (canonical_gr ref), Some (List.length args)
  | NRef ref -> RefKey(canonical_gr ref), None
  | NApp (_,args) -> Oth, Some (List.length args)
  | _ -> Oth, None

(**********************************************************************)
(* Interpreting numbers (not in summary because functional objects)   *)

type required_module = full_path * string list
type rawnum = NumTok.Signed.t

type prim_token_uid = string

type 'a prim_token_interpreter = ?loc:Loc.t -> 'a -> glob_constr
type 'a prim_token_uninterpreter = any_glob_constr -> 'a option

type 'a prim_token_interpretation =
  'a prim_token_interpreter * 'a prim_token_uninterpreter

module InnerPrimToken = struct

  type interpreter =
    | RawNumInterp of (?loc:Loc.t -> rawnum -> glob_constr)
    | BigNumInterp of (?loc:Loc.t -> Bigint.bigint -> glob_constr)
    | StringInterp of (?loc:Loc.t -> string -> glob_constr)

  let interp_eq f f' = match f,f' with
    | RawNumInterp f, RawNumInterp f' -> f == f'
    | BigNumInterp f, BigNumInterp f' -> f == f'
    | StringInterp f, StringInterp f' -> f == f'
    | _ -> false

  let do_interp ?loc interp primtok =
    match primtok, interp with
    | Numeral n, RawNumInterp interp -> interp ?loc n
    | Numeral n, BigNumInterp interp ->
      (match NumTok.Signed.to_bigint n with
       | Some n -> interp ?loc n
       | None -> raise Not_found)
    | String s, StringInterp interp -> interp ?loc s
    | (Numeral _ | String _),
      (RawNumInterp _ | BigNumInterp _ | StringInterp _) -> raise Not_found

  type uninterpreter =
    | RawNumUninterp of (any_glob_constr -> rawnum option)
    | BigNumUninterp of (any_glob_constr -> Bigint.bigint option)
    | StringUninterp of (any_glob_constr -> string option)

  let uninterp_eq f f' = match f,f' with
    | RawNumUninterp f, RawNumUninterp f' -> f == f'
    | BigNumUninterp f, BigNumUninterp f' -> f == f'
    | StringUninterp f, StringUninterp f' -> f == f'
    | _ -> false

  let mkNumeral n =
    Numeral (NumTok.Signed.of_bigint CDec n)

  let mkString = function
    | None -> None
    | Some s -> if Unicode.is_utf8 s then Some (String s) else None

  let do_uninterp uninterp g = match uninterp with
    | RawNumUninterp u -> Option.map (fun (s,n) -> Numeral (s,n)) (u g)
    | BigNumUninterp u -> Option.map mkNumeral (u g)
    | StringUninterp u -> mkString (u g)

end

(* The following two tables of (un)interpreters will *not* be
   synchronized.  But their indexes will be checked to be unique.
   These tables contain primitive token interpreters which are
   registered in plugins, such as string and ascii syntax.  It is
   essential that only plugins add to these tables, and that
   vernacular commands do not.  See
   https://github.com/coq/coq/issues/8401 for details of what goes
   wrong when vernacular commands add to these tables. *)
let prim_token_interpreters =
  (Hashtbl.create 7 : (prim_token_uid, InnerPrimToken.interpreter) Hashtbl.t)

let prim_token_uninterpreters =
  (Hashtbl.create 7 : (prim_token_uid, InnerPrimToken.uninterpreter) Hashtbl.t)

(*******************************************************)
(* Numeral notation interpretation                     *)
type prim_token_notation_error =
  | UnexpectedTerm of Constr.t
  | UnexpectedNonOptionTerm of Constr.t

exception PrimTokenNotationError of string * Environ.env * Evd.evar_map * prim_token_notation_error

type numnot_option =
  | Nop
  | Warning of NumTok.UnsignedNat.t
  | Abstract of NumTok.UnsignedNat.t

type int_ty =
  { dec_uint : Names.inductive;
    dec_int : Names.inductive;
    hex_uint : Names.inductive;
    hex_int : Names.inductive;
    uint : Names.inductive;
    int : Names.inductive }

type z_pos_ty =
  { z_ty : Names.inductive;
    pos_ty : Names.inductive }

type numeral_ty =
  { int : int_ty;
    decimal : Names.inductive;
    hexadecimal : Names.inductive;
    numeral : Names.inductive }

type target_kind =
  | Int of int_ty (* Coq.Init.Numeral.int + uint *)
  | UInt of int_ty (* Coq.Init.Numeral.uint *)
  | Z of z_pos_ty (* Coq.Numbers.BinNums.Z and positive *)
  | Int63 (* Coq.Numbers.Cyclic.Int63.Int63.int *)
  | Numeral of numeral_ty (* Coq.Init.Numeral.numeral + uint + int *)
  | DecimalInt of int_ty (* Coq.Init.Decimal.int + uint (deprecated) *)
  | DecimalUInt of int_ty (* Coq.Init.Decimal.uint (deprecated) *)
  | Decimal of numeral_ty (* Coq.Init.Decimal.Decimal + uint + int (deprecated) *)

type string_target_kind =
  | ListByte
  | Byte

type option_kind = Option | Direct
type 'target conversion_kind = 'target * option_kind

type ('target, 'warning) prim_token_notation_obj =
  { to_kind : 'target conversion_kind;
    to_ty : GlobRef.t;
    of_kind : 'target conversion_kind;
    of_ty : GlobRef.t;
    ty_name : Libnames.qualid; (* for warnings / error messages *)
    warning : 'warning }

type numeral_notation_obj = (target_kind, numnot_option) prim_token_notation_obj
type string_notation_obj = (string_target_kind, unit) prim_token_notation_obj

module PrimTokenNotation = struct
(** * Code shared between Numeral notation and String notation *)
(** Reduction

    The constr [c] below isn't necessarily well-typed, since we
    built it via an [mkApp] of a conversion function on a term
    that starts with the right constructor but might be partially
    applied.

    At least [c] is known to be evar-free, since it comes from
    our own ad-hoc [constr_of_glob] or from conversions such
    as [coqint_of_rawnum].

    It is important to fully normalize the term, *including inductive
    parameters of constructors*; see
    https://github.com/coq/coq/issues/9840 for details on what goes
    wrong if this does not happen, e.g., from using the vm rather than
    cbv.
*)

let eval_constr env sigma (c : Constr.t) =
  let c = EConstr.of_constr c in
  let c' = Tacred.compute env sigma c in
  EConstr.Unsafe.to_constr c'

let eval_constr_app env sigma c1 c2 =
  eval_constr env sigma (mkApp (c1,[| c2 |]))

exception NotAValidPrimToken

(** The uninterp function below work at the level of [glob_constr]
    which is too low for us here. So here's a crude conversion back
    to [constr] for the subset that concerns us.

    Note that if you update [constr_of_glob], you should update the
    corresponding numeral notation *and* string notation doc in
    doc/sphinx/user-extensions/syntax-extensions.rst that describes
    what it means for a term to be ground / to be able to be
    considered for parsing. *)

let rec constr_of_glob env sigma g = match DAst.get g with
  | Glob_term.GRef (GlobRef.ConstructRef c, _) ->
      let sigma,c = Evd.fresh_constructor_instance env sigma c in
      sigma,mkConstructU c
  | Glob_term.GRef (GlobRef.IndRef c, _) ->
      let sigma,c = Evd.fresh_inductive_instance env sigma c in
      sigma,mkIndU c
  | Glob_term.GApp (gc, gcl) ->
      let sigma,c = constr_of_glob env sigma gc in
      let sigma,cl = List.fold_left_map (constr_of_glob env) sigma gcl in
      sigma,mkApp (c, Array.of_list cl)
  | Glob_term.GInt i -> sigma, mkInt i
  | Glob_term.GSort gs ->
      let sigma,c = Evd.fresh_sort_in_family sigma (Glob_ops.glob_sort_family gs) in
      sigma,mkSort c
  | _ ->
      raise NotAValidPrimToken

let rec glob_of_constr token_kind ?loc env sigma c = match Constr.kind c with
  | App (c, ca) ->
      let c = glob_of_constr token_kind ?loc env sigma c in
      let cel = List.map (glob_of_constr token_kind ?loc env sigma) (Array.to_list ca) in
      DAst.make ?loc (Glob_term.GApp (c, cel))
  | Construct (c, _) -> DAst.make ?loc (Glob_term.GRef (GlobRef.ConstructRef c, None))
  | Const (c, _) -> DAst.make ?loc (Glob_term.GRef (GlobRef.ConstRef c, None))
  | Ind ((ind, _), _) -> DAst.make ?loc (Glob_term.GRef (GlobRef.IndRef ind, None))
  | Var id -> DAst.make ?loc (Glob_term.GRef (GlobRef.VarRef id, None))
  | Int i -> DAst.make ?loc (Glob_term.GInt i)
  | Sort Sorts.SProp -> DAst.make ?loc (Glob_term.GSort (Glob_term.UNamed [Glob_term.GSProp, 0]))
  | Sort Sorts.Prop -> DAst.make ?loc (Glob_term.GSort (Glob_term.UNamed [Glob_term.GProp, 0]))
  | Sort Sorts.Set -> DAst.make ?loc (Glob_term.GSort (Glob_term.UNamed [Glob_term.GSet, 0]))
  | Sort (Sorts.Type _) -> DAst.make ?loc (Glob_term.GSort (Glob_term.UAnonymous {rigid=true}))
  | _ -> Loc.raise ?loc (PrimTokenNotationError(token_kind,env,sigma,UnexpectedTerm c))

let no_such_prim_token uninterpreted_token_kind ?loc ty =
  CErrors.user_err ?loc
   (str ("Cannot interpret this "^uninterpreted_token_kind^" as a value of type ") ++
    pr_qualid ty)

let interp_option uninterpreted_token_kind token_kind ty ?loc env sigma c =
  match Constr.kind c with
  | App (_Some, [| _; c |]) -> glob_of_constr token_kind ?loc env sigma c
  | App (_None, [| _ |]) -> no_such_prim_token uninterpreted_token_kind ?loc ty
  | x -> Loc.raise ?loc (PrimTokenNotationError(token_kind,env,sigma,UnexpectedNonOptionTerm c))

let uninterp_option c =
  match Constr.kind c with
  | App (_Some, [| _; x |]) -> x
  | _ -> raise NotAValidPrimToken

let uninterp to_raw o (Glob_term.AnyGlobConstr n) =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let sigma,of_ty = Evd.fresh_global env sigma o.of_ty in
  let of_ty = EConstr.Unsafe.to_constr of_ty in
  try
    let sigma,n = constr_of_glob env sigma n in
    let c = eval_constr_app env sigma of_ty n in
    let c = if snd o.of_kind == Direct then c else uninterp_option c in
    Some (to_raw (fst o.of_kind, c))
  with
  | Type_errors.TypeError _ | Pretype_errors.PretypeError _ -> None (* cf. eval_constr_app *)
  | NotAValidPrimToken -> None (* all other functions except NumTok.Signed.of_bigint *)

end

(** Conversion from bigint to int63 *)
let rec int63_of_pos_bigint i =
  let open Bigint in
  if equal i zero then Uint63.of_int 0
  else
    let (quo,rem) = div2_with_rest i in
    if rem then Uint63.add (Uint63.of_int 1)
      (Uint63.mul (Uint63.of_int 2) (int63_of_pos_bigint quo))
    else Uint63.mul (Uint63.of_int 2) (int63_of_pos_bigint quo)

module Numeral = struct
(** * Numeral notation *)
open PrimTokenNotation

let warn_large_num =
  CWarnings.create ~name:"large-number" ~category:"numbers"
    (fun ty ->
      strbrk "Stack overflow or segmentation fault happens when " ++
      strbrk "working with large numbers in " ++ pr_qualid ty ++
      strbrk " (threshold may vary depending" ++
      strbrk " on your system limits and on the command executed).")

let warn_abstract_large_num =
  CWarnings.create ~name:"abstract-large-number" ~category:"numbers"
    (fun (ty,f) ->
      strbrk "To avoid stack overflow, large numbers in " ++
      pr_qualid ty ++ strbrk " are interpreted as applications of " ++
      Nametab.pr_global_env (Termops.vars_of_env (Global.env ())) f ++ strbrk ".")

(***********************************************************************)

(** ** Conversion between Coq [Decimal.int] and internal raw string *)

(** Decimal.Nil has index 1, then Decimal.D0 has index 2 .. Decimal.D9 is 11 *)

let digit_of_char c =
  assert ('0' <= c && c <= '9' || 'a' <= c && c <= 'f');
  if c <= '9' then Char.code c - Char.code '0' + 2
  else Char.code c - Char.code 'a' + 12

let char_of_digit n =
  assert (2<=n && n<=17);
  if n <= 11 then Char.chr (n-2 + Char.code '0')
  else Char.chr (n-12 + Char.code 'a')

let coquint_of_rawnum inds c n =
  let uint = match c with CDec -> inds.dec_uint | CHex -> inds.hex_uint in
  let nil = mkConstruct (uint,1) in
  match n with None -> nil | Some n ->
  let str = NumTok.UnsignedNat.to_string n in
  let str = match c with
    | CDec -> str
    | CHex -> String.sub str 2 (String.length str - 2) in  (* cut "0x" *)
  let rec do_chars s i acc =
    if i < 0 then acc
    else
      let dg = mkConstruct (uint, digit_of_char s.[i]) in
      do_chars s (i-1) (mkApp(dg,[|acc|]))
  in
  do_chars str (String.length str - 1) nil

let coqint_of_rawnum inds c (sign,n) =
  let ind = match c with CDec -> inds.dec_int | CHex -> inds.hex_int in
  let uint = coquint_of_rawnum inds c (Some n) in
  let pos_neg = match sign with SPlus -> 1 | SMinus -> 2 in
  mkApp (mkConstruct (ind, pos_neg), [|uint|])

let coqnumeral_of_rawnum inds c n =
  let ind = match c with CDec -> inds.decimal | CHex -> inds.hexadecimal in
  let i, f, e = NumTok.Signed.to_int_frac_and_exponent n in
  let i = coqint_of_rawnum inds.int c i in
  let f = coquint_of_rawnum inds.int c f in
  match e with
  | None -> mkApp (mkConstruct (ind, 1), [|i; f|])  (* (D|Hexad)ecimal *)
  | Some e ->
    let e = coqint_of_rawnum inds.int CDec e in
    mkApp (mkConstruct (ind, 2), [|i; f; e|])  (* (D|Hexad)ecimalExp *)

let mkDecHex ind c n = match c with
  | CDec -> mkApp (mkConstruct (ind, 1), [|n|])  (* (UInt|Int|)Dec *)
  | CHex -> mkApp (mkConstruct (ind, 2), [|n|])  (* (UInt|Int|)Hex *)

exception NonDecimal

let decimal_coqnumeral_of_rawnum inds n =
  if NumTok.Signed.classify n <> CDec then raise NonDecimal;
  coqnumeral_of_rawnum inds CDec n

let coqnumeral_of_rawnum inds n =
  let c = NumTok.Signed.classify n in
  let n = coqnumeral_of_rawnum inds c n in
  mkDecHex inds.numeral c n

let decimal_coquint_of_rawnum inds n =
  if NumTok.UnsignedNat.classify n <> CDec then raise NonDecimal;
  coquint_of_rawnum inds CDec (Some n)

let coquint_of_rawnum inds n =
  let c = NumTok.UnsignedNat.classify n in
  let n = coquint_of_rawnum inds c (Some n) in
  mkDecHex inds.uint c n

let decimal_coqint_of_rawnum inds n =
  if NumTok.SignedNat.classify n <> CDec then raise NonDecimal;
  coqint_of_rawnum inds CDec n

let coqint_of_rawnum inds n =
  let c = NumTok.SignedNat.classify n in
  let n = coqint_of_rawnum inds c n in
  mkDecHex inds.int c n

let rawnum_of_coquint cl c =
  let rec of_uint_loop c buf =
    match Constr.kind c with
    | Construct ((_,1), _) (* Nil *) -> ()
    | App (c, [|a|]) ->
       (match Constr.kind c with
        | Construct ((_,n), _) (* D0 to Df *) ->
           let () = Buffer.add_char buf (char_of_digit n) in
           of_uint_loop a buf
        | _ -> raise NotAValidPrimToken)
    | _ -> raise NotAValidPrimToken
  in
  let buf = Buffer.create 64 in
  if cl = CHex then (Buffer.add_char buf '0'; Buffer.add_char buf 'x');
  let () = of_uint_loop c buf in
  if Int.equal (Buffer.length buf) (match cl with CDec -> 0 | CHex -> 2) then
    (* To avoid ambiguities between Nil and (D0 Nil), we choose
       to not display Nil alone as "0" *)
    raise NotAValidPrimToken
  else NumTok.UnsignedNat.of_string (Buffer.contents buf)

let rawnum_of_coqint cl c =
  match Constr.kind c with
  | App (c,[|c'|]) ->
     (match Constr.kind c with
      | Construct ((_,1), _) (* Pos *) -> (SPlus,rawnum_of_coquint cl c')
      | Construct ((_,2), _) (* Neg *) -> (SMinus,rawnum_of_coquint cl c')
      | _ -> raise NotAValidPrimToken)
  | _ -> raise NotAValidPrimToken

let rawnum_of_coqnumeral cl c =
  let of_ife i f e =
    let n = rawnum_of_coqint cl i in
    let f = try Some (rawnum_of_coquint cl f) with NotAValidPrimToken -> None in
    let e = match e with None -> None | Some e -> Some (rawnum_of_coqint CDec e) in
    NumTok.Signed.of_int_frac_and_exponent n f e in
  match Constr.kind c with
  | App (_,[|i; f|]) -> of_ife i f None
  | App (_,[|i; f; e|]) -> of_ife i f (Some e)
  | _ -> raise NotAValidPrimToken

let destDecHex c = match Constr.kind c with
  | App (c,[|c'|]) ->
     (match Constr.kind c with
      | Construct ((_,1), _) (* (UInt|Int|)Dec *) -> CDec, c'
      | Construct ((_,2), _) (* (UInt|Int|)Hex *) -> CHex, c'
      | _ -> raise NotAValidPrimToken)
  | _ -> raise NotAValidPrimToken

let decimal_rawnum_of_coqnumeral c =
  rawnum_of_coqnumeral CDec c

let rawnum_of_coqnumeral c =
  let cl, c = destDecHex c in
  rawnum_of_coqnumeral cl c

let decimal_rawnum_of_coquint c =
  rawnum_of_coquint CDec c

let rawnum_of_coquint c =
  let cl, c = destDecHex c in
  rawnum_of_coquint cl c

let decimal_rawnum_of_coqint c =
  rawnum_of_coqint CDec c

let rawnum_of_coqint c =
  let cl, c = destDecHex c in
  rawnum_of_coqint cl c

(***********************************************************************)

(** ** Conversion between Coq [Z] and internal bigint *)

(** First, [positive] from/to bigint *)

let rec pos_of_bigint posty n =
  match Bigint.div2_with_rest n with
  | (q, false) ->
      let c = mkConstruct (posty, 2) in (* xO *)
      mkApp (c, [| pos_of_bigint posty q |])
  | (q, true) when not (Bigint.equal q Bigint.zero) ->
      let c = mkConstruct (posty, 1) in (* xI *)
      mkApp (c, [| pos_of_bigint posty q |])
  | (q, true) ->
      mkConstruct (posty, 3) (* xH *)

let rec bigint_of_pos c = match Constr.kind c with
  | Construct ((_, 3), _) -> (* xH *) Bigint.one
  | App (c, [| d |]) ->
      begin match Constr.kind c with
      | Construct ((_, n), _) ->
          begin match n with
          | 1 -> (* xI *) Bigint.add_1 (Bigint.mult_2 (bigint_of_pos d))
          | 2 -> (* xO *) Bigint.mult_2 (bigint_of_pos d)
          | n -> assert false (* no other constructor of type positive *)
          end
      | x -> raise NotAValidPrimToken
      end
  | x -> raise NotAValidPrimToken

(** Now, [Z] from/to bigint *)

let z_of_bigint { z_ty; pos_ty } n =
  if Bigint.equal n Bigint.zero then
    mkConstruct (z_ty, 1) (* Z0 *)
  else
    let (s, n) =
      if Bigint.is_pos_or_zero n then (2, n) (* Zpos *)
      else (3, Bigint.neg n) (* Zneg *)
    in
    let c = mkConstruct (z_ty, s) in
    mkApp (c, [| pos_of_bigint pos_ty n |])

let bigint_of_z z = match Constr.kind z with
  | Construct ((_, 1), _) -> (* Z0 *) Bigint.zero
  | App (c, [| d |]) ->
      begin match Constr.kind c with
      | Construct ((_, n), _) ->
          begin match n with
          | 2 -> (* Zpos *) bigint_of_pos d
          | 3 -> (* Zneg *) Bigint.neg (bigint_of_pos d)
          | n -> assert false (* no other constructor of type Z *)
          end
      | _ -> raise NotAValidPrimToken
      end
  | _ -> raise NotAValidPrimToken

(** Now, [Int63] from/to bigint *)

let int63_of_pos_bigint ?loc n =
  let i = int63_of_pos_bigint n in
  mkInt i

let error_negative ?loc =
  CErrors.user_err ?loc ~hdr:"interp_int63" (Pp.str "int63 are only non-negative numbers.")

let error_overflow ?loc n =
  CErrors.user_err ?loc ~hdr:"interp_int63" Pp.(str "overflow in int63 literal: " ++ str (Bigint.to_string n))

let interp_int63 ?loc n =
  let open Bigint in
  if is_pos_or_zero n
  then
    if less_than n (pow two 63)
    then int63_of_pos_bigint ?loc n
    else error_overflow ?loc n
  else error_negative ?loc

let bigint_of_int63 c =
  match Constr.kind c with
  | Int i -> Bigint.of_string (Uint63.to_string i)
  | _ -> raise NotAValidPrimToken

let interp o ?loc n =
  begin match o.warning, n with
  | Warning threshold, n when NumTok.Signed.is_bigger_int_than n threshold ->
     warn_large_num o.ty_name
  | _ -> ()
  end;
  let c = match fst o.to_kind, NumTok.Signed.to_int n with
    | Int int_ty, Some n ->
       coqint_of_rawnum int_ty n
    | UInt int_ty, Some (SPlus, n) ->
       coquint_of_rawnum int_ty n
    | DecimalInt int_ty, Some n ->
       (try decimal_coqint_of_rawnum int_ty n
        with NonDecimal -> no_such_prim_token "number" ?loc o.ty_name)
    | DecimalUInt int_ty, Some (SPlus, n) ->
       (try decimal_coquint_of_rawnum int_ty n
        with NonDecimal -> no_such_prim_token "number" ?loc o.ty_name)
    | Z z_pos_ty, Some n ->
       z_of_bigint z_pos_ty (NumTok.SignedNat.to_bigint n)
    | Int63, Some n ->
       interp_int63 ?loc (NumTok.SignedNat.to_bigint n)
    | (Int _ | UInt _ | DecimalInt _ | DecimalUInt _ | Z _ | Int63), _ ->
       no_such_prim_token "number" ?loc o.ty_name
    | Numeral numeral_ty, _ -> coqnumeral_of_rawnum numeral_ty n
    | Decimal numeral_ty, _ ->
       (try decimal_coqnumeral_of_rawnum numeral_ty n
        with NonDecimal -> no_such_prim_token "number" ?loc o.ty_name)
  in
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let sigma,to_ty = Evd.fresh_global env sigma o.to_ty in
  let to_ty = EConstr.Unsafe.to_constr to_ty in
  match o.warning, snd o.to_kind with
  | Abstract threshold, Direct when NumTok.Signed.is_bigger_int_than n threshold ->
     warn_abstract_large_num (o.ty_name,o.to_ty);
     glob_of_constr "numeral" ?loc env sigma (mkApp (to_ty,[|c|]))
  | _ ->
     let res = eval_constr_app env sigma to_ty c in
     match snd o.to_kind with
     | Direct -> glob_of_constr "numeral" ?loc env sigma res
     | Option -> interp_option "number" "numeral" o.ty_name ?loc env sigma res

let uninterp o n =
  PrimTokenNotation.uninterp
    begin function
      | (Int _, c) -> NumTok.Signed.of_int (rawnum_of_coqint c)
      | (UInt _, c) -> NumTok.Signed.of_nat (rawnum_of_coquint c)
      | (Z _, c) -> NumTok.Signed.of_bigint CDec (bigint_of_z c)
      | (Int63, c) -> NumTok.Signed.of_bigint CDec (bigint_of_int63 c)
      | (Numeral _, c) -> rawnum_of_coqnumeral c
      | (DecimalInt _, c) -> NumTok.Signed.of_int (decimal_rawnum_of_coqint c)
      | (DecimalUInt _, c) -> NumTok.Signed.of_nat (decimal_rawnum_of_coquint c)
      | (Decimal _, c) -> decimal_rawnum_of_coqnumeral c
    end o n
end

module Strings = struct
(** * String notation *)
open PrimTokenNotation

let qualid_of_ref n =
  n |> Coqlib.lib_ref |> Nametab.shortest_qualid_of_global Id.Set.empty

let q_list () = qualid_of_ref "core.list.type"
let q_byte () = qualid_of_ref "core.byte.type"

let unsafe_locate_ind q =
  match Nametab.locate q with
  | GlobRef.IndRef i -> i
  | _ -> raise Not_found

let locate_list () = unsafe_locate_ind (q_list ())
let locate_byte () = unsafe_locate_ind (q_byte ())

(***********************************************************************)

(** ** Conversion between Coq [list Byte.byte] and internal raw string *)

let coqbyte_of_char_code byte c =
  mkConstruct (byte, 1 + c)

let coqbyte_of_string ?loc byte s =
  let p =
    if Int.equal (String.length s) 1 then int_of_char s.[0]
    else
      if Int.equal (String.length s) 3 && is_digit s.[0] && is_digit s.[1] && is_digit s.[2]
      then int_of_string s
      else
       user_err ?loc ~hdr:"coqbyte_of_string"
         (str "Expects a single character or a three-digits ascii code.") in
  coqbyte_of_char_code byte p

let coqbyte_of_char byte c = coqbyte_of_char_code byte (Char.code c)

let make_ascii_string n =
  if n>=32 && n<=126 then String.make 1 (char_of_int n)
  else Printf.sprintf "%03d" n

let char_code_of_coqbyte c =
  match Constr.kind c with
  | Construct ((_,c), _) -> c - 1
  | _ -> raise NotAValidPrimToken

let string_of_coqbyte c = make_ascii_string (char_code_of_coqbyte c)

let coqlist_byte_of_string byte_ty list_ty str =
  let cbyte = mkInd byte_ty in
  let nil = mkApp (mkConstruct (list_ty, 1), [|cbyte|]) in
  let cons x xs = mkApp (mkConstruct (list_ty, 2), [|cbyte; x; xs|]) in
  let rec do_chars s i acc =
    if i < 0 then acc
    else
      let b = coqbyte_of_char byte_ty s.[i] in
      do_chars s (i-1) (cons b acc)
  in
  do_chars str (String.length str - 1) nil

(* N.B. We rely on the fact that [nil] is the first constructor and [cons] is the second constructor, for [list] *)
let string_of_coqlist_byte c =
  let rec of_coqlist_byte_loop c buf =
    match Constr.kind c with
    | App (_nil, [|_ty|]) -> ()
    | App (_cons, [|_ty;b;c|]) ->
      let () = Buffer.add_char buf (Char.chr (char_code_of_coqbyte b)) in
      of_coqlist_byte_loop c buf
    | _ -> raise NotAValidPrimToken
  in
  let buf = Buffer.create 64 in
  let () = of_coqlist_byte_loop c buf in
  Buffer.contents buf

let interp o ?loc n =
  let byte_ty = locate_byte () in
  let list_ty = locate_list () in
  let c = match fst o.to_kind with
    | ListByte -> coqlist_byte_of_string byte_ty list_ty n
    | Byte -> coqbyte_of_string ?loc byte_ty n
  in
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let sigma,to_ty = Evd.fresh_global env sigma o.to_ty in
  let to_ty = EConstr.Unsafe.to_constr to_ty in
  let res = eval_constr_app env sigma to_ty c in
  match snd o.to_kind with
  | Direct -> glob_of_constr "string" ?loc env sigma res
  | Option -> interp_option "string" "string" o.ty_name ?loc env sigma res

let uninterp o n =
  PrimTokenNotation.uninterp
    begin function
      | (ListByte, c) -> string_of_coqlist_byte c
      | (Byte, c) -> string_of_coqbyte c
    end o n
end

(* A [prim_token_infos], which is synchronized with the document
   state, either contains a unique id pointing to an unsynchronized
   prim token function, or a numeral notation object describing how to
   interpret and uninterpret.  We provide [prim_token_infos] because
   we expect plugins to provide their own interpretation functions,
   rather than going through numeral notations, which are available as
   a vernacular. *)

type prim_token_interp_info =
    Uid of prim_token_uid
  | NumeralNotation of numeral_notation_obj
  | StringNotation of string_notation_obj

type prim_token_infos = {
  pt_local : bool; (** Is this interpretation local? *)
  pt_scope : scope_name; (** Concerned scope *)
  pt_interp_info : prim_token_interp_info; (** Unique id "pointing" to (un)interp functions, OR a numeral notation object describing (un)interp functions *)
  pt_required : required_module; (** Module that should be loaded first *)
  pt_refs : GlobRef.t list; (** Entry points during uninterpretation *)
  pt_in_match : bool (** Is this prim token legal in match patterns ? *)
}

(* Table from scope_name to backtrack-able informations about interpreters
   (in particular interpreter unique id). *)
let prim_token_interp_infos =
  ref (String.Map.empty : (required_module * prim_token_interp_info) String.Map.t)

(* Table from global_reference to backtrack-able informations about
   prim_token uninterpretation (in particular uninterpreter unique id). *)
let prim_token_uninterp_infos =
  ref (GlobRef.Map.empty : ((scope_name * (prim_token_interp_info * bool)) list) GlobRef.Map.t)

let hashtbl_check_and_set allow_overwrite uid f h eq =
  match Hashtbl.find h uid with
   | exception Not_found -> Hashtbl.add h uid f
   | _ when allow_overwrite -> Hashtbl.add h uid f
   | g when eq f g -> ()
   | _ ->
      user_err ~hdr:"prim_token_interpreter"
       (str "Unique identifier " ++ str uid ++
        str " already used to register a numeral or string (un)interpreter.")

let register_gen_interpretation allow_overwrite uid (interp, uninterp) =
  hashtbl_check_and_set
    allow_overwrite uid interp prim_token_interpreters InnerPrimToken.interp_eq;
  hashtbl_check_and_set
    allow_overwrite uid uninterp prim_token_uninterpreters InnerPrimToken.uninterp_eq

let register_rawnumeral_interpretation ?(allow_overwrite=false) uid (interp, uninterp) =
  register_gen_interpretation allow_overwrite uid
    (InnerPrimToken.RawNumInterp interp, InnerPrimToken.RawNumUninterp uninterp)

let register_bignumeral_interpretation ?(allow_overwrite=false) uid (interp, uninterp) =
  register_gen_interpretation allow_overwrite uid
    (InnerPrimToken.BigNumInterp interp, InnerPrimToken.BigNumUninterp uninterp)

let register_string_interpretation ?(allow_overwrite=false) uid (interp, uninterp) =
  register_gen_interpretation allow_overwrite uid
    (InnerPrimToken.StringInterp interp, InnerPrimToken.StringUninterp uninterp)

let cache_prim_token_interpretation (_,infos) =
  let ptii = infos.pt_interp_info in
  let sc = infos.pt_scope in
  check_scope ~tolerant:true sc;
  prim_token_interp_infos :=
    String.Map.add sc (infos.pt_required,ptii) !prim_token_interp_infos;
  let add_uninterp r =
    let l = try GlobRef.Map.find r !prim_token_uninterp_infos with Not_found -> [] in
    let l = List.remove_assoc_f String.equal sc l in
    prim_token_uninterp_infos :=
      GlobRef.Map.add r ((sc,(ptii,infos.pt_in_match)) :: l)
        !prim_token_uninterp_infos in
  List.iter add_uninterp infos.pt_refs

let subst_prim_token_interpretation (subs,infos) =
  { infos with
    pt_refs = List.map (subst_global_reference subs) infos.pt_refs }

let classify_prim_token_interpretation infos =
    if infos.pt_local then Dispose else Substitute infos

let open_prim_token_interpretation i o =
  if Int.equal i 1 then cache_prim_token_interpretation o

let inPrimTokenInterp : prim_token_infos -> obj =
  declare_object {(default_object "PRIM-TOKEN-INTERP") with
     open_function  = simple_open open_prim_token_interpretation;
     cache_function = cache_prim_token_interpretation;
     subst_function = subst_prim_token_interpretation;
     classify_function = classify_prim_token_interpretation}

let enable_prim_token_interpretation infos =
  Lib.add_anonymous_leaf (inPrimTokenInterp infos)

(** Compatibility.
    Avoid the next two functions, they will now store unnecessary
    objects in the library segment. Instead, combine
    [register_*_interpretation] and [enable_prim_token_interpretation]
    (the latter inside a [Mltop.declare_cache_obj]).
*)

let fresh_string_of =
  let count = ref 0 in
  fun root -> count := !count+1; (string_of_int !count)^"_"^root

let declare_numeral_interpreter ?(local=false) sc dir interp (patl,uninterp,b) =
  let uid = fresh_string_of sc in
  register_bignumeral_interpretation uid (interp,uninterp);
  enable_prim_token_interpretation
    { pt_local = local;
      pt_scope = sc;
      pt_interp_info = Uid uid;
      pt_required = dir;
      pt_refs = List.map_filter glob_prim_constr_key patl;
      pt_in_match = b }
let declare_string_interpreter ?(local=false) sc dir interp (patl,uninterp,b) =
  let uid = fresh_string_of sc in
  register_string_interpretation uid (interp,uninterp);
  enable_prim_token_interpretation
    { pt_local = local;
      pt_scope = sc;
      pt_interp_info = Uid uid;
      pt_required = dir;
      pt_refs = List.map_filter glob_prim_constr_key patl;
      pt_in_match = b }


let check_required_module ?loc sc (sp,d) =
  try let _ = Nametab.global_of_path sp in ()
  with Not_found as exn ->
    let _, info = Exninfo.capture exn in
    match d with
    | [] ->
      user_err ?loc ~info ~hdr:"prim_token_interpreter"
        (str "Cannot interpret in " ++ str sc ++ str " because " ++ pr_path sp ++
         str " could not be found in the current environment.")
    | _ ->
      user_err ?loc ~info ~hdr:"prim_token_interpreter"
        (str "Cannot interpret in " ++ str sc ++ str " without requiring first module " ++
         str (List.last d) ++ str ".")

(* Look if some notation or numeral printer in [scope] can be used in
   the scope stack [scopes], and if yes, using delimiters or not *)

let find_with_delimiters = function
  | LastLonelyNotation -> None
  | NotationInScope scope ->
      match (String.Map.find scope !scope_map).delimiters with
        | Some key -> Some (Some scope, Some key)
        | None -> None

let rec find_without_delimiters find (ntn_scope,ntn) = function
  | OpenScopeItem scope :: scopes ->
      (* Is the expected ntn/numpr attached to the most recently open scope? *)
      begin match ntn_scope with
      | NotationInScope scope' when String.equal scope scope' ->
        Some (None,None)
      | _ ->
        (* If the most recently open scope has a notation/numeral printer
           but not the expected one then we need delimiters *)
        if find scope then
          find_with_delimiters ntn_scope
        else
          find_without_delimiters find (ntn_scope,ntn) scopes
      end
  | LonelyNotationItem ntn' :: scopes ->
      begin match ntn_scope, ntn with
      | LastLonelyNotation, Some ntn when notation_eq ntn ntn' ->
        Some (None, None)
      | _ ->
        find_without_delimiters find (ntn_scope,ntn) scopes
      end
  | [] ->
      (* Can we switch to [scope]? Yes if it has defined delimiters *)
      find_with_delimiters ntn_scope

(* The mapping between notations and their interpretation *)

let warn_notation_overridden =
  CWarnings.create ~name:"notation-overridden" ~category:"parsing"
                   (fun (ntn,which_scope) ->
                    str "Notation" ++ spc () ++ pr_notation ntn ++ spc ()
                    ++ strbrk "was already used" ++ which_scope ++ str ".")

let declare_notation_interpretation ntn scopt pat df ~onlyprint deprecation =
  let scope = match scopt with Some s -> s | None -> default_scope in
  let sc = find_scope scope in
  if not onlyprint then begin
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
      not_deprecation = deprecation;
    } in
    let sc = { sc with notations = NotationMap.add ntn notdata sc.notations } in
    scope_map := String.Map.add scope sc !scope_map
  end;
  begin match scopt with
  | None -> scope_stack := LonelyNotationItem ntn :: !scope_stack
  | Some _ -> ()
  end

let declare_uninterpretation rule (metas,c as pat) =
  let (key,n) = notation_constr_key c in
  notations_key_table := keymap_add key (rule,pat,n) !notations_key_table

let rec find_interpretation ntn find = function
  | [] -> raise Not_found
  | OpenScopeItem scope :: scopes ->
      (try let n = find scope in (n,Some scope)
       with Not_found -> find_interpretation ntn find scopes)
  | LonelyNotationItem ntn'::scopes when notation_eq ntn' ntn ->
      (try let n = find default_scope in (n,None)
       with Not_found ->
         (* e.g. because single notation only for constr, not cases_pattern *)
         find_interpretation ntn find scopes)
  | LonelyNotationItem _::scopes ->
      find_interpretation ntn find scopes

let find_notation ntn sc =
  NotationMap.find ntn (find_scope sc).notations

let notation_of_prim_token = function
  | Constrexpr.Numeral (SPlus,n) -> InConstrEntrySomeLevel, NumTok.Unsigned.sprint n
  | Constrexpr.Numeral (SMinus,n) -> InConstrEntrySomeLevel, "- "^NumTok.Unsigned.sprint n
  | String _ -> raise Not_found

let find_prim_token check_allowed ?loc p sc =
  (* Try for a user-defined numerical notation *)
  try
    let n = find_notation (notation_of_prim_token p) sc in
    let (_,c) = n.not_interp in
    let df = n.not_location in
    let pat = Notation_ops.glob_constr_of_notation_constr ?loc c in
    check_allowed pat;
    pat, df
  with Not_found ->
  (* Try for a primitive numerical notation *)
  let (spdir,info) = String.Map.find sc !prim_token_interp_infos in
  check_required_module ?loc sc spdir;
  let interp = match info with
    | Uid uid -> Hashtbl.find prim_token_interpreters uid
    | NumeralNotation o -> InnerPrimToken.RawNumInterp (Numeral.interp o)
    | StringNotation o -> InnerPrimToken.StringInterp (Strings.interp o)
  in
  let pat = InnerPrimToken.do_interp ?loc interp p in
  check_allowed pat;
  pat, ((dirpath (fst spdir),DirPath.empty),"")

let interp_prim_token_gen ?loc g p local_scopes =
  let scopes = make_current_scopes local_scopes in
  let p_as_ntn = try notation_of_prim_token p with Not_found -> InConstrEntrySomeLevel,"" in
  try
    let (pat,loc), sc = find_interpretation p_as_ntn (find_prim_token ?loc g p) scopes in
    pat, (loc,sc)
  with Not_found as exn ->
    let _, info = Exninfo.capture exn in
    user_err ?loc ~info ~hdr:"interp_prim_token"
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

let warn_deprecated_notation =
  Deprecation.create_warning ~object_name:"Notation" ~warning_name:"deprecated-notation"
    pr_notation

let interp_notation ?loc ntn local_scopes =
  let scopes = make_current_scopes local_scopes in
  try
    let (n,sc) = find_interpretation ntn (find_notation ntn) scopes in
    Option.iter (fun d -> warn_deprecated_notation ?loc (ntn,d)) n.not_deprecation;
    n.not_interp, (n.not_location, sc)
  with Not_found as exn ->
    let _, info = Exninfo.capture exn in
    user_err ?loc ~info
      (str "Unknown interpretation for notation " ++ pr_notation ntn ++ str ".")

let uninterp_notations c =
  List.map_append (fun key -> keymap_find key !notations_key_table)
    (glob_constr_keys c)

let uninterp_cases_pattern_notations c =
  keymap_find (cases_pattern_key c) !notations_key_table

let uninterp_ind_pattern_notations ind =
  keymap_find (RefKey (canonical_gr (GlobRef.IndRef ind))) !notations_key_table

let availability_of_notation (ntn_scope,ntn) scopes =
  let f scope =
    NotationMap.mem ntn (String.Map.find scope !scope_map).notations in
  find_without_delimiters f (ntn_scope,Some ntn) (make_current_scopes scopes)

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
   let compare = pervasives_compare
 end

module EntryCoercionMap = Map.Make(EntryCoercionOrd)

let entry_coercion_map = ref EntryCoercionMap.empty

let level_ord lev lev' =
  match lev, lev' with
  | None, _ -> true
  | _, None -> true
  | Some n, Some n' -> n <= n'

let rec search nfrom nto = function
  | [] -> raise Not_found
  | ((pfrom,pto),coe)::l ->
    if level_ord pfrom nfrom && level_ord nto pto then coe else search nfrom nto l

let decompose_custom_entry = function
  | InConstrEntrySomeLevel -> InConstrEntry, None
  | InCustomEntryLevel (s,n) -> InCustomEntry s, Some n

let availability_of_entry_coercion entry entry' =
  let entry, lev = decompose_custom_entry entry in
  let entry', lev' = decompose_custom_entry entry' in
  if notation_entry_eq entry entry' && level_ord lev' lev then Some []
  else
    try Some (search lev lev' (EntryCoercionMap.find (entry,entry') !entry_coercion_map))
    with Not_found -> None

let better_path ((lev1,lev2),path) ((lev1',lev2'),path') =
  (* better = shorter and lower source and higher target *)
  level_ord lev1 lev1' && level_ord lev2' lev2 && List.length path <= List.length path'

let shorter_path (_,path) (_,path') =
  List.length path <= List.length path'

let rec insert_coercion_path path = function
  | [] -> [path]
  | path'::paths as allpaths ->
      (* If better or equal we keep the more recent one *)
      if better_path path path' then path::paths
      else if better_path path' path then allpaths
      else if shorter_path path path' then path::allpaths
      else path'::insert_coercion_path path paths

let declare_entry_coercion (scope,(entry,_) as specific_ntn) entry' =
  let entry, lev = decompose_custom_entry entry in
  let entry', lev' = decompose_custom_entry entry' in
  (* Transitive closure *)
  let toaddleft =
    EntryCoercionMap.fold (fun (entry'',entry''') paths l ->
        List.fold_right (fun ((lev'',lev'''),path) l ->
        if notation_entry_eq entry entry''' && level_ord lev lev''' &&
           not (notation_entry_eq entry' entry'')
        then ((entry'',entry'),((lev'',lev'),path@[specific_ntn]))::l else l) paths l)
      !entry_coercion_map [] in
  let toaddright =
    EntryCoercionMap.fold (fun (entry'',entry''') paths l ->
        List.fold_right (fun ((lev'',lev'''),path) l ->
        if entry' = entry'' && level_ord lev' lev'' && entry <> entry'''
        then ((entry,entry'''),((lev,lev'''),path@[specific_ntn]))::l else l) paths l)
      !entry_coercion_map [] in
  entry_coercion_map :=
    List.fold_right (fun (pair,path) ->
        let olds = try EntryCoercionMap.find pair !entry_coercion_map with Not_found -> [] in
        EntryCoercionMap.add pair (insert_coercion_path path olds))
      (((entry,entry'),((lev,lev'),[specific_ntn]))::toaddright@toaddleft)
      !entry_coercion_map

let entry_has_global_map = ref String.Map.empty

let declare_custom_entry_has_global s n =
  try
    let p = String.Map.find s !entry_has_global_map in
    user_err (str "Custom entry " ++ str s ++
              str " has already a rule for global references at level " ++ int p ++ str ".")
  with Not_found ->
    entry_has_global_map := String.Map.add s n !entry_has_global_map

let entry_has_global = function
  | InConstrEntrySomeLevel -> true
  | InCustomEntryLevel (s,n) ->
     try String.Map.find s !entry_has_global_map <= n with Not_found -> false

let entry_has_ident_map = ref String.Map.empty

let declare_custom_entry_has_ident s n =
  try
    let p = String.Map.find s !entry_has_ident_map in
    user_err (str "Custom entry " ++ str s ++
              str " has already a rule for global references at level " ++ int p ++ str ".")
  with Not_found ->
    entry_has_ident_map := String.Map.add s n !entry_has_ident_map

let entry_has_ident = function
  | InConstrEntrySomeLevel -> true
  | InCustomEntryLevel (s,n) ->
     try String.Map.find s !entry_has_ident_map <= n with Not_found -> false

let availability_of_prim_token n printer_scope local_scopes =
  let f scope =
    try
      let uid = snd (String.Map.find scope !prim_token_interp_infos) in
      let open InnerPrimToken in
      match n, uid with
      | Constrexpr.Numeral _, NumeralNotation _ -> true
      | _, NumeralNotation _ -> false
      | String _, StringNotation _ -> true
      | _, StringNotation _ -> false
      | _, Uid uid ->
        let interp = Hashtbl.find prim_token_interpreters uid in
        match n, interp with
        | Constrexpr.Numeral _, (RawNumInterp _ | BigNumInterp _) -> true
        | String _, StringInterp _ -> true
        | _ -> false
    with Not_found -> false
  in
  let scopes = make_current_scopes local_scopes in
  Option.map snd (find_without_delimiters f (NotationInScope printer_scope,None) scopes)

let rec find_uninterpretation need_delim def find = function
  | [] ->
      List.find_map
        (fun (sc,_,_) -> try Some (find need_delim sc) with Not_found -> None)
        def
  | OpenScopeItem scope :: scopes ->
      (try find need_delim scope
       with Not_found -> find_uninterpretation need_delim def find scopes)  (* TODO: here we should also update the need_delim list with all regular notations in scope [scope] that could shadow a numeral notation *)
  | LonelyNotationItem ntn::scopes ->
      find_uninterpretation (ntn::need_delim) def find scopes

let uninterp_prim_token c local_scopes =
  match glob_prim_constr_key c with
  | None -> raise Notation_ops.No_match
  | Some r ->
     let uninterp (sc,(info,_)) =
       try
         let uninterp = match info with
           | Uid uid -> Hashtbl.find prim_token_uninterpreters uid
           | NumeralNotation o -> InnerPrimToken.RawNumUninterp (Numeral.uninterp o)
           | StringNotation o -> InnerPrimToken.StringUninterp (Strings.uninterp o)
         in
         match InnerPrimToken.do_uninterp uninterp (AnyGlobConstr c) with
         | None -> None
         | Some n -> Some (sc,n)
       with Not_found -> None in
     let add_key (sc,n) =
       Option.map (fun k -> sc,n,k) (availability_of_prim_token n sc local_scopes) in
     let l =
       try GlobRef.Map.find r !prim_token_uninterp_infos
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

let uninterp_prim_token_cases_pattern c local_scopes =
  match glob_constr_of_closed_cases_pattern (Global.env()) c with
  | exception Not_found -> raise Notation_ops.No_match
  | na,c -> let (sc,n) = uninterp_prim_token c local_scopes in (na,sc,n)

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
  notation_entry_level_eq entry1 entry2 &&
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
    interpretation_eq n.not_interp r
  with Not_found -> false

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

let rec compute_arguments_classes env sigma t =
  match EConstr.kind sigma (Reductionops.whd_betaiotazeta env sigma t) with
    | Prod (na, t, u) ->
        let env = EConstr.push_rel (Context.Rel.Declaration.LocalAssum (na, t)) env in
        let cl = try Some (compute_scope_class env sigma t) with Not_found -> None in
        cl :: compute_arguments_classes env sigma u
    | _ -> []

let compute_arguments_scope_full env sigma t =
  let cls = compute_arguments_classes env sigma t in
  let scs = List.map find_scope_class_opt cls in
  scs, cls

let compute_arguments_scope env sigma t = fst (compute_arguments_scope_full env sigma t)

let compute_type_scope env sigma t =
  find_scope_class_opt (try Some (compute_scope_class env sigma t) with Not_found -> None)

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

let arguments_scope = ref GlobRef.Map.empty

type arguments_scope_discharge_request =
  | ArgsScopeAuto
  | ArgsScopeManual
  | ArgsScopeNoDischarge

let load_arguments_scope _ (_,(_,r,n,scl,cls)) =
  List.iter (Option.iter check_scope) scl;
  let initial_stamp = ScopeClassMap.empty in
  arguments_scope := GlobRef.Map.add r (scl,cls,initial_stamp) !arguments_scope

let cache_arguments_scope o =
  load_arguments_scope 1 o

let subst_scope_class env subst cs =
  try Some (subst_cl_typ env subst cs) with Not_found -> None

let subst_arguments_scope (subst,(req,r,n,scl,cls)) =
  let r' = fst (subst_global subst r) in
  let subst_cl ocl = match ocl with
    | None -> ocl
    | Some cl ->
        let env = Global.env () in
        match subst_scope_class env subst cl with
        | Some cl'  as ocl' when cl' != cl -> ocl'
        | _ -> ocl in
  let cls' = List.Smart.map subst_cl cls in
  (ArgsScopeNoDischarge,r',n,scl,cls')

let discharge_arguments_scope (_,(req,r,n,l,_)) =
  if req == ArgsScopeNoDischarge || (isVarRef r && Lib.is_in_section r) then None
  else
    let n =
      try
        let vars = Lib.variable_section_segment_of_reference r in
        vars |> List.filter is_local_assum |> List.length
      with
        Not_found (* Not a ref defined in this section *) -> 0 in
    Some (req,r,n,l,[])

let classify_arguments_scope (req,_,_,_,_ as obj) =
  if req == ArgsScopeNoDischarge then Dispose else Substitute obj

let rebuild_arguments_scope sigma (req,r,n,l,_) =
  match req with
    | ArgsScopeNoDischarge -> assert false
    | ArgsScopeAuto ->
      let env = Global.env () in (*FIXME?*)
      let typ = EConstr.of_constr @@ fst (Typeops.type_of_global_in_context env r) in
      let scs,cls = compute_arguments_scope_full env sigma typ in
      (req,r,List.length scs,scs,cls)
    | ArgsScopeManual ->
      (* Add to the manually given scopes the one found automatically
         for the extra parameters of the section. Discard the classes
         of the manually given scopes to avoid further re-computations. *)
      let env = Global.env () in (*FIXME?*)
      let typ = EConstr.of_constr @@ fst (Typeops.type_of_global_in_context env r) in
      let l',cls = compute_arguments_scope_full env sigma typ in
      let l1 = List.firstn n l' in
      let cls1 = List.firstn n cls in
      (req,r,0,l1@l,cls1)

type arguments_scope_obj =
    arguments_scope_discharge_request * GlobRef.t *
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
    let (scl,cls,stamp) = GlobRef.Map.find r !arguments_scope in
    let cur_stamp = !scope_class_map in
    if stamp == cur_stamp then scl
    else
      (* Recent changes in the Bind Scope base, we re-compute the scopes *)
      let scl' = update_scopes cls scl in
      arguments_scope := GlobRef.Map.add r (scl',cls,cur_stamp) !arguments_scope;
      scl'
  with Not_found -> []

let declare_ref_arguments_scope sigma ref =
  let env = Global.env () in (* FIXME? *)
  let typ = EConstr.of_constr @@ fst @@ Typeops.type_of_global_in_context env ref in
  let (scs,cls as o) = compute_arguments_scope_full env sigma typ in
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
  | OpenScopeItem scope :: scopes ->
    if NotationMap.mem ntn (find_scope scope).notations then
      Some scope
    else find_default ntn scopes
  | LonelyNotationItem ntn' :: scopes ->
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

let global_reference_of_notation ~head test (ntn,(sc,c,_)) =
  match c with
  | NRef ref when test ref -> Some (ntn,sc,ref)
  | NApp (NRef ref, l) when head || List.for_all isNVar_or_NHole l && test ref ->
      Some (ntn,sc,ref)
  | _ -> None

let error_ambiguous_notation ?loc _ntn =
  user_err ?loc (str "Ambiguous notation.")

let error_notation_not_reference ?loc ntn =
  user_err ?loc
   (str "Unable to interpret " ++ quote (str ntn) ++
    str " as a reference.")

let interp_notation_as_global_reference ?loc ~head test ntn sc =
  let scopes = match sc with
  | Some sc ->
      let scope = find_scope (find_delimiters_scope sc) in
      String.Map.add sc scope String.Map.empty
  | None -> !scope_map in
  let ntns = browse_notation true ntn scopes in
  let refs = List.map (global_reference_of_notation ~head test) ntns in
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
    prlist_with_sep fnl (fun (ntn,l) ->
      let scope = find_default ntn scopes in
      prlist_with_sep fnl
        (fun (sc,r,(_,df)) ->
          hov 0 (
            pr_notation_info prglob df r ++
            (if String.equal sc default_scope then mt ()
             else (spc () ++ str ": " ++ str sc)) ++
            (if Option.equal String.equal (Some sc) scope
             then spc () ++ str "(default interpretation)" else mt ())))
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
            let { not_interp  = (_, r); not_location = (_, df) } =
              NotationMap.find ntn (find_scope default_scope).notations in
            let all' = match all with
              | (s,lonelyntn)::rest when String.equal s default_scope ->
                  (s,(df,r)::lonelyntn)::rest
              | _ ->
                  (default_scope,[df,r])::all in
            (all',ntn::knownntn)
          with Not_found -> (* e.g. if only printing *) (all,knownntn))
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
(* Synchronisation with reset *)

let freeze ~marshallable =
 (!scope_map, !scope_stack, !arguments_scope,
  !delimiters_map, !notations_key_table, !scope_class_map,
  !prim_token_interp_infos, !prim_token_uninterp_infos,
  !entry_coercion_map, !entry_has_global_map,
  !entry_has_ident_map)

let unfreeze (scm,scs,asc,dlm,fkm,clsc,ptii,ptui,coe,globs,ids) =
  scope_map := scm;
  scope_stack := scs;
  delimiters_map := dlm;
  arguments_scope := asc;
  notations_key_table := fkm;
  scope_class_map := clsc;
  prim_token_interp_infos := ptii;
  prim_token_uninterp_infos := ptui;
  entry_coercion_map := coe;
  entry_has_global_map := globs;
  entry_has_ident_map := ids

let init () =
  init_scope_map ();
  delimiters_map := String.Map.empty;
  notations_key_table := KeyMap.empty;
  scope_class_map := initial_scope_class_map;
  prim_token_interp_infos := String.Map.empty;
  prim_token_uninterp_infos := GlobRef.Map.empty

let _ =
  Summary.declare_summary "symbols"
    { Summary.freeze_function = freeze;
      Summary.unfreeze_function = unfreeze;
      Summary.init_function = init }

let with_notation_protection f x =
  let fs = freeze ~marshallable:false in
  try let a = f x in unfreeze fs; a
  with reraise ->
    let reraise = Exninfo.capture reraise in
    let () = unfreeze fs in
    Exninfo.iraise reraise
