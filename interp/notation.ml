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
open Constr
open Libnames
open Globnames
open Libobject
open Constrexpr
open Notation_term
open Glob_term
open Glob_ops
open NumTok
open Notationextern

(*i*)

let mkRef (env,sigmaref) r =
  let sigma, c = Evd.fresh_global env !sigmaref r in
  sigmaref := sigma;
  EConstr.Unsafe.to_constr c

let mkConstruct esig c = mkRef esig (ConstructRef c)
let mkInd esig i = mkRef esig (IndRef i)

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

let pr_notation (from,ntn) = qstring ntn ++ match from with InConstrEntry -> mt () | InCustomEntry s -> str " in custom " ++ str s

module NotationOrd =
  struct
    type t = notation
    let compare = Stdlib.compare
  end

module NotationSet = Set.Make(NotationOrd)
module NotationMap = CMap.Make(NotationOrd)

module SpecificNotationOrd =
  struct
    type t = specific_notation
    let compare = Stdlib.compare
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
  try
    let _ = NotationMap.find ntn !notation_level_map in
    anomaly (str "Notation " ++ pr_notation ntn ++ str " is already assigned a level.")
  with Not_found ->
  notation_level_map := NotationMap.add ntn level !notation_level_map

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
    | BigNumInterp of (?loc:Loc.t -> Z.t -> glob_constr)
    | StringInterp of (?loc:Loc.t -> string -> glob_constr)

  let interp_eq f f' = match f,f' with
    | RawNumInterp f, RawNumInterp f' -> f == f'
    | BigNumInterp f, BigNumInterp f' -> f == f'
    | StringInterp f, StringInterp f' -> f == f'
    | _ -> false

  let do_interp ?loc interp primtok =
    match primtok, interp with
    | Number n, RawNumInterp interp -> interp ?loc n
    | Number n, BigNumInterp interp ->
      (match NumTok.Signed.to_bigint n with
       | Some n -> interp ?loc n
       | None -> raise Not_found)
    | String s, StringInterp interp -> interp ?loc s
    | (Number _ | String _),
      (RawNumInterp _ | BigNumInterp _ | StringInterp _) -> raise Not_found

  type uninterpreter =
    | RawNumUninterp of (any_glob_constr -> rawnum option)
    | BigNumUninterp of (any_glob_constr -> Z.t option)
    | StringUninterp of (any_glob_constr -> string option)

  let uninterp_eq f f' = match f,f' with
    | RawNumUninterp f, RawNumUninterp f' -> f == f'
    | BigNumUninterp f, BigNumUninterp f' -> f == f'
    | StringUninterp f, StringUninterp f' -> f == f'
    | _ -> false

  let mkNumber n =
    Number (NumTok.Signed.of_bigint CDec n)

  let mkString = function
    | None -> None
    | Some s -> if Unicode.is_utf8 s then Some (String s) else None

  let do_uninterp uninterp g = match uninterp with
    | RawNumUninterp u -> Option.map (fun (s,n) -> Number (s,n)) (u g)
    | BigNumUninterp u -> Option.map mkNumber (u g)
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
(* Number notation interpretation                      *)
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

type number_ty =
  { int : int_ty;
    decimal : Names.inductive;
    hexadecimal : Names.inductive;
    number : Names.inductive }

type pos_neg_int63_ty =
  { pos_neg_int63_ty : Names.inductive }

type target_kind =
  | Int of int_ty (* Corelib.Init.Number.int + uint *)
  | UInt of int_ty (* Corelib.Init.Number.uint *)
  | Z of z_pos_ty (* Corelib.Numbers.BinNums.Z and positive *)
  | Int63 of pos_neg_int63_ty (* Corelib.Numbers.Cyclic.Int63.PrimInt63.pos_neg_int63 *)
  | Float64 (* Corelib.Floats.PrimFloat.float *)
  | Number of number_ty (* Corelib.Init.Number.number + uint + int *)

type string_target_kind =
  | ListByte
  | Byte
  | PString

type option_kind = Option | Direct
type 'target conversion_kind = 'target * option_kind

(** A postprocessing translation [to_post] can be done after execution
   of the [to_ty] interpreter. The reverse translation is performed
   before the [of_ty] uninterpreter.

   [to_post] is an array of [n] lists [l_i] of tuples [(f, t,
   args)]. When the head symbol of the translated term matches one of
   the [f] in the list [l_0] it is replaced by [t] and its arguments
   are translated acording to [args] where [ToPostCopy] means that the
   argument is kept unchanged and [ToPostAs k] means that the
   argument is recursively translated according to [l_k].
   [ToPostHole] introduces an additional implicit argument hole
   (in the reverse translation, the corresponding argument is removed).
   [ToPostCheck r] behaves as [ToPostCopy] except in the reverse
   translation which fails if the copied term is not [r].
   When [n] is null, no translation is performed. *)
type to_post_arg = ToPostCopy | ToPostAs of int | ToPostHole | ToPostCheck of Constr.t
type ('target, 'warning) prim_token_notation_obj =
  { to_kind : 'target conversion_kind;
    to_ty : GlobRef.t;
    to_post : ((GlobRef.t * GlobRef.t * to_post_arg list) list) array;
    of_kind : 'target conversion_kind;
    of_ty : GlobRef.t;
    ty_name : Libnames.qualid; (* for warnings / error messages *)
    warning : 'warning }

type number_notation_obj = (target_kind, numnot_option) prim_token_notation_obj
type string_notation_obj = (string_target_kind, unit) prim_token_notation_obj

type 'a token_kind =
| TVar of Id.t * 'a list
| TSort of Sorts.t
| TConst of Constant.t * 'a list
| TInd of inductive * 'a list
| TConstruct of constructor * 'a list
| TInt of Uint63.t
| TFloat of Float64.t
| TString of Pstring.t
| TArray of 'a array * 'a * 'a
| TOther

module TokenValue :
sig
  type t
  val kind : t -> t token_kind
  val make : Environ.env -> Evd.evar_map -> EConstr.unsafe_judgment -> t
  val repr : t -> Constr.t
end =
struct

type t = Constr.t (* Guaranteed to be in strong normal form *)

let kind c =
  let hd, args = decompose_app_list c in
  match Constr.kind hd with
  | Var id -> TVar (id, args)
  | Sort s -> TSort s
  | Const (c, _) -> TConst (c, args)
  | Ind (ind, _) -> TInd (ind, args)
  | Construct (c, _) -> TConstruct (c, args)
  | Int i -> TInt i
  | Float f -> TFloat f
  | String s -> TString s
  | Array (_, t, u, v) -> TArray (t, u, v)
  | Rel _ | Meta _ | Evar _ | Cast _ | Prod _ | Lambda _ | LetIn _ | App _
  | Proj _ | Case _ | Fix _ | CoFix _ -> TOther

let make env sigma c =
  let c' = Tacred.compute env sigma c.Environ.uj_val in
  EConstr.Unsafe.to_constr @@ c'

let repr c = c

end

module PrimTokenNotation = struct
(** * Code shared between Number notation and String notation *)
(** Reduction

    The constr [c] below isn't necessarily well-typed, since we
    built it via an [mkApp] of a conversion function on a term
    that starts with the right constructor but might be partially
    applied.

    At least [c] is known to be evar-free, since it comes from
    our own ad-hoc [constr_of_glob] or from conversions such
    as [rocqint_of_rawnum].

    It is important to fully normalize the term, *including inductive
    parameters of constructors*; see
    https://github.com/coq/coq/issues/9840 for details on what goes
    wrong if this does not happen, e.g., from using the vm rather than
    cbv.
*)

let eval_constr env sigma (c : Constr.t) =
  let c = EConstr.of_constr c in
  let sigma, t = Typing.type_of env sigma c in
  TokenValue.make env sigma { Environ.uj_val = c; Environ.uj_type = t }

let eval_constr_app env sigma c1 c2 =
  eval_constr env sigma (mkApp (c1,[| c2 |]))

exception NotAValidPrimToken

(** The uninterp function below work at the level of [glob_constr]
    which is too low for us here. So here's a crude conversion back
    to [constr] for the subset that concerns us.

    Note that if you update [constr_of_glob], you should update the
    corresponding number notation *and* string notation doc in
    doc/sphinx/user-extensions/syntax-extensions.rst that describes
    what it means for a term to be ground / to be able to be
    considered for parsing. *)

let constr_of_globref ?(allow_constant=true) env sigma = function
  | GlobRef.ConstructRef c ->
     let sigma,c = Evd.fresh_constructor_instance env sigma c in
     sigma,mkConstructU c
  | GlobRef.IndRef c ->
     let sigma,c = Evd.fresh_inductive_instance env sigma c in
     sigma,mkIndU c
  | GlobRef.ConstRef c when allow_constant || Environ.is_primitive_type env c ->
     let sigma,c = Evd.fresh_constant_instance env sigma c in
     sigma,mkConstU c
  | _ -> raise NotAValidPrimToken

(** [check_glob g c] checks that glob [g] is equal to constr [c]
    and returns [g] as a constr (with fresh universe instances)
    or raises [NotAValidPrimToken]. *)
let rec check_glob env sigma g c = match DAst.get g, Constr.kind c with
  | Glob_term.GRef (GlobRef.ConstructRef c as g, _), Constr.Construct (c', _)
       when Environ.QConstruct.equal env c c' -> constr_of_globref env sigma g
  | Glob_term.GRef (GlobRef.IndRef c as g, _), Constr.Ind (c', _)
       when Environ.QInd.equal env c c' -> constr_of_globref env sigma g
  | Glob_term.GRef (GlobRef.ConstRef c as g, _), Constr.Const (c', _)
       when Environ.QConstant.equal env c c' -> constr_of_globref env sigma g
  | Glob_term.GApp (gc, gcl), Constr.App (gc', gc'a) ->
     let sigma,c = check_glob env sigma gc gc' in
     let sigma,cl =
       try List.fold_left2_map (check_glob env) sigma gcl (Array.to_list gc'a)
       with Invalid_argument _ -> raise NotAValidPrimToken in
     sigma, mkApp (c, Array.of_list cl)
  | Glob_term.GInt i, Constr.Int i' when Uint63.equal i i' -> sigma, mkInt i
  | Glob_term.GFloat f, Constr.Float f' when Float64.equal f f' -> sigma, mkFloat f
  | Glob_term.GString s, Constr.String s' when Pstring.equal s s' -> sigma, mkString s
  | Glob_term.GArray (_,t,def,ty), Constr.Array (_,t',def',ty') ->
     let sigma,u = Evd.fresh_array_instance env sigma in
     let sigma,def = check_glob env sigma def def' in
     let sigma,t =
       try Array.fold_left2_map (check_glob env) sigma t t'
       with Invalid_argument _ -> raise NotAValidPrimToken in
     let sigma,ty = check_glob env sigma ty ty' in
     sigma, mkArray (u,t,def,ty)
  | Glob_term.GSort s, Constr.Sort s' ->
     let sigma,s = Evd.fresh_sort_in_family sigma (Glob_ops.glob_sort_family s) in
     let s = EConstr.ESorts.kind sigma s in
     if not (Sorts.equal s s') then raise NotAValidPrimToken;
     sigma,mkSort s
  | _ -> raise NotAValidPrimToken

let rec constr_of_glob to_post post env sigma g = match DAst.get g with
  | Glob_term.GRef (r, _) ->
      let o = List.find_opt (fun (_,r',_) -> Environ.QGlobRef.equal env r r') post in
      begin match o with
      | None -> constr_of_globref ~allow_constant:false env sigma r
      | Some (r, _, a) ->
         (* [g] is not a GApp so check that [post]
            does not expect any actual argument
            (i.e., [a] contains only ToPostHole since they mean "ignore arg") *)
         if List.exists ((<>) ToPostHole) a then raise NotAValidPrimToken;
         constr_of_globref env sigma r
      end
  | Glob_term.GApp (gc, gcl) ->
      let o = match DAst.get gc with
        | Glob_term.GRef (r, _) -> List.find_opt (fun (_,r',_) -> Environ.QGlobRef.equal env r r') post
        | _ -> None in
      begin match o with
      | None ->
         let sigma,c = constr_of_glob to_post post env sigma gc in
         let sigma,cl = List.fold_left_map (constr_of_glob to_post post env) sigma gcl in
         sigma,mkApp (c, Array.of_list cl)
      | Some (r, _, a) ->
         let sigma,c = constr_of_globref env sigma r in
         let rec aux sigma a gcl = match a, gcl with
           | [], [] -> sigma,[]
           | ToPostCopy :: a, gc :: gcl ->
              let sigma,c = constr_of_glob [||] [] env sigma gc in
              let sigma,cl = aux sigma a gcl in
              sigma, c :: cl
           | ToPostCheck r :: a, gc :: gcl ->
              let sigma,c = check_glob env sigma gc r in
              let sigma,cl = aux sigma a gcl in
              sigma, c :: cl
           | ToPostAs i :: a, gc :: gcl ->
              let sigma,c = constr_of_glob to_post to_post.(i) env sigma gc in
              let sigma,cl = aux sigma a gcl in
              sigma, c :: cl
           | ToPostHole :: post, _ :: gcl -> aux sigma post gcl
           | [], _ :: _ | _ :: _, [] -> raise NotAValidPrimToken
         in
         let sigma,cl = aux sigma a gcl in
         sigma,mkApp (c, Array.of_list cl)
      end
  | Glob_term.GInt i -> sigma, mkInt i
  | Glob_term.GFloat f -> sigma, mkFloat f
  | Glob_term.GString s -> sigma, mkString s
  | Glob_term.GArray (_,t,def,ty) ->
      let sigma, u' = Evd.fresh_array_instance env sigma in
      let sigma, def' = constr_of_glob to_post post env sigma def in
      let sigma, t' = Array.fold_left_map (constr_of_glob to_post post env) sigma t in
      let sigma, ty' = constr_of_glob to_post post env sigma ty in
       sigma, mkArray (u',t',def',ty')
  | Glob_term.GSort gs ->
      let sigma,c = Evd.fresh_sort_in_family sigma (Glob_ops.glob_sort_family gs) in
      let c = EConstr.ESorts.kind sigma c in
      sigma,mkSort c
  | _ ->
      raise NotAValidPrimToken

let constr_of_glob to_post env sigma (Glob_term.AnyGlobConstr g) =
  let post = match to_post with [||] -> [] | _ -> to_post.(0) in
  constr_of_glob to_post post env sigma g

let rec glob_of_constr token_kind ?loc env sigma c = match Constr.kind c with
  | App (c, ca) ->
      let c = glob_of_constr token_kind ?loc env sigma c in
      let cel = List.map (glob_of_constr token_kind ?loc env sigma) (Array.to_list ca) in
      DAst.make ?loc (Glob_term.GApp (c, cel))
  | Construct (c, _) -> DAst.make ?loc (Glob_term.GRef (GlobRef.ConstructRef c, None))
  | Const (c, _) -> DAst.make ?loc (Glob_term.GRef (GlobRef.ConstRef c, None))
  | Ind (ind, _) -> DAst.make ?loc (Glob_term.GRef (GlobRef.IndRef ind, None))
  | Var id -> DAst.make ?loc (Glob_term.GRef (GlobRef.VarRef id, None))
  | Int i -> DAst.make ?loc (Glob_term.GInt i)
  | Float f -> DAst.make ?loc (Glob_term.GFloat f)
  | String s -> DAst.make ?loc (Glob_term.GString s)
  | Array (u,t,def,ty) ->
      let def' = glob_of_constr token_kind ?loc env sigma def
      and t' = Array.map (glob_of_constr token_kind ?loc env sigma) t
      and ty' = glob_of_constr token_kind ?loc env sigma ty in
      DAst.make ?loc (Glob_term.GArray (None,t',def',ty'))
  | Sort Sorts.SProp -> DAst.make ?loc (Glob_term.GSort Glob_ops.glob_SProp_sort)
  | Sort Sorts.Prop -> DAst.make ?loc (Glob_term.GSort Glob_ops.glob_Prop_sort)
  | Sort Sorts.Set -> DAst.make ?loc (Glob_term.GSort Glob_ops.glob_Set_sort)
  | Sort (Sorts.Type _) -> DAst.make ?loc (Glob_term.GSort Glob_ops.glob_Type_sort)
  | _ -> Loc.raise ?loc (PrimTokenNotationError(token_kind,env,sigma,UnexpectedTerm c))

let mkGApp ?loc hd args = match args with
| [] -> hd
| _ :: _ -> mkGApp ?loc hd args

let rec glob_of_token token_kind ?loc env sigma c = match TokenValue.kind c with
  | TConstruct (c, l) ->
    let ce = DAst.make ?loc (Glob_term.GRef (GlobRef.ConstructRef c, None)) in
    let cel = List.map (glob_of_token token_kind ?loc env sigma) l in
    mkGApp ?loc ce cel
  | TConst (c, l) ->
    let ce = DAst.make ?loc (Glob_term.GRef (GlobRef.ConstRef c, None)) in
    let cel = List.map (glob_of_token token_kind ?loc env sigma) l in
    mkGApp ?loc ce cel
  | TInd (ind, l) ->
    let ce = DAst.make ?loc (Glob_term.GRef (GlobRef.IndRef ind, None)) in
    let cel = List.map (glob_of_token token_kind ?loc env sigma) l in
    mkGApp ?loc ce cel
  | TVar (id, l) ->
    let ce = DAst.make ?loc (Glob_term.GRef (GlobRef.VarRef id, None)) in
    let cel = List.map (glob_of_token token_kind ?loc env sigma) l in
    mkGApp ?loc ce cel
  | TInt i -> DAst.make ?loc (Glob_term.GInt i)
  | TFloat f -> DAst.make ?loc (Glob_term.GFloat f)
  | TString s -> DAst.make ?loc (Glob_term.GString s)
  | TArray (t,def,ty) ->
    let def' = glob_of_token token_kind ?loc env sigma def
    and t' = Array.map (glob_of_token token_kind ?loc env sigma) t
    and ty' = glob_of_token token_kind ?loc env sigma ty in
    DAst.make ?loc (Glob_term.GArray (None,t',def',ty'))
  | TSort Sorts.SProp -> DAst.make ?loc (Glob_term.GSort Glob_ops.glob_SProp_sort)
  | TSort Sorts.Prop -> DAst.make ?loc (Glob_term.GSort Glob_ops.glob_Prop_sort)
  | TSort Sorts.Set -> DAst.make ?loc (Glob_term.GSort Glob_ops.glob_Set_sort)
  | TSort (Sorts.Type _ | Sorts.QSort _) -> DAst.make ?loc (Glob_term.GSort Glob_ops.glob_Type_sort)
  | TOther ->
    let c = TokenValue.repr c in
    Loc.raise ?loc (PrimTokenNotationError(token_kind,env,sigma,UnexpectedTerm c))

let no_such_prim_token uninterpreted_token_kind ?loc ty =
  CErrors.user_err ?loc
   (str ("Cannot interpret this "^uninterpreted_token_kind^" as a value of type ") ++
    pr_qualid ty)

let rec postprocess env token_kind ?loc ty to_post post g =
  let g', gl = match DAst.get g with Glob_term.GApp (g, gl) -> g, gl | _ -> g, [] in
  let o =
    match DAst.get g' with
    | Glob_term.GRef (r, None) ->
       List.find_opt (fun (r',_,_) -> Environ.QGlobRef.equal env r r') post
    | _ -> None in
  match o with None -> g | Some (_, r, a) ->
  let rec f n a gl = match a, gl with
    | [], [] -> []
    | ToPostHole :: a, gl ->
       let e = GImplicitArg (r, (n, None), true) in
       let h = DAst.make ?loc (Glob_term.GHole e) in
       h :: f (n+1) a gl
    | (ToPostCopy | ToPostCheck _) :: a, g :: gl -> g :: f (n+1) a gl
    | ToPostAs c :: a, g :: gl ->
       postprocess env token_kind ?loc ty to_post to_post.(c) g :: f (n+1) a gl
    | [], _::_ | _::_, [] ->
       no_such_prim_token token_kind ?loc ty
  in
  let gl = f 1 a gl in
  let g = DAst.make ?loc (Glob_term.GRef (r, None)) in
  DAst.make ?loc (Glob_term.GApp (g, gl))

let glob_of_constr token_kind ty ?loc env sigma to_post c =
  let g = glob_of_constr token_kind ?loc env sigma c in
  match to_post with [||] -> g | _ ->
    postprocess env token_kind ?loc ty to_post to_post.(0) g

let glob_of_token token_kind ty ?loc env sigma to_post c =
  let g = glob_of_token token_kind ?loc env sigma c in
  match to_post with [||] -> g | _ ->
    postprocess env token_kind ?loc ty to_post to_post.(0) g

let interp_option uninterpreted_token_kind token_kind ty ?loc env sigma to_post c =
  match TokenValue.kind c with
  | TConstruct (_Some, [_; c]) -> glob_of_token token_kind ty ?loc env sigma to_post c
  | TConstruct (_None, [_]) -> no_such_prim_token uninterpreted_token_kind ?loc ty
  | x ->
    let c = TokenValue.repr c in
    Loc.raise ?loc (PrimTokenNotationError(token_kind,env,sigma,UnexpectedNonOptionTerm c))

let uninterp_option c =
  match TokenValue.kind c with
  | TConstruct (_Some, [_; x]) -> x
  | _ -> raise NotAValidPrimToken

let uninterp to_raw o n =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let sigma,of_ty = Evd.fresh_global env sigma o.of_ty in
  let of_ty = EConstr.Unsafe.to_constr of_ty in
  try
    let sigma,n = constr_of_glob o.to_post env sigma n in
    let c = eval_constr_app env sigma of_ty n in
    let c = if snd o.of_kind == Direct then c else uninterp_option c in
    Some (to_raw (fst o.of_kind, c))
  with
  | Type_errors.TypeError _ | Pretype_errors.PretypeError _ -> None (* cf. eval_constr_app *)
  | NotAValidPrimToken -> None (* all other functions except NumTok.Signed.of_bigint *)

end

let z_two = Z.of_int 2

(** Conversion from bigint to int63 *)
let int63_of_pos_bigint i = Uint63.of_int64 (Z.to_int64 i)

module Numbers = struct
(** * Number notation *)
open PrimTokenNotation

let warn_large_num =
  CWarnings.create ~name:"large-number" ~category:CWarnings.CoreCategories.numbers
    (fun ty ->
      strbrk "Stack overflow or segmentation fault happens when " ++
      strbrk "working with large numbers in " ++ pr_qualid ty ++
      strbrk " (threshold may vary depending" ++
      strbrk " on your system limits and on the command executed).")

let warn_abstract_large_num =
  CWarnings.create ~name:"abstract-large-number" ~category:CWarnings.CoreCategories.numbers
    (fun (ty,f) ->
      strbrk "To avoid stack overflow, large numbers in " ++
      pr_qualid ty ++ strbrk " are interpreted as applications of " ++
      Nametab.pr_global_env (Termops.vars_of_env (Global.env ())) f ++ strbrk ".")

(***********************************************************************)

(** ** Conversion between Rocq [Decimal.int] and internal raw string *)

(** Decimal.Nil has index 1, then Decimal.D0 has index 2 .. Decimal.D9 is 11 *)

let digit_of_char c =
  assert ('0' <= c && c <= '9' || 'a' <= c && c <= 'f');
  if c <= '9' then Char.code c - Char.code '0' + 2
  else Char.code c - Char.code 'a' + 12

let char_of_digit n =
  assert (2<=n && n<=17);
  if n <= 11 then Char.chr (n-2 + Char.code '0')
  else Char.chr (n-12 + Char.code 'a')

let rocquint_of_rawnum esig inds c n =
  let uint = match c with CDec -> inds.dec_uint | CHex -> inds.hex_uint in
  let nil = mkConstruct esig (uint,1) in
  match n with None -> nil | Some n ->
  let str = NumTok.UnsignedNat.to_string n in
  let str = match c with
    | CDec -> str
    | CHex -> String.sub str 2 (String.length str - 2) in  (* cut "0x" *)
  let rec do_chars s i acc =
    if i < 0 then acc
    else
      let dg = mkConstruct esig (uint, digit_of_char s.[i]) in
      do_chars s (i-1) (mkApp(dg,[|acc|]))
  in
  do_chars str (String.length str - 1) nil

let rocqint_of_rawnum esig inds c (sign,n) =
  let ind = match c with CDec -> inds.dec_int | CHex -> inds.hex_int in
  let uint = rocquint_of_rawnum esig inds c (Some n) in
  let pos_neg = match sign with SPlus -> 1 | SMinus -> 2 in
  mkApp (mkConstruct esig (ind, pos_neg), [|uint|])

let rocqnumber_of_rawnum esig inds c n =
  let ind = match c with CDec -> inds.decimal | CHex -> inds.hexadecimal in
  let i, f, e = NumTok.Signed.to_int_frac_and_exponent n in
  let i = rocqint_of_rawnum esig inds.int c i in
  let f = rocquint_of_rawnum esig inds.int c f in
  match e with
  | None -> mkApp (mkConstruct esig (ind, 1), [|i; f|])  (* (D|Hexad)ecimal *)
  | Some e ->
    let e = rocqint_of_rawnum esig inds.int CDec e in
    mkApp (mkConstruct esig (ind, 2), [|i; f; e|])  (* (D|Hexad)ecimalExp *)

let mkDecHex esig ind c n = match c with
  | CDec -> mkApp (mkConstruct esig (ind, 1), [|n|])  (* (UInt|Int|)Decimal *)
  | CHex -> mkApp (mkConstruct esig (ind, 2), [|n|])  (* (UInt|Int|)Hexadecimal *)

let rocqnumber_of_rawnum esig inds n =
  let c = NumTok.Signed.classify n in
  let n = rocqnumber_of_rawnum esig inds c n in
  mkDecHex esig inds.number c n

let rocquint_of_rawnum esig inds n =
  let c = NumTok.UnsignedNat.classify n in
  let n = rocquint_of_rawnum esig inds c (Some n) in
  mkDecHex esig inds.uint c n

let rocqint_of_rawnum esig inds n =
  let c = NumTok.SignedNat.classify n in
  let n = rocqint_of_rawnum esig inds c n in
  mkDecHex esig inds.int c n

let rawnum_of_rocquint cl c =
  let rec of_uint_loop c buf =
    match TokenValue.kind c with
    | TConstruct ((_, 1), _) (* Nil *) -> ()
    | TConstruct ((_, n), [a]) (* D0 to Df *) ->
      let () = Buffer.add_char buf (char_of_digit n) in
      of_uint_loop a buf
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

let rawnum_of_rocqint cl c =
  match TokenValue.kind c with
  | TConstruct ((_, 1), [c']) (* Pos *) -> (SPlus, rawnum_of_rocquint cl c')
  | TConstruct ((_, 2), [c']) (* Neg *) -> (SMinus, rawnum_of_rocquint cl c')
  | _ -> raise NotAValidPrimToken

let rawnum_of_rocqnumber cl c =
  let of_ife i f e =
    let n = rawnum_of_rocqint cl i in
    let f = try Some (rawnum_of_rocquint cl f) with NotAValidPrimToken -> None in
    let e = match e with None -> None | Some e -> Some (rawnum_of_rocqint CDec e) in
    NumTok.Signed.of_int_frac_and_exponent n f e in
  match TokenValue.kind c with
  | TConstruct (_, [i; f]) -> of_ife i f None
  | TConstruct (_, [i; f; e]) -> of_ife i f (Some e)
  | _ -> raise NotAValidPrimToken

let destDecHex c = match TokenValue.kind c with
  | TConstruct ((_, 1), [c']) (* (UInt|Int|)Decimal *) -> CDec, c'
  | TConstruct ((_, 2), [c']) (* (UInt|Int|)Hexadecimal *) -> CHex, c'
  | _ -> raise NotAValidPrimToken

let rawnum_of_rocqnumber c =
  let cl, c = destDecHex c in
  rawnum_of_rocqnumber cl c

let rawnum_of_rocquint c =
  let cl, c = destDecHex c in
  rawnum_of_rocquint cl c

let rawnum_of_rocqint c =
  let cl, c = destDecHex c in
  rawnum_of_rocqint cl c

(***********************************************************************)

(** ** Conversion between Rocq [Z] and internal bigint *)

(** First, [positive] from/to bigint *)

let rec pos_of_bigint esig posty n =
  match Z.div_rem n z_two with
  | (q, rem) when rem = Z.zero ->
      let c = mkConstruct esig (posty, 2) in (* xO *)
      mkApp (c, [| pos_of_bigint esig posty q |])
  | (q, _) when not (Z.equal q Z.zero) ->
      let c = mkConstruct esig (posty, 1) in (* xI *)
      mkApp (c, [| pos_of_bigint esig posty q |])
  | (q, _) ->
      mkConstruct esig (posty, 3) (* xH *)

let rec bigint_of_pos c = match TokenValue.kind c with
| TConstruct ((_, 3), []) -> (* xH *) Z.one
| TConstruct ((_, 1), [d]) -> (* xI *) Z.add Z.one (Z.mul z_two (bigint_of_pos d))
| TConstruct ((_, 2), [d]) -> (* xO *) Z.mul z_two (bigint_of_pos d)
| x -> raise NotAValidPrimToken

(** Now, [Z] from/to bigint *)

let z_of_bigint esig { z_ty; pos_ty } n =
  if Z.(equal n zero) then
    mkConstruct esig (z_ty, 1) (* Z0 *)
  else
    let (s, n) =
      if Z.(leq zero n) then (2, n) (* Zpos *)
      else (3, Z.neg n) (* Zneg *)
    in
    let c = mkConstruct esig (z_ty, s) in
    mkApp (c, [| pos_of_bigint esig pos_ty n |])

let bigint_of_z z = match TokenValue.kind z with
| TConstruct ((_, 1), []) -> (* Z0 *) Z.zero
| TConstruct ((_, 2), [d]) -> (* Zpos *) bigint_of_pos d
| TConstruct ((_, 3), [d]) -> (* Zneg *) Z.neg (bigint_of_pos d)
| _ -> raise NotAValidPrimToken

(** Now, [Int63] from/to bigint *)

let int63_of_pos_bigint ?loc n =
  let i = int63_of_pos_bigint n in
  mkInt i

let error_overflow ?loc n =
  CErrors.user_err ?loc Pp.(str "Overflow in int63 literal: " ++ str (Z.to_string n)
    ++ str ".")

let rocqpos_neg_int63_of_bigint ?loc esig ind (sign,n) =
  let uint = int63_of_pos_bigint ?loc n in
  let pos_neg = match sign with SPlus -> 1 | SMinus -> 2 in
  mkApp (mkConstruct esig (ind, pos_neg), [|uint|])

let interp_int63 ?loc esig ind n =
  let sign = if Z.(compare n zero >= 0) then SPlus else SMinus in
  let an = Z.abs n in
  if Z.(lt an (pow z_two 63))
  then rocqpos_neg_int63_of_bigint ?loc esig ind (sign,an)
  else error_overflow ?loc n

let warn_inexact_float =
  CWarnings.create ~name:"inexact-float" ~category:CWarnings.CoreCategories.parsing
    (fun (sn, f) ->
      Pp.strbrk
        (Printf.sprintf
           "The constant %s is not a binary64 floating-point value. \
            A closest value %s will be used and unambiguously printed %s."
           sn (Float64.to_hex_string f) (Float64.to_string f)))

let interp_float64 ?loc n =
  let sn = NumTok.Signed.to_string n in
  let f = Float64.of_string sn in
  (* return true when f is not exactly equal to n,
     this is only used to decide whether or not to display a warning
     and does not play any actual role in the parsing *)
  let inexact () = match Float64.classify f with
    | Float64.(PInf | NInf | NaN) -> true
    | Float64.(PZero | NZero) -> not (NumTok.Signed.is_zero n)
    | Float64.(PNormal | NNormal | PSubn | NSubn) ->
       let m, e =
         let (_, i), f, e = NumTok.Signed.to_int_frac_and_exponent n in
         let i = NumTok.UnsignedNat.to_string i in
         let f = match f with
           | None -> "" | Some f -> NumTok.UnsignedNat.to_string f in
         let e = match e with
           | None -> "0" | Some e -> NumTok.SignedNat.to_string e in
         Z.of_string (i ^ f),
         (try int_of_string e with Failure _ -> 0) - String.length f in
       let m', e' =
         let m', e' = Float64.frshiftexp f in
         let m' = Float64.normfr_mantissa m' in
         let e' = Uint63.to_int_min e' 4096 - Float64.eshift - 53 in
         Z.of_string (Uint63.to_string m'),
         e' in
       let c2, c5 = Z.(of_int 2, of_int 5) in
       (* check m*5^e <> m'*2^e' *)
       let check m e m' e' =
         not (Z.(equal (mul m (pow c5 e)) (mul m' (pow c2 e')))) in
       (* check m*5^e*2^e' <> m' *)
       let check' m e e' m' =
         not (Z.(equal (mul (mul m (pow c5 e)) (pow c2 e')) m')) in
       (* we now have to check m*10^e <> m'*2^e' *)
       if e >= 0 then
         if e <= e' then check m e m' (e' - e)
         else check' m e (e - e') m'
       else  (* e < 0 *)
         if e' <= e then check m' (-e) m (e - e')
         else check' m' (-e) (e' - e) m in
  if NumTok.(Signed.classify n = CDec) && inexact () then
    warn_inexact_float ?loc (sn, f);
  mkFloat f

let bigint_of_int63 c = match TokenValue.kind c with
| TInt i -> Z.of_int64 (Uint63.to_int64 i)
| _ -> raise NotAValidPrimToken

let bigint_of_rocqpos_neg_int63 c = match TokenValue.kind c with
| TConstruct ((_, 1), [c']) (* Pos *) -> bigint_of_int63 c'
| TConstruct ((_, 2), [c']) (* Neg *) -> Z.neg (bigint_of_int63 c')
| _ -> raise NotAValidPrimToken

let { Goptions.get = get_printing_float } =
  Goptions.declare_bool_option_and_ref
    ~key:["Printing";"Float"]
    ~value:true
    ()

let uninterp_float64 c = match TokenValue.kind c with
| TFloat f when not (Float64.is_infinity f || Float64.is_neg_infinity f
                    || Float64.is_nan f) && get_printing_float () ->
  NumTok.Signed.of_string (Float64.to_string f)
| _ -> raise NotAValidPrimToken

let interp o ?loc n =
  begin match o.warning, n with
  | Warning threshold, n when NumTok.Signed.is_bigger_int_than n threshold ->
     warn_large_num o.ty_name
  | _ -> ()
  end;
  let env = Global.env () in
  let sigma = ref (Evd.from_env env) in
  let esig = env, sigma in
  let c = match fst o.to_kind, NumTok.Signed.to_int n with
    | Int int_ty, Some n ->
       rocqint_of_rawnum esig int_ty n
    | UInt int_ty, Some (SPlus, n) ->
       rocquint_of_rawnum esig int_ty n
    | Z z_pos_ty, Some n ->
       z_of_bigint esig z_pos_ty (NumTok.SignedNat.to_bigint n)
    | Int63 pos_neg_int63_ty, Some n ->
       interp_int63 ?loc esig pos_neg_int63_ty.pos_neg_int63_ty (NumTok.SignedNat.to_bigint n)
    | (Int _ | UInt _ | Z _ | Int63 _), _ ->
       no_such_prim_token "number" ?loc o.ty_name
    | Float64, _ -> interp_float64 ?loc n
    | Number number_ty, _ -> rocqnumber_of_rawnum esig number_ty n
  in
  let sigma = !sigma in
  let sigma,to_ty = Evd.fresh_global env sigma o.to_ty in
  let to_ty = EConstr.Unsafe.to_constr to_ty in
  match o.warning, snd o.to_kind with
  | Abstract threshold, Direct when NumTok.Signed.is_bigger_int_than n threshold ->
     warn_abstract_large_num (o.ty_name,o.to_ty);
     assert (Array.length o.to_post = 0);
     glob_of_constr "number" o.ty_name ?loc env sigma o.to_post (mkApp (to_ty,[|c|]))
  | _ ->
     let res = eval_constr_app env sigma to_ty c in
     match snd o.to_kind with
     | Direct -> glob_of_token "number" o.ty_name ?loc env sigma o.to_post res
     | Option -> interp_option "number" "number" o.ty_name ?loc env sigma o.to_post res

let uninterp o n =
  PrimTokenNotation.uninterp
    begin function
      | (Int _, c) -> NumTok.Signed.of_int (rawnum_of_rocqint c)
      | (UInt _, c) -> NumTok.Signed.of_nat (rawnum_of_rocquint c)
      | (Z _, c) -> NumTok.Signed.of_bigint CDec (bigint_of_z c)
      | (Int63 _, c) -> NumTok.Signed.of_bigint CDec (bigint_of_rocqpos_neg_int63 c)
      | (Float64, c) -> uninterp_float64 c
      | (Number _, c) -> rawnum_of_rocqnumber c
    end o n
end

module Strings = struct
(** * String notation *)
open PrimTokenNotation

let qualid_of_ref n =
  n |> Rocqlib.lib_ref |> Nametab.shortest_qualid_of_global Id.Set.empty

let q_list () = qualid_of_ref "core.list.type"
let q_byte () = qualid_of_ref "core.byte.type"

let unsafe_locate_ind q =
  match Nametab.locate q with
  | GlobRef.IndRef i -> i
  | _ -> raise Not_found

let locate_list () = unsafe_locate_ind (q_list ())
let locate_byte () = unsafe_locate_ind (q_byte ())

(***********************************************************************)

(** ** Conversion between Rocq [list Byte.byte] and internal raw string *)

let rocqbyte_of_char_code esig byte c =
  mkConstruct esig (byte, 1 + c)

let rocqbyte_of_string ?loc esig byte s =
  let p =
    if Int.equal (String.length s) 1 then int_of_char s.[0]
    else
      let n =
        if Int.equal (String.length s) 3 && is_digit s.[0] && is_digit s.[1] && is_digit s.[2]
        then int_of_string s else 256 in
      if n < 256 then n else
       user_err ?loc
         (str "Expects a single character or a three-digit ASCII code.") in
  rocqbyte_of_char_code esig byte p

let rocqbyte_of_char esig byte c = rocqbyte_of_char_code esig byte (Char.code c)

let pstring_of_string ?loc s =
  match Pstring.of_string s with
  | Some s -> Constr.mkString s
  | None -> user_err ?loc (str "String literal would be too large on a 32-bits system.")

let make_ascii_string n =
  if n>=32 && n<=126 then String.make 1 (char_of_int n)
  else Printf.sprintf "%03d" n

let char_code_of_rocqbyte c = match TokenValue.kind c with
| TConstruct ((_,c), []) -> c - 1
| _ -> raise NotAValidPrimToken

let string_of_rocqbyte c = make_ascii_string (char_code_of_rocqbyte c)

let string_of_pstring c =
  match TokenValue.kind c with
  | TString s -> Pstring.to_string s
  | _ -> raise NotAValidPrimToken

let rocqlist_byte_of_string esig byte_ty list_ty str =
  let cbyte = mkInd esig byte_ty in
  let nil = mkApp (mkConstruct esig (list_ty, 1), [|cbyte|]) in
  let cons x xs = mkApp (mkConstruct esig (list_ty, 2), [|cbyte; x; xs|]) in
  let rec do_chars s i acc =
    if i < 0 then acc
    else
      let b = rocqbyte_of_char esig byte_ty s.[i] in
      do_chars s (i-1) (cons b acc)
  in
  do_chars str (String.length str - 1) nil

(* N.B. We rely on the fact that [nil] is the first constructor and [cons] is the second constructor, for [list] *)
let string_of_rocqlist_byte c =
  let rec of_rocqlist_byte_loop c buf =
    match TokenValue.kind c with
    | TConstruct (_nil, [_ty]) -> ()
    | TConstruct (_cons, [_ty;b;c]) ->
      let () = Buffer.add_char buf (Char.chr (char_code_of_rocqbyte b)) in
      of_rocqlist_byte_loop c buf
    | _ -> raise NotAValidPrimToken
  in
  let buf = Buffer.create 64 in
  let () = of_rocqlist_byte_loop c buf in
  Buffer.contents buf

let interp o ?loc n =
  let byte_ty = locate_byte () in
  let list_ty = locate_list () in
  let env = Global.env () in
  let sigma = ref (Evd.from_env env) in
  let esig = env, sigma in
  let c = match fst o.to_kind with
    | ListByte -> rocqlist_byte_of_string esig byte_ty list_ty n
    | Byte -> rocqbyte_of_string ?loc esig byte_ty n
    | PString -> pstring_of_string ?loc n
  in
  let sigma = !sigma in
  let sigma,to_ty = Evd.fresh_global env sigma o.to_ty in
  let to_ty = EConstr.Unsafe.to_constr to_ty in
  let res = eval_constr_app env sigma to_ty c in
  match snd o.to_kind with
  | Direct -> glob_of_token "string" o.ty_name ?loc env sigma o.to_post res
  | Option -> interp_option "string" "string" o.ty_name ?loc env sigma o.to_post res

let uninterp o n =
  PrimTokenNotation.uninterp
    begin function
      | (ListByte, c) -> string_of_rocqlist_byte c
      | (Byte, c) -> string_of_rocqbyte c
      | (PString, c) -> string_of_pstring c
    end o n
end

(* A [prim_token_infos], which is synchronized with the document
   state, either contains a unique id pointing to an unsynchronized
   prim token function, or a number notation object describing how to
   interpret and uninterpret.  We provide [prim_token_infos] because
   we expect plugins to provide their own interpretation functions,
   rather than going through number notations, which are available as
   a vernacular. *)

type prim_token_interp_info =
    Uid of prim_token_uid
  | NumberNotation of number_notation_obj
  | StringNotation of string_notation_obj

type prim_token_infos = {
  pt_local : bool; (** Is this interpretation local? *)
  pt_scope : scope_name; (** Concerned scope *)
  pt_interp_info : prim_token_interp_info; (** Unique id "pointing" to (un)interp functions, OR a number notation object describing (un)interp functions *)
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
      user_err
       (str "Unique identifier " ++ str uid ++
        str " already used to register a number or string (un)interpreter.")

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

let cache_prim_token_interpretation infos =
  let ptii = infos.pt_interp_info in
  let sc = infos.pt_scope in
  check_scope ~tolerant:true sc;
  prim_token_interp_infos :=
    String.Map.add sc (infos.pt_required,ptii) !prim_token_interp_infos;
  let add_uninterp r =
    let l = try GlobRef.Map.find r !prim_token_uninterp_infos with Not_found -> [] in
    prim_token_uninterp_infos :=
      GlobRef.Map.add r ((sc,(ptii,infos.pt_in_match)) :: l)
        !prim_token_uninterp_infos in
  List.iter add_uninterp infos.pt_refs

let subst_prim_token_interpretation (subs,infos) =
  { infos with
    pt_refs = List.map (subst_global_reference subs) infos.pt_refs }

let classify_prim_token_interpretation infos =
    if infos.pt_local then Dispose else Substitute

let open_prim_token_interpretation i o =
  if Int.equal i 1 then cache_prim_token_interpretation o

let inPrimTokenInterp : prim_token_infos -> obj =
  declare_object {(default_object "PRIM-TOKEN-INTERP") with
     open_function  = simple_open ~cat:notation_cat open_prim_token_interpretation;
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
  let interp = match info with
    | Uid uid -> Hashtbl.find prim_token_interpreters uid
    | NumberNotation o -> InnerPrimToken.RawNumInterp (Numbers.interp o)
    | StringNotation o -> InnerPrimToken.StringInterp (Strings.interp o)
  in
  let pat = InnerPrimToken.do_interp ?loc interp p in
  check_allowed pat;
  pat

let interp_prim_token_gen ?loc g p local_scopes =
  let scopes = make_current_scopes local_scopes in
  let p_as_ntn = try notation_of_prim_token p with Not_found -> InConstrEntry,"" in
  try
    let pat, sc = find_interpretation p_as_ntn (find_prim_token ?loc g p) scopes in
    pat, sc
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

let warn_deprecated_notation =
  Deprecation.create_warning ~object_name:"Notation" ~warning_name_if_no_since:"deprecated-notation"
    pr_notation

let interp_notation ?loc ntn local_scopes =
  let scopes = make_current_scopes local_scopes in
  try
    let (n,sc) = find_interpretation ntn (find_notation ntn) scopes in
    Option.iter (fun d -> Option.iter (fun d -> warn_deprecated_notation ?loc (ntn,d)) d.UserWarn.depr) n.not_user_warns;
    n.not_interp, (n.not_location, sc)
  with Not_found as exn ->
    let _, info = Exninfo.capture exn in
    user_err ?loc ~info
      (str "Unknown interpretation for notation " ++ pr_notation ntn ++ str ".")

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
    try let _ = Nametab.path_of_abbreviation kn in false with Not_found -> true

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
   let compare = Stdlib.compare
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

let entry_has_global_map = ref String.Map.empty

let declare_custom_entry_has_global s n =
  try
    let p = String.Map.find s !entry_has_global_map in
    user_err (str "Custom entry " ++ str s ++
              str " has already a rule for global references at level " ++ int p ++ str ".")
  with Not_found ->
    entry_has_global_map := String.Map.add s n !entry_has_global_map

let entry_has_global { notation_subentry = entry; notation_relative_level = n } =
  match entry with
  | InConstrEntry -> true
  | InCustomEntry s ->
     try entry_relative_level_le (String.Map.find s !entry_has_global_map) n with Not_found -> false

let entry_has_ident_map = ref String.Map.empty

let declare_custom_entry_has_ident s n =
  try
    let p = String.Map.find s !entry_has_ident_map in
    user_err (str "Custom entry " ++ str s ++
              str " has already a rule for global references at level " ++ int p ++ str ".")
  with Not_found ->
    entry_has_ident_map := String.Map.add s n !entry_has_ident_map

let entry_has_ident { notation_subentry = entry; notation_relative_level = n } =
  match entry with
  | InConstrEntry -> true
  | InCustomEntry s ->
     try entry_relative_level_le (String.Map.find s !entry_has_ident_map) n with Not_found -> false

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
  | IsEntryGlobal of string * int
  | IsEntryIdent of string * int

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
     | Some pat -> remove_uninterpretation (NotationRule (scopt,ntn)) pat
     | None -> ()
     end;
     declare_uninterpretation (NotationRule (scopt,ntn)) pat
  end

let availability_of_prim_token n printer_scope local_scopes =
  let f scope =
    try
      let uid = snd (String.Map.find scope !prim_token_interp_infos) in
      let open InnerPrimToken in
      match n, uid with
      | Constrexpr.Number _, NumberNotation _ -> true
      | _, NumberNotation _ -> false
      | String _, StringNotation _ -> true
      | _, StringNotation _ -> false
      | _, Uid uid ->
        let interp = Hashtbl.find prim_token_interpreters uid in
        match n, interp with
        | Constrexpr.Number _, (RawNumInterp _ | BigNumInterp _) -> true
        | String _, StringInterp _ -> true
        | _ -> false
    with Not_found -> false
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

let uninterp_prim_token c local_scopes =
  match glob_prim_constr_key c with
  | None -> raise Notation_ops.No_match
  | Some r ->
     let uninterp (sc,(info,_)) =
       try
         let uninterp = match info with
           | Uid uid -> Hashtbl.find prim_token_uninterpreters uid
           | NumberNotation o -> InnerPrimToken.RawNumUninterp (Numbers.uninterp o)
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
      let c1 = EConstr.of_constr @@ term_of_fconstr c1 in
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

let arguments_scope = ref GlobRef.Map.empty

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
  arguments_scope := GlobRef.Map.add r (scl,cls,initial_stamp) !arguments_scope

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
  if req == ArgsScopeNoDischarge || (isVarRef r && Lib.is_in_section r) then None
  else
    let n =
      try
        Array.length (Lib.section_instance r)
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

let is_local local ref = local || isVarRef ref && Lib.is_in_section ref

let declare_arguments_scope_gen req r (scl,cls) =
  Lib.add_leaf (inArgumentsScope (req,r,scl,cls,!scope_class_map))

let declare_arguments_scope local r scl =
  let req = if is_local local r then ArgsScopeNoDischarge else ArgsScopeManual in
  (* We empty the list of argument classes to disable further scope
     re-computations and keep these manually given scopes. *)
  declare_arguments_scope_gen req r (scl,[])

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
      let scope = find_scope (find_delimiters_scope sc) in
      String.Map.add sc scope String.Map.empty
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

let locate_notation prglob ntn scope =
  let ntns = factorize_entries (browse_notation false ntn !scope_map) in
  let scopes = Option.fold_right push_scope scope !scope_stack in
  match ntns with
  | [] -> str "Unknown notation"
  | _ ->
    prlist_with_sep fnl (fun (ntn,l) ->
      let scope = find_default ntn scopes in
      prlist_with_sep fnl
        (fun (sc,(on_parsing,on_printing,{ not_interp  = (_, r); not_location = (_, df) })) ->
          hov 0 (
            str "Notation" ++ brk (1,2) ++
            Notation_ops.pr_notation_info prglob df r ++
            (if String.equal sc default_scope then mt ()
             else (brk (1,2) ++ str ": " ++ str sc)) ++
            (if Option.equal String.equal (Some sc) scope
             then brk (1,2) ++ str "(default interpretation)" else mt ()) ++
            pr_non_empty (brk (1,2)) (pr_notation_status on_parsing on_printing)))
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
  List.exists (notation_entry_eq notation_entry) notation_entry_pattern

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
    let test sp a =
      let res = match_notation_interpretation ntn_pattern.interpretation_pattern a in
      let res' = match qid with
        | Some qid -> Libnames.is_qualid_suffix_of_full_path qid sp
        | None -> true in
      let res'' = res && res' in
      if res'' then found := (Inr sp, a) :: !found; res'' in
    Abbreviation.toggle_abbreviations ~on ~use:ntn_pattern.use_pattern test
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
              hov 0 (str "Notation " ++ pr_notation_data prglob (Some true,Some true,data) ++
              (match entry with InCustomEntry s -> str " (in custom " ++ str s ++ str ")" | _ -> mt ()) ++
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
  prim_token_uninterp_infos := GlobRef.Map.empty

let _ =
  Summary.declare_summary "symbols"
    { stage = Summary.Stage.Interp;
      Summary.freeze_function = freeze;
      Summary.unfreeze_function = unfreeze;
      Summary.init_function = init }

let with_notation_protection f x =
  let fs = freeze () in
  try let a = with_notation_uninterpretation_protection f x in unfreeze fs; a
  with reraise ->
    let reraise = Exninfo.capture reraise in
    let () = unfreeze fs in
    Exninfo.iraise reraise
