(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open CErrors
open Util
open Pp
open Names
open Constr
open Libnames
open Constrexpr
open Glob_term
open Glob_ops
open NumTok

let mkRef (env,sigmaref) r =
  let sigma, c = Evd.fresh_global env !sigmaref r in
  sigmaref := sigma;
  EConstr.Unsafe.to_constr c

let mkConstruct esig c = mkRef esig (ConstructRef c)
let mkInd esig i = mkRef esig (IndRef i)

(**********************************************************************)
(* Interpreting numbers (not in summary because functional objects)   *)

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
   https://github.com/rocq-prover/rocq/issues/8401 for details of what goes
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

type option_kind = Direct | Option | Error
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
type to_post_arg = ToPostCopy | ToPostAs of int | ToPostHole of Id.t | ToPostCheck of Constr.t
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
  | Proj _ | Case _ | Fix _ | CoFix _ | PBlock _ | PUnblock _ | PRun _ -> TOther

let make env sigma c =
  let flags = Environ.typing_flags env in
  if flags.enable_VM then
    let flags = Vnorm.{ vm_normalize_params = true } in
    let c' = Vnorm.cbv_vm ~flags env sigma c.Environ.uj_val c.Environ.uj_type in
    EConstr.Unsafe.to_constr @@ c'
  else
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
    https://github.com/rocq-prover/rocq/issues/9840 for details on what goes
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

let constr_of_globref ?(allow_constant=true) env sigma =
  let open EConstr in
  function
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
let rec check_glob env sigma g c =
  let open EConstr in
  match DAst.get g, Constr.kind c with
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
     let sigma,s = Glob_ops.fresh_glob_sort_in_quality sigma s in
     let s' = ESorts.make s' in
     if not (ESorts.equal sigma s s') then raise NotAValidPrimToken;
     sigma,mkSort s
  | _ -> raise NotAValidPrimToken

let rec constr_of_glob to_post post env sigma g =
  let open EConstr in
  match DAst.get g with
  | Glob_term.GRef (r, _) ->
      let o = List.find_opt (fun (_,r',_) -> Environ.QGlobRef.equal env r r') post in
      begin match o with
      | None -> constr_of_globref ~allow_constant:false env sigma r
      | Some (r, _, a) ->
         (* [g] is not a GApp so check that [post]
            does not expect any actual argument
            (i.e., [a] contains only ToPostHole since they mean "ignore arg") *)
         if List.exists (function ToPostHole _ -> false | _ -> true) a then raise NotAValidPrimToken;
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
           | ToPostHole _ :: post, _ :: gcl -> aux sigma post gcl
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
      let sigma,c = Glob_ops.fresh_glob_sort_in_quality sigma gs in
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
  | TSort (Sorts.Type _ | Sorts.VSort _) -> DAst.make ?loc (Glob_term.GSort Glob_ops.glob_Type_sort)
  | TSort (Sorts.GSort (q, _)) ->
    let q = GQuality (QGlobal q) in
    DAst.make ?loc (Glob_term.GSort (Some q, Glob_ops.glob_rigid_univ))
  | TOther ->
    let c = TokenValue.repr c in
    Loc.raise ?loc (PrimTokenNotationError(token_kind,env,sigma,UnexpectedTerm c))

let no_such_prim_token uninterpreted_token_kind ?loc ?errmsg ty =
  CErrors.user_err ?loc
   (str ("Cannot interpret this "^uninterpreted_token_kind^" as a value of type ") ++
    pr_qualid ty ++
    pr_opt (fun errmsg -> surround errmsg) errmsg)

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
    | ToPostHole id :: a, gl ->
       let e = GImplicitArg (r, (n, id), true) in
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

let interp_error uninterpreted_token_kind token_kind ty ?loc env sigma to_post c =
  match TokenValue.kind c with
  | TConstruct ((_, 1), [_; _; c]) -> glob_of_token token_kind ty ?loc env sigma to_post c
  | TConstruct ((_, 2), [_; _; msg]) ->
    let errmsg =
      Termops.Internal.print_constr_env env sigma
        (EConstr.of_constr @@ TokenValue.repr msg)
    in
    no_such_prim_token uninterpreted_token_kind ?loc ~errmsg ty
  | x ->
    let c = TokenValue.repr c in
    Loc.raise ?loc (PrimTokenNotationError(token_kind,env,sigma,UnexpectedNonOptionTerm c))

let uninterp_option c =
  match TokenValue.kind c with
  | TConstruct (_Some, [_; x]) -> x
  | _ -> raise NotAValidPrimToken

let uninterp_error c =
  match TokenValue.kind c with
  | TConstruct ((_, 1), [_; _; x]) -> x
  | _ -> raise NotAValidPrimToken

let uninterp to_raw o n =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let sigma,of_ty = Evd.fresh_global env sigma o.of_ty in
  let of_ty = EConstr.Unsafe.to_constr of_ty in
  try
    let sigma,n = constr_of_glob o.to_post env sigma n in
    let n = EConstr.Unsafe.to_constr n in
    let c = eval_constr_app env sigma of_ty n in
    let c = match snd o.of_kind with
      | Direct -> c
      | Option -> uninterp_option c
      | Error -> uninterp_error c
    in
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
      Termops.pr_global_env (Global.env ()) f ++ strbrk ".")

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

let uninterp_float64 ~print_float c = match TokenValue.kind c with
| TFloat f when not (Float64.is_infinity f || Float64.is_neg_infinity f
                    || Float64.is_nan f) && print_float ->
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
     | Error -> interp_error "number" "number" o.ty_name ?loc env sigma o.to_post res

let uninterp ~print_float o n =
  PrimTokenNotation.uninterp
    begin function
      | (Int _, c) -> NumTok.Signed.of_int (rawnum_of_rocqint c)
      | (UInt _, c) -> NumTok.Signed.of_nat (rawnum_of_rocquint c)
      | (Z _, c) -> NumTok.Signed.of_bigint CDec (bigint_of_z c)
      | (Int63 _, c) -> NumTok.Signed.of_bigint CDec (bigint_of_rocqpos_neg_int63 c)
      | (Float64, c) -> uninterp_float64 ~print_float c
      | (Number _, c) -> rawnum_of_rocqnumber c
    end o n
end

module Strings = struct
(** * String notation *)
open PrimTokenNotation

let q_ref n =
  n |> Rocqlib.lib_ref

let q_list () = q_ref "core.list.type"
let q_byte () = q_ref "core.byte.type"

let force_ind q =
  match q with
  | GlobRef.IndRef i -> i
  | _ -> raise Not_found

let locate_list () = force_ind (q_list ())
let locate_byte () = force_ind (q_byte ())

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
  | Error -> interp_error "string" "string" o.ty_name ?loc env sigma o.to_post res

let uninterp o n =
  PrimTokenNotation.uninterp
    begin function
      | (ListByte, c) -> string_of_rocqlist_byte c
      | (Byte, c) -> string_of_rocqbyte c
      | (PString, c) -> string_of_pstring c
    end o n
end

let hashtbl_check_and_set allow_overwrite uid f h eq =
  match Hashtbl.find h uid with
   | exception Not_found -> Hashtbl.add h uid f
   | _ when allow_overwrite -> Hashtbl.add h uid f
   | g when eq f g -> ()
   | _ ->
      user_err
       (str "Unique identifier " ++ str uid ++
        str " already used to register a number or string (un)interpreter.")

let register_gen_interpretation allow_overwrite (uid:string) (interp, uninterp) : prim_token_uid =
  hashtbl_check_and_set
    allow_overwrite uid interp prim_token_interpreters InnerPrimToken.interp_eq;
  hashtbl_check_and_set
    allow_overwrite uid uninterp prim_token_uninterpreters InnerPrimToken.uninterp_eq;
  uid

let register_rawnumeral_interpretation ?(allow_overwrite=false) uid (interp, uninterp) =
  register_gen_interpretation allow_overwrite uid
    (InnerPrimToken.RawNumInterp interp, InnerPrimToken.RawNumUninterp uninterp)

let register_bignumeral_interpretation ?(allow_overwrite=false) uid (interp, uninterp) =
  register_gen_interpretation allow_overwrite uid
    (InnerPrimToken.BigNumInterp interp, InnerPrimToken.BigNumUninterp uninterp)

let register_string_interpretation ?(allow_overwrite=false) uid (interp, uninterp) =
  register_gen_interpretation allow_overwrite uid
    (InnerPrimToken.StringInterp interp, InnerPrimToken.StringUninterp uninterp)

type prim_token_interp_info =
  | Uid of prim_token_uid
  | NumberNotation of number_notation_obj
  | StringNotation of string_notation_obj

let do_interp ?loc info p =
  let interp = match info with
    | Uid uid -> Hashtbl.find prim_token_interpreters uid
    | NumberNotation o -> InnerPrimToken.RawNumInterp (Numbers.interp o)
    | StringNotation o -> InnerPrimToken.StringInterp (Strings.interp o)
  in
  InnerPrimToken.do_interp ?loc interp p

let do_uninterp ~print_float info c =
  try
    let uninterp = match info with
      | Uid uid -> Hashtbl.find prim_token_uninterpreters uid
      | NumberNotation o -> InnerPrimToken.RawNumUninterp (Numbers.uninterp ~print_float o)
      | StringNotation o -> InnerPrimToken.StringUninterp (Strings.uninterp o)
    in
    InnerPrimToken.do_uninterp uninterp (AnyGlobConstr c)
  with Not_found -> None

let can_interp uid n =
  let open InnerPrimToken in
  match n, uid with
  | Constrexpr.Number _, NumberNotation _ -> true
  | _, NumberNotation _ -> false
  | String _, StringNotation _ -> true
  | _, StringNotation _ -> false
  | _, Uid uid ->
    let interp = Hashtbl.find_opt prim_token_interpreters uid in
    match n, interp with
    | Constrexpr.Number _, Some (RawNumInterp _ | BigNumInterp _) -> true
    | String _, Some (StringInterp _) -> true
    | _ -> false
