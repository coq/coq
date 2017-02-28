(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

DECLARE PLUGIN "numeral_notation_plugin"

open Pp
open Util
open Names
open Libnames
open Globnames
open Constrexpr
open Constrexpr_ops
open Constr
open Misctypes

(** * Numeral notation *)

(** Reduction

    The constr [c] below isn't necessarily well-typed, since we
    built it via an [mkApp] of a conversion function on a term
    that starts with the right constructor, but might be partially
    applied.

    At least [c] is known to be evar-free, since it comes for
    our own ad-hoc [constr_of_glob] or from conversions such
    as [coqint_of_rawnum].
*)

let eval_constr (c : Constr.t) =
  let env = Global.env () in
  let j = Typeops.infer env c in
  let c'=
    Vnorm.cbv_vm env (Evd.from_env env)
                 (EConstr.of_constr j.Environ.uj_val)
                 (EConstr.of_constr j.Environ.uj_type)
  in EConstr.Unsafe.to_constr c'

(* For testing with "compute" instead of "vm_compute" :
let eval_constr (c : constr) =
 let (sigma, env) = Lemmas.get_current_context () in
 Tacred.compute env sigma c
*)

let eval_constr_app c1 c2 = eval_constr (mkApp (c1,[| c2 |]))

exception NotANumber

let warning_big_num ty =
  strbrk "Stack overflow or segmentation fault happens when " ++
  strbrk "working with large numbers in " ++ pr_reference ty ++
  strbrk " (threshold may vary depending" ++
  strbrk " on your system limits and on the command executed)."

let warning_abstract_num ty f =
  let (sigma, env) = Pfedit.get_current_context () in
  strbrk "To avoid stack overflow, large numbers in " ++
  pr_reference ty ++ strbrk " are interpreted as applications of " ++
  Printer.pr_constr_env env sigma f ++ strbrk "."

(** Comparing two raw numbers (base 10, big-endian, non-negative).
    A bit nasty, but not critical : only used to decide when a
    nat number is considered as large. *)

exception Comp of int

let rec rawnum_compare s s' =
 let l = String.length s and l' = String.length s' in
 if l < l' then - rawnum_compare s' s
 else
   let d = l-l' in
   try
     for i = 0 to d-1 do if s.[i] != '0' then raise (Comp 1) done;
     for i = d to l-1 do
       let c = Pervasives.compare s.[i] s'.[i-d] in
       if c != 0 then raise (Comp c)
     done;
     0
   with Comp c -> c

(***********************************************************************)

(** ** Conversion between Coq [Decimal.int] and internal raw string *)

type int_ty =
  { uint : Names.inductive;
    int : Names.inductive }

(** Decimal.Nil has index 1, then Decimal.D0 has index 2 .. Decimal.D9 is 11 *)

let digit_of_char c =
  assert ('0' <= c && c <= '9');
  Char.code c - Char.code '0' + 2

let char_of_digit n =
  assert (2<=n && n<=11);
  Char.chr (n-2 + Char.code '0')

let coquint_of_rawnum uint str =
  let nil = mkConstruct (uint,1) in
  let rec do_chars s i acc =
    if i < 0 then acc
    else
      let dg = mkConstruct (uint, digit_of_char s.[i]) in
      do_chars s (i-1) (mkApp(dg,[|acc|]))
  in
  do_chars str (String.length str - 1) nil

let coqint_of_rawnum inds (str,sign) =
  let uint = coquint_of_rawnum inds.uint str in
  mkApp (mkConstruct (inds.int, if sign then 1 else 2), [|uint|])

let rawnum_of_coquint c =
  let rec of_uint_loop c buf =
    match Constr.kind c with
    | Construct ((_,1), _) (* Nil *) -> ()
    | App (c, [|a|]) ->
       (match Constr.kind c with
        | Construct ((_,n), _) (* D0 to D9 *) ->
           let () = Buffer.add_char buf (char_of_digit n) in
           of_uint_loop a buf
        | _ -> raise NotANumber)
    | _ -> raise NotANumber
  in
  let buf = Buffer.create 64 in
  let () = of_uint_loop c buf in
  if Int.equal (Buffer.length buf) 0 then
    (* To avoid ambiguities between Nil and (D0 Nil), we choose
       to not display Nil alone as "0" *)
    raise NotANumber
  else Buffer.contents buf

let rawnum_of_coqint c =
  match Constr.kind c with
  | App (c,[|c'|]) ->
     (match Constr.kind c with
      | Construct ((_,1), _) (* Pos *) -> (rawnum_of_coquint c', true)
      | Construct ((_,2), _) (* Neg *) -> (rawnum_of_coquint c', false)
      | _ -> raise NotANumber)
  | _ -> raise NotANumber


(***********************************************************************)

(** ** Conversion between Coq [Z] and internal bigint *)

type z_pos_ty =
  { z_ty : Names.inductive;
    pos_ty : Names.inductive }

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
      | x -> raise NotANumber
      end
  | x -> raise NotANumber

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
      | _ -> raise NotANumber
      end
  | _ -> raise NotANumber

(** The uninterp function below work at the level of [glob_constr]
    which is too low for us here. So here's a crude conversion back
    to [constr] for the subset that concerns us. *)

let rec constr_of_glob g = match DAst.get g with
  | Glob_term.GRef (ConstructRef c, _) -> mkConstruct c
  | Glob_term.GApp (gc, gcl) ->
      let c = constr_of_glob gc in
      let cl = List.map constr_of_glob gcl in
      mkApp (c, Array.of_list cl)
  | _ ->
      raise NotANumber

let rec glob_of_constr ?loc c = match Constr.kind c with
  | App (c, ca) ->
      let c = glob_of_constr ?loc c in
      let cel = List.map (glob_of_constr ?loc) (Array.to_list ca) in
      DAst.make ?loc (Glob_term.GApp (c, cel))
  | Construct (c, _) -> DAst.make ?loc (Glob_term.GRef (ConstructRef c, None))
  | Const (c, _) -> DAst.make ?loc (Glob_term.GRef (ConstRef c, None))
  | Ind (ind, _) -> DAst.make ?loc (Glob_term.GRef (IndRef ind, None))
  | Var id -> DAst.make ?loc (Glob_term.GRef (VarRef id, None))
  | _ -> CErrors.anomaly (str "Numeral.interp: unexpected constr")

let no_such_number ?loc ty =
  CErrors.user_err ?loc
   (str "Cannot interpret this number as a value of type " ++
    pr_reference ty)

let interp_option ty ?loc c =
  match Constr.kind c with
  | App (_Some, [| _; c |]) -> glob_of_constr ?loc c
  | App (_None, [| _ |]) -> no_such_number ?loc ty
  | x -> CErrors.anomaly (str "Numeral.interp: option expected")

let uninterp_option c =
  match Constr.kind c with
  | App (_Some, [| _; x |]) -> x
  | _ -> raise NotANumber

let big2raw n =
  if Bigint.is_pos_or_zero n then (Bigint.to_string n, true)
  else (Bigint.to_string (Bigint.neg n), false)

let raw2big (n,s) =
  if s then Bigint.of_string n else Bigint.neg (Bigint.of_string n)

type target_kind = Int | UInt | Z
type option_kind = Option | Direct
type conversion_kind = target_kind * option_kind

type numnot_option =
  | Nop
  | Warning of raw_natural_number
  | Abstract of raw_natural_number

type numeral_notation_obj =
  { num_ty : Libnames.reference;
    z_pos_ty : z_pos_ty option;
    int_ty : int_ty;
    to_kind : conversion_kind;
    to_ty : constr;
    of_kind : conversion_kind;
    of_ty : constr;
    scope : Notation_term.scope_name;
    constructors : Glob_term.glob_constr list;
    warning : numnot_option;
    path : Libnames.full_path }

let interp o ?loc n =
  begin match o.warning with
  | Warning threshold when snd n && rawnum_compare (fst n) threshold >= 0 ->
     Feedback.msg_warning (warning_big_num o.num_ty)
  | _ -> ()
  end;
  let c = match fst o.to_kind with
    | Int -> coqint_of_rawnum o.int_ty n
    | UInt when snd n -> coquint_of_rawnum o.int_ty.uint (fst n)
    | UInt (* n <= 0 *) -> no_such_number ?loc o.num_ty
    | Z -> z_of_bigint (Option.get o.z_pos_ty) (raw2big n)
  in
  match o.warning, snd o.to_kind with
  | Abstract threshold, Direct when rawnum_compare (fst n) threshold >= 0 ->
     Feedback.msg_warning (warning_abstract_num o.num_ty o.to_ty);
     glob_of_constr ?loc (mkApp (o.to_ty,[|c|]))
  | _ ->
     let res = eval_constr_app o.to_ty c in
     match snd o.to_kind with
     | Direct -> glob_of_constr ?loc res
     | Option -> interp_option o.num_ty ?loc res

let uninterp o (Glob_term.AnyGlobConstr n) =
  try
    let c = eval_constr_app o.of_ty (constr_of_glob n) in
    let c = if snd o.of_kind == Direct then c else uninterp_option c in
    match fst o.of_kind with
    | Int -> Some (rawnum_of_coqint c)
    | UInt -> Some (rawnum_of_coquint c, true)
    | Z -> Some (big2raw (bigint_of_z c))
  with
  | Type_errors.TypeError _ -> None (* cf. eval_constr_app *)
  | NotANumber -> None (* all other functions except big2raw *)

let load_numeral_notation _ (_, o) =
  Notation.declare_rawnumeral_interpreter o.scope (o.path, [])
  (interp o)
  (o.constructors, uninterp o, true)

let cache_numeral_notation o = load_numeral_notation 1 o

let inNumeralNotation : numeral_notation_obj -> Libobject.obj =
  Libobject.declare_object {
    (Libobject.default_object "NUMERAL NOTATION") with
    Libobject.cache_function = cache_numeral_notation;
    Libobject.load_function = load_numeral_notation }

let get_constructors ind =
  let mib,oib = Global.lookup_inductive ind in
  let mc = oib.Declarations.mind_consnames in
  Array.to_list
    (Array.mapi
       (fun j c ->
         DAst.make
           (Glob_term.GRef (ConstructRef (ind, j + 1), None)))
       mc)

let q_z = qualid_of_string "Coq.Numbers.BinNums.Z"
let q_positive = qualid_of_string "Coq.Numbers.BinNums.positive"
let q_int = qualid_of_string "Coq.Init.Decimal.int"
let q_uint = qualid_of_string "Coq.Init.Decimal.uint"
let q_option = qualid_of_string "Coq.Init.Datatypes.option"

let unsafe_locate_ind q =
  match Nametab.locate q with
  | IndRef i -> i
  | _ -> raise Not_found

let locate_ind q =
  try unsafe_locate_ind q
  with Not_found -> Nametab.error_global_not_found (CAst.make q)

let locate_z () =
  try
    Some { z_ty = unsafe_locate_ind q_z;
           pos_ty = unsafe_locate_ind q_positive }
  with Not_found -> None

let locate_int () =
  { uint = locate_ind q_uint;
    int = locate_ind q_int }

let locate_globref r =
  let q = qualid_of_reference r in
  try Nametab.locate CAst.(q.v)
  with Not_found -> Nametab.error_global_not_found q

let locate_constant r =
  let q = qualid_of_reference r in
  try Nametab.locate_constant CAst.(q.v)
  with Not_found -> Nametab.error_global_not_found q

let has_type f ty =
  let (sigma, env) = Pfedit.get_current_context () in
  let c = mkCastC (mkRefC f, CastConv ty) in
  try let _ = Constrintern.interp_constr env sigma c in true
  with Pretype_errors.PretypeError _ -> false

let vernac_numeral_notation ty f g scope opts =
  let int_ty = locate_int () in
  let z_pos_ty = locate_z () in
  let tyc = locate_globref ty in
  let to_ty = mkConst (locate_constant f) in
  let of_ty = mkConst (locate_constant g) in
  let cty = mkRefC ty in
  let app x y = mkAppC (x,[y]) in
  let cref q = mkRefC (CAst.make (Qualid q)) in
  let arrow x y =
    mkProdC ([CAst.make Anonymous],Default Decl_kinds.Explicit, x, y)
  in
  let cZ = cref q_z in
  let cint = cref q_int in
  let cuint = cref q_uint in
  let coption = cref q_option in
  let opt r = app coption r in
  (* Check that [ty] is an inductive type *)
  let constructors = match tyc with
    | IndRef ind when not (Global.is_polymorphic tyc) ->
       get_constructors ind
    | IndRef _ ->
       CErrors.user_err
         (str "The inductive type " ++ pr_reference ty ++
          str " cannot be polymorphic here for the moment")
    | ConstRef _ | ConstructRef _ | VarRef _ ->
       CErrors.user_err
        (pr_reference ty ++ str " is not an inductive type")
  in
  (* Check the type of f *)
  let to_kind =
    if has_type f (arrow cint cty) then Int, Direct
    else if has_type f (arrow cint (opt cty)) then Int, Option
    else if has_type f (arrow cuint cty) then UInt, Direct
    else if has_type f (arrow cuint (opt cty)) then UInt, Option
    else if Option.is_empty z_pos_ty then
      CErrors.user_err
        (pr_reference f ++ str " should goes from Decimal.int or uint to " ++
         pr_reference ty ++ str " or (option " ++ pr_reference ty ++
         str ")." ++ fnl () ++
         str "Instead of int, the type Z could also be used (load it first).")
    else if has_type f (arrow cZ cty) then Z, Direct
    else if has_type f (arrow cZ (opt cty)) then Z, Option
    else
       CErrors.user_err
        (pr_reference f ++ str " should goes from Decimal.int or uint or Z to "
         ++
         pr_reference ty ++ str " or (option " ++ pr_reference ty ++ str ")")
  in
  (* Check the type of g *)
  let of_kind =
    if has_type g (arrow cty cint) then Int, Direct
    else if has_type g (arrow cty (opt cint)) then Int, Option
    else if has_type g (arrow cty cuint) then UInt, Direct
    else if has_type g (arrow cty (opt cuint)) then UInt, Option
    else if Option.is_empty z_pos_ty then
      CErrors.user_err
        (pr_reference g ++ str " should goes from " ++
         pr_reference ty ++
         str " to Decimal.int or (option int) or uint." ++ fnl () ++
         str "Instead of int, the type Z could also be used (load it first).")
    else if has_type g (arrow cty cZ) then Z, Direct
    else if has_type g (arrow cty (opt cZ)) then Z, Option
    else
      CErrors.user_err
        (pr_reference g ++ str " should goes from " ++
         pr_reference ty ++
         str " to Decimal.int or (option int) or uint or Z or (option Z)")
  in
  Lib.add_anonymous_leaf
    (inNumeralNotation
       { num_ty = ty;
         z_pos_ty;
         int_ty;
         to_kind;
         to_ty;
         of_kind;
         of_ty;
         scope;
         constructors;
         warning = opts;
         path = Nametab.path_of_global tyc })

open Ltac_plugin
open Stdarg
open Pcoq.Prim

let pr_numnot_option _ _ _ = function
  | Nop -> mt ()
  | Warning n -> str "(warning after " ++ str n ++ str ")"
  | Abstract n -> str "(abstract after " ++ str n ++ str ")"

ARGUMENT EXTEND numnotoption
  PRINTED BY pr_numnot_option
| [ ] -> [ Nop ]
| [ "(" "warning" "after" bigint(waft) ")" ] -> [ Warning waft ]
| [ "(" "abstract" "after" bigint(n) ")" ] -> [ Abstract n ]
END

VERNAC COMMAND EXTEND NumeralNotation CLASSIFIED AS SIDEFF
  | [ "Numeral" "Notation" reference(ty) reference(f) reference(g) ":"
      ident(sc) numnotoption(o) ] ->
    [ vernac_numeral_notation ty f g (Id.to_string sc) o ]
END
