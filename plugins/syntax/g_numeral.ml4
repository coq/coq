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

let eval_constr (c : Constr.t) =
  let env = Global.env () in
  let j = Arguments_renaming.rename_typing env c in
  let c'=
    Vnorm.cbv_vm env (Evd.from_env env)
                 (EConstr.of_constr j.Environ.uj_val)
                 (EConstr.of_constr j.Environ.uj_type)
  in EConstr.Unsafe.to_constr c'

exception NotANumber

let warning_big_num ty =
  strbrk "Stack overflow or segmentation fault happens when " ++
  strbrk "working with large numbers in " ++ pr_reference ty ++
  strbrk " (threshold may vary depending" ++
  strbrk " on your system limits and on the command executed)."

type conversion_function =
  | Direct of Constant.t
  | Option of Constant.t

(** Conversion between Coq's [Positive] and our internal bigint *)

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

(** Conversion between Coq's [Z] and our internal bigint *)

type z_pos_ty =
  { z_ty : Names.inductive;
    pos_ty : Names.inductive }

let maybe_warn (thr,msg) n =
  if Bigint.is_pos_or_zero n && not (Bigint.equal thr Bigint.zero) &&
     Bigint.less_than thr n
  then Feedback.msg_warning msg

let z_of_bigint { z_ty; pos_ty } warn n =
  maybe_warn warn n;
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

(** The uinterp function below work at the level of [glob_constr]
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
  | _ -> CErrors.anomaly (str "interp_big_int: unexpected constr")

let interp_big_int zposty ty warn of_z ?loc bi =
  match of_z with
  | Direct f ->
     let c = mkApp (mkConst f, [| z_of_bigint zposty warn bi |]) in
     glob_of_constr ?loc (eval_constr c)
  | Option f ->
     let c = mkApp (mkConst f, [| z_of_bigint zposty warn bi |]) in
     match Constr.kind (eval_constr c) with
     | App (_Some, [| _; c |]) -> glob_of_constr ?loc c
     | App (_None, [| _ |]) ->
        CErrors.user_err ?loc
         (str "Cannot interpret this number as a value of type " ++
          pr_reference ty)
     | x -> CErrors.anomaly (str "interp_big_int: option expected")

let uninterp_big_int to_z (Glob_term.AnyGlobConstr c) =
  try
    let t = constr_of_glob c in
    match to_z with
    | Direct g ->
       let r = eval_constr (mkApp (mkConst g, [| t |])) in
       Some (bigint_of_z r)
    | Option g ->
       let r = eval_constr (mkApp (mkConst g, [| t |])) in
       match Constr.kind r with
       | App (_Some, [| _; x |]) -> Some (bigint_of_z x)
       | x -> None
  with
  | Type_errors.TypeError _ -> None (* cf. eval_constr *)
  | NotANumber -> None (* cf constr_of_glob or bigint_of_z *)

type numeral_notation_obj =
  { num_ty : Libnames.reference;
    z_pos_ty : z_pos_ty;
    of_z : conversion_function;
    to_z : conversion_function;
    scope : Notation_term.scope_name;
    constructors : Glob_term.glob_constr list;
    warning : Bigint.bigint * Pp.t;
    path : Libnames.full_path }

let load_numeral_notation _ (_, o) =
  Notation.declare_numeral_interpreter o.scope (o.path, [])
   (interp_big_int o.z_pos_ty o.num_ty o.warning o.of_z)
   (o.constructors, uninterp_big_int o.to_z, true)

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

let locate_ind s =
  let q = qualid_of_string s in
  try
    match Nametab.locate q with
    | IndRef i -> i
    | _ -> raise Not_found
  with Not_found -> Nametab.error_global_not_found (CAst.make q)

(** TODO: we should ensure that BinNums is loaded (or autoload it ?) *)

let locate_z () =
  { z_ty = locate_ind "Coq.Numbers.BinNums.Z";
    pos_ty = locate_ind "Coq.Numbers.BinNums.positive"; }

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

let vernac_numeral_notation ty f g scope waft =
  let z_pos_ty = locate_z () in
  let tyc = locate_globref ty in
  let fc = locate_constant f in
  let gc = locate_constant g in
  let cty = mkRefC (CAst.(make (Qualid (qualid_of_reference ty).v)))
  in
  let app x y = mkAppC (x,[y]) in
  let cref s = mkIdentC (Id.of_string s) in
  let arrow x y =
    mkProdC ([CAst.make Anonymous],Default Decl_kinds.Explicit, x, y)
  in
  (* Check that [ty] is an inductive type *)
  let constructors = match tyc with
    | IndRef ind -> get_constructors ind
    | ConstRef _ | ConstructRef _ | VarRef _ ->
       CErrors.user_err
        (pr_reference ty ++ str " is not an inductive type")
  in
  (* Is "f" of type "Z -> ty" or "Z -> option ty" ? *)
  let of_z =
    if has_type f (arrow (cref "Z") cty) then
      Direct fc
    else if has_type f (arrow (cref "Z") (app (cref "option") cty)) then
      Option fc
    else
       CErrors.user_err
        (pr_reference f ++ str " should goes from Z to " ++
         pr_reference ty ++ str " or (option " ++ pr_reference ty ++ str ")")
  in
  (* Is "g" of type "ty -> Z" or "ty -> option Z" ? *)
  let to_z =
    if has_type g (arrow cty (cref "Z")) then
      Direct gc
    else if has_type g (arrow cty (app (cref "option") (cref "Z"))) then
      Option gc
    else
      CErrors.user_err
        (pr_reference g ++ str " should goes from " ++
         pr_reference ty ++ str " to Z or (option Z)")
  in
  Lib.add_anonymous_leaf
    (inNumeralNotation
       { num_ty = ty;
         z_pos_ty;
         of_z;
         to_z;
         scope;
         constructors;
         warning = (Bigint.of_int waft, warning_big_num ty);
         path = Nametab.path_of_global tyc })

open Stdarg

VERNAC COMMAND EXTEND NumeralNotation CLASSIFIED AS SIDEFF
  | [ "Numeral" "Notation" reference(ty) reference(f) reference(g) ":"
      ident(sc) ] ->
    [ let waft = 0 in
      vernac_numeral_notation ty f g (Id.to_string sc) waft ]
  | [ "Numeral" "Notation" reference(ty) reference(f) reference(g) ":"
      ident(sc) "(" "warning" "after" int(waft) ")" ] ->
    [ vernac_numeral_notation ty f g (Id.to_string sc) waft ]
END
