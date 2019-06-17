(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open Util
open Names
open Libnames
open Globnames
open Constrexpr
open Constrexpr_ops
open Notation

(** * Numeral notation *)

let warn_abstract_large_num_no_op =
  CWarnings.create ~name:"abstract-large-number-no-op" ~category:"numbers"
    (fun f ->
      strbrk "The 'abstract after' directive has no effect when " ++
      strbrk "the parsing function (" ++
      Nametab.pr_global_env (Termops.vars_of_env (Global.env ())) f ++ strbrk ") targets an " ++
      strbrk "option type.")

let get_constructors ind =
  let mib,oib = Global.lookup_inductive ind in
  let mc = oib.Declarations.mind_consnames in
  Array.to_list
    (Array.mapi (fun j c -> ConstructRef (ind, j + 1)) mc)

let qualid_of_ref n =
  n |> Coqlib.lib_ref |> Nametab.shortest_qualid_of_global Id.Set.empty

let q_option () = qualid_of_ref "core.option.type"

let unsafe_locate_ind q =
  match Nametab.locate q with
  | IndRef i -> i
  | _ -> raise Not_found

let locate_z () =
  let zn = "num.Z.type" in
  let pn = "num.pos.type" in
  if Coqlib.has_ref zn && Coqlib.has_ref pn
  then
    let q_z = qualid_of_ref zn in
    let q_pos = qualid_of_ref pn in
    Some ({
        z_ty = unsafe_locate_ind q_z;
        pos_ty = unsafe_locate_ind q_pos;
    }, mkRefC q_z)
  else None

let locate_decimal () =
  let int = "num.int.type" in
  let uint = "num.uint.type" in
  let dec = "num.decimal.type" in
  if Coqlib.has_ref int && Coqlib.has_ref uint && Coqlib.has_ref dec
  then
    let q_int = qualid_of_ref int in
    let q_uint = qualid_of_ref uint in
    let q_dec = qualid_of_ref dec in
    let int_ty = {
        int = unsafe_locate_ind q_int;
        uint = unsafe_locate_ind q_uint;
      } in
    let dec_ty = {
        int = int_ty;
        decimal = unsafe_locate_ind q_dec;
      } in
    Some (int_ty, mkRefC q_int, mkRefC q_uint, dec_ty, mkRefC q_dec)
  else None

let locate_int63 () =
  let int63n = "num.int63.type" in
  if Coqlib.has_ref int63n
  then
    let q_int63 = qualid_of_ref int63n in
    Some (mkRefC q_int63)
  else None

let has_type env sigma f ty =
  let c = mkCastC (mkRefC f, Glob_term.CastConv ty) in
  try let _ = Constrintern.interp_constr env sigma c in true
  with Pretype_errors.PretypeError _ -> false

let type_error_to f ty =
  CErrors.user_err
    (pr_qualid f ++ str " should go from Decimal.int to " ++
     pr_qualid ty ++ str " or (option " ++ pr_qualid ty ++ str ")." ++
     fnl () ++ str "Instead of Decimal.int, the types Decimal.uint or Z or Int63.int or Decimal.decimal could be used (you may need to require BinNums or Decimal or Int63 first).")

let type_error_of g ty =
  CErrors.user_err
    (pr_qualid g ++ str " should go from " ++ pr_qualid ty ++
     str " to Decimal.int or (option Decimal.int)." ++ fnl () ++
     str "Instead of Decimal.int, the types Decimal.uint or Z or Int63.int or Decimal.decimal could be used (you may need to require BinNums or Decimal or Int63 first).")

let vernac_numeral_notation local ty f g scope opts =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let dec_ty = locate_decimal () in
  let z_pos_ty = locate_z () in
  let int63_ty = locate_int63 () in
  let tyc = Smartlocate.global_inductive_with_alias ty in
  let to_ty = Smartlocate.global_with_alias f in
  let of_ty = Smartlocate.global_with_alias g in
  let cty = mkRefC ty in
  let app x y = mkAppC (x,[y]) in
  let arrow x y =
    mkProdC ([CAst.make Anonymous],Default Decl_kinds.Explicit, x, y)
  in
  let opt r = app (mkRefC (q_option ())) r in
  let constructors = get_constructors tyc in
  (* Check the type of f *)
  let to_kind =
    match dec_ty with
    | Some (int_ty, cint, _, _, _) when has_type env sigma f (arrow cint cty) -> Int int_ty, Direct
    | Some (int_ty, cint, _, _, _) when has_type env sigma f (arrow cint (opt cty)) -> Int int_ty, Option
    | Some (int_ty, _, cuint, _, _) when has_type env sigma f (arrow cuint cty) -> UInt int_ty.uint, Direct
    | Some (int_ty, _, cuint, _, _) when has_type env sigma f (arrow cuint (opt cty)) -> UInt int_ty.uint, Option
    | Some (_, _, _, dec_ty, cdec) when has_type env sigma f (arrow cdec cty) -> Decimal dec_ty, Direct
    | Some (_, _, _, dec_ty, cdec) when has_type env sigma f (arrow cdec (opt cty)) -> Decimal dec_ty, Option
    | _ ->
    match z_pos_ty with
    | Some (z_pos_ty, cZ) when has_type env sigma f (arrow cZ cty) -> Z z_pos_ty, Direct
    | Some (z_pos_ty, cZ) when has_type env sigma f (arrow cZ (opt cty)) -> Z z_pos_ty, Option
    | _ ->
    match int63_ty with
    | Some cint63 when has_type env sigma f (arrow cint63 cty) -> Int63, Direct
    | Some cint63 when has_type env sigma f (arrow cint63 (opt cty)) -> Int63, Option
    | _ -> type_error_to f ty
  in
  (* Check the type of g *)
  let of_kind =
    match dec_ty with
    | Some (int_ty, cint, _, _, _) when has_type env sigma g (arrow cty cint) -> Int int_ty, Direct
    | Some (int_ty, cint, _, _, _) when has_type env sigma g (arrow cty (opt cint)) -> Int int_ty, Option
    | Some (int_ty, _, cuint, _, _) when has_type env sigma g (arrow cty cuint) -> UInt int_ty.uint, Direct
    | Some (int_ty, _, cuint, _, _) when has_type env sigma g (arrow cty (opt cuint)) -> UInt int_ty.uint, Option
    | Some (_, _, _, dec_ty, cdec) when has_type env sigma g (arrow cty cdec) -> Decimal dec_ty, Direct
    | Some (_, _, _, dec_ty, cdec) when has_type env sigma g (arrow cty (opt cdec)) -> Decimal dec_ty, Option
    | _ ->
    match z_pos_ty with
    | Some (z_pos_ty, cZ) when has_type env sigma g (arrow cty cZ) -> Z z_pos_ty, Direct
    | Some (z_pos_ty, cZ) when has_type env sigma g (arrow cty (opt cZ)) -> Z z_pos_ty, Option
    | _ ->
    match int63_ty with
    | Some cint63 when has_type env sigma g (arrow cty cint63) -> Int63, Direct
    | Some cint63 when has_type env sigma g (arrow cty (opt cint63)) -> Int63, Option
    | _ -> type_error_of g ty
  in
  let o = { to_kind; to_ty; of_kind; of_ty;
            ty_name = ty;
            warning = opts }
  in
  (match opts, to_kind with
   | Abstract _, (_, Option) -> warn_abstract_large_num_no_op o.to_ty
   | _ -> ());
  let i =
       { pt_local = local;
         pt_scope = scope;
         pt_interp_info = NumeralNotation o;
         pt_required = Nametab.path_of_global (IndRef tyc),[];
         pt_refs = constructors;
         pt_in_match = true }
  in
  enable_prim_token_interpretation i
