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

(** * String notation *)

let get_constructors ind =
  let mib,oib = Global.lookup_inductive ind in
  let mc = oib.Declarations.mind_consnames in
  Array.to_list
    (Array.mapi (fun j c -> ConstructRef (ind, j + 1)) mc)

let qualid_of_ref n =
  n |> Coqlib.lib_ref |> Nametab.shortest_qualid_of_global Id.Set.empty

let q_option () = qualid_of_ref "core.option.type"
let q_list () = qualid_of_ref "core.list.type"
let q_byte () = qualid_of_ref "core.byte.type"

let has_type env sigma f ty =
  let c = mkCastC (mkRefC f, Glob_term.CastConv ty) in
  try let _ = Constrintern.interp_constr env sigma c in true
  with Pretype_errors.PretypeError _ -> false

let type_error_to f ty =
  CErrors.user_err
    (pr_qualid f ++ str " should go from Byte.byte or (list Byte.byte) to " ++
     pr_qualid ty ++ str " or (option " ++ pr_qualid ty ++ str ").")

let type_error_of g ty =
  CErrors.user_err
    (pr_qualid g ++ str " should go from " ++ pr_qualid ty ++
     str " to Byte.byte or (option Byte.byte) or (list Byte.byte) or (option (list Byte.byte)).")

let vernac_string_notation local ty f g scope =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let app x y = mkAppC (x,[y]) in
  let cref q = mkRefC q in
  let cbyte = cref (q_byte ()) in
  let clist = cref (q_list ()) in
  let coption = cref (q_option ()) in
  let opt r = app coption r in
  let clist_byte = app clist cbyte in
  let tyc = Smartlocate.global_inductive_with_alias ty in
  let to_ty = Smartlocate.global_with_alias f in
  let of_ty = Smartlocate.global_with_alias g in
  let cty = cref ty in
  let arrow x y =
    mkProdC ([CAst.make Anonymous],Default Decl_kinds.Explicit, x, y)
  in
  let constructors = get_constructors tyc in
  (* Check the type of f *)
  let to_kind =
    if has_type env sigma f (arrow clist_byte cty) then ListByte, Direct
    else if has_type env sigma f (arrow clist_byte (opt cty)) then ListByte, Option
    else if has_type env sigma f (arrow cbyte cty) then Byte, Direct
    else if has_type env sigma f (arrow cbyte (opt cty)) then Byte, Option
    else type_error_to f ty
  in
  (* Check the type of g *)
  let of_kind =
    if has_type env sigma g (arrow cty clist_byte) then ListByte, Direct
    else if has_type env sigma g (arrow cty (opt clist_byte)) then ListByte, Option
    else if has_type env sigma g (arrow cty cbyte) then Byte, Direct
    else if has_type env sigma g (arrow cty (opt cbyte)) then Byte, Option
    else type_error_of g ty
  in
  let o = { to_kind = to_kind;
            to_ty = to_ty;
            of_kind = of_kind;
            of_ty = of_ty;
            ty_name = ty;
            warning = () }
  in
  let i =
       { pt_local = local;
         pt_scope = scope;
         pt_interp_info = StringNotation o;
         pt_required = Nametab.path_of_global (IndRef tyc),[];
         pt_refs = constructors;
         pt_in_match = true }
  in
  enable_prim_token_interpretation i
