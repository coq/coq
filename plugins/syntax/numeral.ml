(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
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
  with Not_found -> Nametab.error_global_not_found q

let locate_z () =
  try
    Some { z_ty = unsafe_locate_ind q_z;
           pos_ty = unsafe_locate_ind q_positive }
  with Not_found -> None

let locate_int () =
  { uint = locate_ind q_uint;
    int = locate_ind q_int }

let has_type f ty =
  let (sigma, env) = Pfedit.get_current_context () in
  let c = mkCastC (mkRefC f, Glob_term.CastConv ty) in
  try let _ = Constrintern.interp_constr env sigma c in true
  with Pretype_errors.PretypeError _ -> false

let type_error_to f ty loadZ =
  CErrors.user_err
    (pr_qualid f ++ str " should go from Decimal.int to " ++
     pr_qualid ty ++ str " or (option " ++ pr_qualid ty ++ str ")." ++
     fnl () ++ str "Instead of Decimal.int, the types Decimal.uint or Z could be used" ++
     (if loadZ then str " (require BinNums first)." else str "."))

let type_error_of g ty loadZ =
  CErrors.user_err
    (pr_qualid g ++ str " should go from " ++ pr_qualid ty ++
     str " to Decimal.int or (option Decimal.int)." ++ fnl () ++
     str "Instead of Decimal.int, the types Decimal.uint or Z could be used" ++
     (if loadZ then str " (require BinNums first)." else str "."))

let vernac_numeral_notation local ty f g scope opts =
  let int_ty = locate_int () in
  let z_pos_ty = locate_z () in
  let tyc = Smartlocate.global_inductive_with_alias ty in
  let to_ty = Smartlocate.global_with_alias f in
  let of_ty = Smartlocate.global_with_alias g in
  let cty = mkRefC ty in
  let app x y = mkAppC (x,[y]) in
  let cref q = mkRefC q in
  let arrow x y =
    mkProdC ([CAst.make Anonymous],Default Decl_kinds.Explicit, x, y)
  in
  let cZ = cref q_z in
  let cint = cref q_int in
  let cuint = cref q_uint in
  let coption = cref q_option in
  let opt r = app coption r in
  let constructors = get_constructors tyc in
  (* Check the type of f *)
  let to_kind =
    if has_type f (arrow cint cty) then Int int_ty, Direct
    else if has_type f (arrow cint (opt cty)) then Int int_ty, Option
    else if has_type f (arrow cuint cty) then UInt int_ty.uint, Direct
    else if has_type f (arrow cuint (opt cty)) then UInt int_ty.uint, Option
    else
      match z_pos_ty with
      | Some z_pos_ty ->
         if has_type f (arrow cZ cty) then Z z_pos_ty, Direct
         else if has_type f (arrow cZ (opt cty)) then Z z_pos_ty, Option
         else type_error_to f ty false
      | None -> type_error_to f ty true
  in
  (* Check the type of g *)
  let of_kind =
    if has_type g (arrow cty cint) then Int int_ty, Direct
    else if has_type g (arrow cty (opt cint)) then Int int_ty, Option
    else if has_type g (arrow cty cuint) then UInt int_ty.uint, Direct
    else if has_type g (arrow cty (opt cuint)) then UInt int_ty.uint, Option
    else
      match z_pos_ty with
      | Some z_pos_ty ->
         if has_type g (arrow cty cZ) then Z z_pos_ty, Direct
         else if has_type g (arrow cty (opt cZ)) then Z z_pos_ty, Option
         else type_error_of g ty false
      | None -> type_error_of g ty true
  in
  let o = { to_kind; to_ty; of_kind; of_ty;
            num_ty = ty;
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
