(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Genlambda

(** This file defines the lambda code generation phase of the native compiler *)

type lambda = Nativevalues.t Genlambda.lambda

(*s Constructors *)

(** Simplification of lambda expression *)

let is_value lc =
  match lc with
  | Lval _ | Lint _ | Luint _ | Lfloat _ | Lstring _ -> true
  | _ -> false

let get_value lc =
  match lc with
  | Lval v -> v
  | Lint tag -> Nativevalues.mk_int tag
  | Luint i -> Nativevalues.mk_uint i
  | Lfloat f -> Nativevalues.mk_float f
  | Lstring s -> Nativevalues.mk_string s
  | _ -> raise Not_found

let as_value tag args =
  if Array.for_all is_value args then
    let dummy_val = Obj.magic 0 in
    let args =
      (* Don't simplify this to Array.map, cf. the related comment in
         function eval_to_patch, file kernel/csymtable.ml *)
      let a = Array.make (Array.length args) dummy_val in
      Array.iteri (fun i v -> a.(i) <- get_value v) args; a in
    Some (Nativevalues.mk_block tag args)
  else None

module Val =
struct
  type value = Nativevalues.t
  let as_value = as_value
  let check_inductive _ _ = ()
end

module Lambda = Genlambda.Make(Val)

let lambda_of_constr env sigma c =
  let lam = Lambda.lambda_of_constr env sigma c in
  optimize lam
