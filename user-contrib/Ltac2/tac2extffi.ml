(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Tac2ffi
open Tac2types

module Value = Tac2ffi

(** Make a representation with a dummy from function *)
let make_to_repr f = Tac2ffi.make_repr (fun _ -> assert false) f

(** More ML representations *)

let to_qhyp v = match Value.to_block v with
| (0, [| i |]) -> AnonHyp (Value.to_int i)
| (1, [| id |]) -> NamedHyp (Value.to_ident id)
| _ -> assert false

let qhyp = make_to_repr to_qhyp

let to_bindings = function
| ValInt 0 -> NoBindings
| ValBlk (0, [| vl |]) ->
  ImplicitBindings (Value.to_list Value.to_constr vl)
| ValBlk (1, [| vl |]) ->
  ExplicitBindings ((Value.to_list (fun p -> to_pair to_qhyp Value.to_constr p) vl))
| _ -> assert false

let bindings = make_to_repr to_bindings

let to_constr_with_bindings v = match Value.to_tuple v with
| [| c; bnd |] -> (Value.to_constr c, to_bindings bnd)
| _ -> assert false

let constr_with_bindings = make_to_repr to_constr_with_bindings
