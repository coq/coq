(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Tac2val
open Tac2ffi
open Tac2types

module Value = Tac2ffi

(** Make a representation with a dummy from function *)
let make_to_repr f = Tac2ffi.make_repr (fun _ -> assert false) f

(** More ML representations *)

let to_qhyp v = match Value.to_block v with
| (0, [| i |]) -> AnonHyp (Value.to_int i)
| (1, [| id |]) -> NamedHyp (CAst.make (Value.to_ident id))
| _ -> assert false

let qhyp_ = make_to_repr to_qhyp
let qhyp = typed qhyp_ Types.(!! Tac2globals.Types.hypothesis)

let to_bindings = function
| ValInt 0 -> NoBindings
| ValBlk (0, [| vl |]) ->
  ImplicitBindings (Value.to_list Value.to_constr vl)
| ValBlk (1, [| vl |]) ->
  ExplicitBindings ((Value.to_list (fun p -> to_pair to_qhyp Value.to_constr p) vl))
| _ -> assert false

let bindings_ = make_to_repr to_bindings
let bindings = typed bindings_ Types.(!! Tac2globals.Types.bindings)

let constr_with_bindings = pair constr bindings
