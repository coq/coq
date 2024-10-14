(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Genarg

(** Substitution functions *)
type 'glb subst_fun = Mod_subst.substitution -> 'glb -> 'glb

module SubstObj =
struct
  type ('raw, 'glb, 'top) obj = 'glb subst_fun
  let name = "subst"
  let default _ = None
end

module Subst = Register (SubstObj)

let substitute = Subst.obj
let register_subst0 = Subst.register0

let generic_substitute subs (GenArg (Glbwit wit, v)) =
  in_gen (glbwit wit) (substitute wit subs v)
