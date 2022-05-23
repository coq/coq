(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module Dynlink : sig
  type t = Opt | Byte | Both | No | Variable
end

val boot : bool ref
val sort : bool ref
val write_vos : bool ref
val noglob : bool ref
val dynlink : Dynlink.t ref
