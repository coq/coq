(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names

val rename_arguments : local:bool -> GlobRef.t -> Name.t list -> unit

val arguments_names : GlobRef.t -> Name.t list
(** May raise [Not_found].

    Used by arguments in a dubious way: suppose constant [c] has type
   [foo] which reduces to [forall x, ...]. If we rename to [y], the
   type is not affected but the implicit argument system is, for
   instance [c (y:=0)] works and [c (x:=0)] stops working.*)
