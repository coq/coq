(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** [declare_mind me] declares a block of inductive types with
   their constructors in the current section; it returns the path of
   the whole block and a boolean indicating if it is a primitive record. *)
val declare_mind : Entries.mutual_inductive_entry -> Libobject.object_name * bool
