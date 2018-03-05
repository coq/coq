(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Compatibility file for making Coq act similar to Coq v8.7 *)

(* In 8.7, omega wasn't taking advantage of local abbreviations,
   see bug 148 and PR#768. For adjusting this flag, we're forced to
   first dynlink the omega plugin, but we should avoid doing a full
   "Require Omega", since it has some undesired effects (at least on hints)
   and breaks at least fiat-crypto. *)
Declare ML Module "omega_plugin".
Unset Omega UseLocalDefs.


Set Typeclasses Axioms Are Instances.
