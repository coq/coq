(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

val warn_cannot_define_graph : ?loc:Loc.t -> Pp.t * Pp.t -> unit
val warn_cannot_define_principle : ?loc:Loc.t -> Pp.t * Pp.t -> unit

val do_generate_principle_interactive : Vernacexpr.fixpoint_expr list -> Lemmas.t
val do_generate_principle : Vernacexpr.fixpoint_expr list -> unit

val make_graph : Names.GlobRef.t -> unit
