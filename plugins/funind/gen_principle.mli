(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

val warn_cannot_define_graph : ?loc:Loc.t -> Pp.t * Pp.t -> unit
val warn_cannot_define_principle : ?loc:Loc.t -> Pp.t * Pp.t -> unit

val do_generate_principle_interactive :
  Vernacexpr.fixpoint_expr list -> Declare.Proof.t

val do_generate_principle : Vernacexpr.fixpoint_expr list -> unit
val make_graph : Names.GlobRef.t -> unit

(* Can be thrown by build_{,case}_scheme *)
exception No_graph_found

val build_scheme : (Names.Id.t * Libnames.qualid * Sorts.family) list -> unit
val build_case_scheme : Names.Id.t * Libnames.qualid * Sorts.family -> unit
