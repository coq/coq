(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** [start_deriving f suchthat lemma] starts a proof of [suchthat]
    (which can contain references to [f]) in the context extended by
    [f:=?x]. When the proof ends, [f] is defined as the value of [?x]
    and [lemma] as the proof. *)
val start_deriving : Names.Id.t -> Constrexpr.constr_expr -> Names.Id.t -> unit
