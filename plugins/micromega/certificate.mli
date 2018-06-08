(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module Mc = Micromega

type 'a number_spec

val q_cert_of_pos : Sos_types.positivstellensatz -> Mc.q Mc.psatz
val z_cert_of_pos : Sos_types.positivstellensatz -> Mc.z Mc.psatz
val lia : bool -> int -> (Mc.z Mc.pExpr * Mc.op1) list -> Mc.zArithProof option
val nlia : bool -> int -> (Mc.z Mc.pExpr * Mc.op1) list -> Mc.zArithProof option
val nlinear_prover : int -> (Mc.q Mc.pExpr * Mc.op1) list -> Mc.q Mc.psatz option
val linear_prover_with_cert : int -> 'a number_spec ->
  ('a Mc.pExpr * Mc.op1) list -> 'a Mc.psatz option
val q_spec : Mc.q number_spec
