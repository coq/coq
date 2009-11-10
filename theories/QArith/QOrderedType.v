(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import QArith_base
 DecidableType2 OrderedType2 OrderedType2Facts.

Local Open Scope Q_scope.

(** * DecidableType structure for rational numbers *)

Module Q_as_DT <: DecidableType.
 Definition t := Q.
 Definition eq := Qeq.
 Instance eq_equiv : Equivalence Qeq.
 Definition eq_dec := Qeq_dec.

 (** The next fields are not mandatory, but allow [Q_as_DT] to be
     also a [DecidableTypeOrig] (resp. a [BooleanEqualityType]). *)
 Definition eq_refl := Qeq_refl.
 Definition eq_sym := Qeq_sym.
 Definition eq_trans := eq_trans.

 Definition eqb := Qeq_bool.
 Definition eqb_eq := Qeq_bool_iff.

End Q_as_DT.


(** * OrderedType structure for rational numbers *)

Module Q_as_OT <: OrderedTypeFull.
 Include Q_as_DT.
 Definition lt := Qlt.
 Definition le := Qle.
 Definition compare := Qcompare.

 Instance lt_strorder : StrictOrder Qlt.
 Proof. split; [ exact Qlt_irrefl | exact Qlt_trans ]. Qed.

 Instance lt_compat : Proper (Qeq==>Qeq==>iff) Qlt.
 Proof. auto with *. Qed.

 Definition le_lteq := Qle_lteq.
 Definition compare_spec := Qcompare_spec.

End Q_as_OT.


(** * An [order] tactic for [Q] numbers *)

Module QOrder := OTF_to_OrderTac Q_as_OT.
Ltac q_order := QOrder.order.

(** Note that [q_order] is domain-agnostic: it will not prove
    [1<=2] or [x<=x+x], but rather things like [x<=y -> y<=x -> x==y]. *)
