(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** We prove that there is only one proof of [x=x], i.e [(refl_equal ? x)].
   This holds if the equality upon the set of [x] is decidable.
   A corollary of this theorem is the equality of the right projections
   of two equal dependent pairs.

   Author:   Thomas Kleymann |<tms@dcs.ed.ac.uk>| in Lego
             adapted to Coq by B. Barras

   Credit:   Proofs up to [K_dec] follows an outline by Michael Hedberg
*)


(** We need some dependent elimination schemes *)

Set Implicit Arguments.

  (** Bijection between [eq] and [eqT] *)
  Definition eq2eqT (A:Set) (x y:A) (eqxy:x = y) : 
    x = y :=
    match eqxy in (_ = y) return x = y with
    | refl_equal => refl_equal x
    end.

  Definition eqT2eq (A:Set) (x y:A) (eqTxy:x = y) : 
    x = y :=
    match eqTxy in (_ = y) return x = y with
    | refl_equal => refl_equal x
    end.

  Lemma eq_eqT_bij : forall (A:Set) (x y:A) (p:x = y), p = eqT2eq (eq2eqT p).
intros.
case p; reflexivity.
Qed.

  Lemma eqT_eq_bij : forall (A:Set) (x y:A) (p:x = y), p = eq2eqT (eqT2eq p).
intros.
case p; reflexivity.
Qed.


Section DecidableEqDep.

  Variable A : Type.

  Let comp (x y y':A) (eq1:x = y) (eq2:x = y') : y = y' :=
    eq_ind _ (fun a => a = y') eq2 _ eq1.

  Remark trans_sym_eqT : forall (x y:A) (u:x = y), comp u u = refl_equal y.
intros.
case u; trivial.
Qed.



  Variable eq_dec : forall x y:A, x = y \/ x <> y.

  Variable x : A.


  Let nu (y:A) (u:x = y) : x = y :=
    match eq_dec x y with
    | or_introl eqxy => eqxy
    | or_intror neqxy => False_ind _ (neqxy u)
    end.

  Let nu_constant : forall (y:A) (u v:x = y), nu u = nu v.
intros.
unfold nu in |- *.
case (eq_dec x y); intros.
reflexivity.

case n; trivial.
Qed.


  Let nu_inv (y:A) (v:x = y) : x = y := comp (nu (refl_equal x)) v.


  Remark nu_left_inv : forall (y:A) (u:x = y), nu_inv (nu u) = u.
intros.
case u; unfold nu_inv in |- *.
apply trans_sym_eqT.
Qed.


  Theorem eq_proofs_unicity : forall (y:A) (p1 p2:x = y), p1 = p2.
intros.
elim nu_left_inv with (u := p1).
elim nu_left_inv with (u := p2).
elim nu_constant with y p1 p2.
reflexivity.
Qed.

  Theorem K_dec :
   forall P:x = x -> Prop, P (refl_equal x) -> forall p:x = x, P p.
intros.
elim eq_proofs_unicity with x (refl_equal x) p.
trivial.
Qed.


  (** The corollary *)

  Let proj (P:A -> Prop) (exP:ex P) (def:P x) : P x :=
    match exP with
    | ex_intro x' prf =>
        match eq_dec x' x with
        | or_introl eqprf => eq_ind x' P prf x eqprf
        | _ => def
        end
    end.


  Theorem inj_right_pair :
   forall (P:A -> Prop) (y y':P x),
     ex_intro P x y = ex_intro P x y' -> y = y'.
intros.
cut (proj (ex_intro P x y) y = proj (ex_intro P x y') y).
simpl in |- *.
case (eq_dec x x).
intro e.
elim e using K_dec; trivial.

intros.
case n; trivial.

case H.
reflexivity.
Qed.

End DecidableEqDep.

  (** We deduce the [K] axiom for (decidable) Set *)
  Theorem K_dec_set :
   forall A:Set,
     (forall x y:A, {x = y} + {x <> y}) ->
     forall (x:A) (P:x = x -> Prop), P (refl_equal x) -> forall p:x = x, P p.
intros.
rewrite eq_eqT_bij.
elim (eq2eqT p) using K_dec.
intros.
case (H x0 y); intros.
elim e; left; reflexivity.

right; red in |- *; intro neq; apply n; elim neq; reflexivity.

trivial.
Qed.