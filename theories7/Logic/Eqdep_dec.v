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
  Definition eq2eqT: (A:Set)(x,y:A)x=y->x==y :=
    [A,x,_,eqxy]<[y:A]x==y>Cases eqxy of refl_equal => (refl_eqT ? x) end.

  Definition eqT2eq: (A:Set)(x,y:A)x==y->x=y :=
    [A,x,_,eqTxy]<[y:A]x=y>Cases eqTxy of refl_eqT => (refl_equal ? x) end.

  Lemma eq_eqT_bij: (A:Set)(x,y:A)(p:x=y)p==(eqT2eq (eq2eqT p)).
Intros.
Case p; Reflexivity.
Qed.

  Lemma eqT_eq_bij: (A:Set)(x,y:A)(p:x==y)p==(eq2eqT (eqT2eq p)).
Intros.
Case p; Reflexivity.
Qed.


Section DecidableEqDep.

  Variable A: Type.

  Local comp [x,y,y':A]: x==y->x==y'->y==y' :=
    [eq1,eq2](eqT_ind ? ? [a]a==y' eq2 ? eq1).

  Remark trans_sym_eqT: (x,y:A)(u:x==y)(comp u u)==(refl_eqT ? y).
Intros.
Case u; Trivial.
Qed.



  Variable eq_dec: (x,y:A) x==y \/ ~x==y.

  Variable x: A.


  Local nu [y:A]: x==y->x==y :=
    [u]Cases (eq_dec x y) of
       (or_introl eqxy)  => eqxy
     | (or_intror neqxy) => (False_ind ? (neqxy u))
     end.

  Local nu_constant : (y:A)(u,v:x==y) (nu u)==(nu v).
Intros.
Unfold nu.
Case (eq_dec x y); Intros.
Reflexivity.

Case n; Trivial.
Qed.


  Local nu_inv [y:A]: x==y->x==y := [v](comp (nu (refl_eqT ? x)) v).


  Remark nu_left_inv : (y:A)(u:x==y) (nu_inv (nu u))==u.
Intros.
Case u; Unfold nu_inv.
Apply trans_sym_eqT.
Qed.


  Theorem eq_proofs_unicity: (y:A)(p1,p2:x==y) p1==p2.
Intros.
Elim nu_left_inv with u:=p1.
Elim nu_left_inv with u:=p2.
Elim nu_constant with y p1 p2.
Reflexivity.
Qed.

  Theorem K_dec: (P:x==x->Prop)(P (refl_eqT ? x)) -> (p:x==x)(P p).
Intros.
Elim eq_proofs_unicity with x (refl_eqT ? x) p.
Trivial.
Qed.


  (** The corollary *)

  Local proj: (P:A->Prop)(ExT P)->(P x)->(P x) :=
    [P,exP,def]Cases exP of
      (exT_intro x' prf) =>
        Cases (eq_dec x' x) of
          (or_introl eqprf) => (eqT_ind ? x' P prf x eqprf)
        | _ => def
        end
      end.


  Theorem inj_right_pair: (P:A->Prop)(y,y':(P x))
    (exT_intro ? P x y)==(exT_intro ? P x y') -> y==y'.
Intros.
Cut (proj (exT_intro A P x y) y)==(proj (exT_intro A P x y') y).
Simpl.
Case (eq_dec x x).
Intro e.
Elim e using K_dec; Trivial.

Intros.
Case n; Trivial.

Case H.
Reflexivity.
Qed.

End DecidableEqDep.

  (** We deduce the [K] axiom for (decidable) Set *)
  Theorem K_dec_set: (A:Set)((x,y:A){x=y}+{~x=y})
                       ->(x:A)(P: x=x->Prop)(P (refl_equal ? x))
                         ->(p:x=x)(P p).
Intros.
Rewrite eq_eqT_bij.
Elim (eq2eqT p) using K_dec.
Intros.
Case (H x0 y); Intros.
Elim e; Left ; Reflexivity.

Right ; Red; Intro neq; Apply n; Elim neq; Reflexivity.

Trivial.
Qed.
