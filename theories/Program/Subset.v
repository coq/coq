(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import Coq.Program.Utils.
Require Import Coq.Program.Equality.

(** Tactics related to subsets and proof irrelevance. *)

(** Simplify dependent equality using sigmas to equality of the codomains if possible. *)

Ltac simpl_existT :=
  match goal with
    [ H : existT _ ?x _ = existT _ ?x _ |- _ ] => 
    let Hi := fresh H in assert(Hi:=inj_pairT2 _ _ _ _ _ H) ; clear H
  end.

Ltac simpl_existTs := repeat simpl_existT.

(** The following tactics implement a poor-man's solution for proof-irrelevance: it tries to 
   factorize every proof of the same proposition in a goal so that equality of such proofs becomes trivial. *)

Ltac on_subset_proof_aux tac T :=
  match T with
    | context [ exist ?P _ ?p ] => try on_subset_proof_aux tac P ; tac p
  end.

Ltac on_subset_proof tac :=
  match goal with
    [ |- ?T ] => on_subset_proof_aux tac T
  end.

Ltac abstract_any_hyp H' p := 
  match type of p with
    ?X => 
    match goal with 
      | [ H : X |- _ ] => fail 1
      | _ => set (H':=p) ; try (change p with H') ; clearbody H'
    end
  end.

Ltac abstract_subset_proof := 
  on_subset_proof ltac:(fun p => let H := fresh "eqH" in abstract_any_hyp H p ; simpl in H).

Ltac abstract_subset_proofs := repeat abstract_subset_proof.

Ltac pi_subset_proof_hyp p :=
  match type of p with
    ?X => 
    match goal with 
      | [ H : X |- _ ] => 
        match p with
          | H => fail 2
          | _ => rewrite (proof_irrelevance X p H)
        end
      | _ => fail " No hypothesis with same type "
    end
  end.

Ltac pi_subset_proof := on_subset_proof pi_subset_proof_hyp.

Ltac pi_subset_proofs := repeat pi_subset_proof.

(** Clear duplicated hypotheses *)

Ltac clear_dup :=
  match goal with 
    | [ H : ?X |- _ ] => 
      match goal with
        | [ H' : X |- _ ] =>
          match H' with
            | H => fail 2 
            | _ => clear H' || clear H
          end
      end
  end.

Ltac clear_dups := repeat clear_dup.

(** The two preceding tactics in sequence. *)

Ltac clear_subset_proofs :=
  abstract_subset_proofs ; simpl in * |- ; pi_subset_proofs ; clear_dups.

Ltac pi := repeat progress f_equal ; apply proof_irrelevance.

Lemma subset_eq : forall A (P : A -> Prop) (n m : sig P), n = m <-> (`n) = (`m).
Proof.
  induction n.
  induction m.
  simpl.
  split ; intros ; subst.

  inversion H.
  reflexivity.

  pi.
Qed.
