Require Export Coq.subtac.SubtacTactics.

Set Implicit Arguments.

Notation "'fun' { x : A | P } => Q" :=
  (fun x:{x:A|P} => Q)
  (at level 200, x ident, right associativity).

Notation " {{ x }} " := (tt : { y : unit | x }).

Notation "( x & ? )" := (@exist _ _ x _) : core_scope.

Notation " ! " := (False_rect _ _).

Require Import Coq.Bool.Sumbool.	
Notation "'dec'" := (sumbool_of_bool) (at level 0). 

Definition ex_pi1 (A : Prop) (P : A -> Prop) (t : ex P) : A.
intros.
induction t.
exact x.
Defined.

Lemma ex_pi2  : forall (A : Prop) (P : A -> Prop) (t : ex P),
 P (ex_pi1 t).
intros A P.
dependent inversion t.
simpl.
exact p.
Defined.


Notation "` t" := (proj1_sig t) (at level 100) : core_scope.
Notation "'forall' { x : A | P } , Q" :=
  (forall x:{x:A|P}, Q)
  (at level 200, x ident, right associativity).

Lemma subset_simpl : forall (A : Set) (P : A -> Prop) 
	(t : sig P), P (` t).
Proof.
intros.
induction t.
 simpl ; auto.
Qed.

Lemma equal_f : forall A B : Type, forall (f g : A -> B), 
  f = g -> forall x, f x = g x.
Proof.
  intros.
  rewrite H.
  auto.
Qed.

Ltac subtac_simpl := simpl ; intros ; destruct_exists ; simpl in * ; try subst ; 
  try (solve [ red ; intros ; discriminate ]) ; auto with arith.  

Extraction Inline proj1_sig.
Extract Inductive unit => "unit" [ "()" ].
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].
Axiom pair : Type -> Type -> Type.
Extract Constant pair "'a" "'b" => " 'a * 'b ".
Extract Inductive prod => "pair" [ "" ].
Extract Inductive sigT => "pair" [ "" ].

Require Export ProofIrrelevance.

Delimit Scope program_scope with program.
