Set Implicit Arguments.

Notation "'fun' { x : A | P } => Q" :=
  (fun x:{x:A|P} => Q)
  (at level 200, x ident, right associativity).

Notation "( x & ? )" := (@exist _ _ x _) : core_scope.

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

Ltac destruct_one_pair :=
 match goal with
 | [H : (ex _) |- _] => destruct H
 | [H : (ex2 _) |- _] => destruct H
 | [H : (sig _) |- _] => destruct H
 | [H : (_ /\ _) |- _] => destruct H
end.

Ltac destruct_exists := repeat (destruct_one_pair) .

Ltac subtac_simpl := simpl ; intros ; destruct_exists ; simpl in *.

(* Destructs calls to f in hypothesis or conclusion, useful if f creates a subset object *)
Ltac destruct_call f :=
  match goal with
    | H : ?T |- _  =>
      match T with
         context [f ?x ?y ?z] => destruct (f x y z)
       | context [f ?x ?y] => destruct (f x y)
       | context [f ?x] => destruct (f x)        
      end
    | |- ?T  =>
      match T with
        context [f ?x ?y ?z] => let n := fresh "H" in set (n:=f x y z); destruct n
        | context [f ?x ?y] => let n := fresh "H" in set (n:=f x y); destruct n
        | context [f ?x] => let n := fresh "H" in set (n:=f x); destruct n
      end
    end.

Extraction Inline proj1_sig.

Require Export ProofIrrelevance.
