Set Universe Polymorphism.
Set Implicit Arguments.
Cumulative Record prod@{s| -a|} (A : Type@{s|a}) (B : Type@{s|a}) : Type@{s|a} := pair {
  fst : A;
  snd : B
  }.
Definition flip_prod@{s|a b|} [A : Type@{s|a}] [B : Type@{s|b}] (v : prod A B) : prod B A
  := {| fst := snd v; snd := fst v |}.

Definition and@{|} : Prop -> Prop -> Prop := prod.

Check prod True Set.

Definition conj@{|} : forall [A B : Prop], A -> B -> and A B := pair.
Definition proj1@{|} : forall [A B : Prop], and A B -> A := fst.
Definition proj2@{|} : forall [A B : Prop], and A B -> B := snd.
Definition flip_and@{|} : forall [A B : Prop], and A B -> and B A := flip_prod.
