Set Universe Polymorphism.
Set Implicit Arguments.
Cumulative Record prod@{s|*a *b|} (A : Type@{s|a}) (B : Type@{s|b}) : Type@{s|max(a,b)} := pair {
  fst : A;
  snd : B
  }.
Definition flip_prod@{s|a b|} [A : Type@{s|a}] [B : Type@{s|b}] (v : prod A B) : prod B A
  := {| fst := snd v; snd := fst v |}.

(* We need to specify univs here (maybe will be fixed someday?) *)
Fail Definition and@{|} : Prop -> Prop -> Prop := prod.
Definition and@{|} : Prop -> Prop -> Prop := prod@{Prop|Set Set}.

(* but not here (with minim to set on) *)
Definition conj@{|} : forall [A B : Prop], A -> B -> and A B := pair.
Definition proj1@{|} : forall [A B : Prop], and A B -> A := fst.
Definition proj2@{|} : forall [A B : Prop], and A B -> B := snd.
Definition flip_and@{|} : forall [A B : Prop], and A B -> and B A := flip_prod.
