Set Universe Polymorphism.

(* univ_anot in Primitive Arrays *)

From Corelib Require Import Array.PrimArray.

#[universes(polymorphic=no)]Universe a b.

Definition a11 : array@{a} Type@{b} := ([|nat; Set; Type; Prop; SProp; Univ|Univ|]@{;+}).
Definition a12 : array@{b} nat := ([| |1|]@{;+}).

Definition a21 : array@{a} Type@{b} := ([|nat; Set; Type; Prop; SProp; Univ|Univ|]@{+;+}).
Definition a22 : array@{b} nat := ([| |1|]@{+;+}).

Definition a31 : array@{a} Type@{b} := ([|nat; Set; Type; Prop; SProp; Univ|Univ|]@{+;_ +}).
Definition a32 : array@{b} nat := ([| |1|]@{+;_ +}).

Fail Definition a41 := ([|nat; Set; Type; Prop; SProp; Univ|Univ|]@{+;_ _ +}).
Fail Definition a42 := ([| |1|]@{+;_ _ +}).

(* univ_anot in Variables inside sections *)

Section Pretype_ref.
    Variable v : Type.
    Check v.
    Check v@{+;+}.
    Check v@{+;}.
    Check v@{;+}.
    Check v@{;}.
    Check v@{}.
    Fail Check v@{_}.
    Fail Check v@{_ +;_ +}.
    Fail Check v@{_ +;}.
    Fail Check v@{;_ +}.
    Fail Check v@{_;}.
    Fail Check v@{_;_}.
End Pretype_ref.

(* Rewriting some of Init/Logic.v from the corelib, but in sort-poly
    using the extensible flag "+" in univ_annot.
*)

Inductive trivial@{s;+} : Univ@{s;_} :=
  trivial_cons : trivial.
Definition True' : Prop := trivial@{Prop;+}.

Inductive impossible@{s;+} : Univ@{s;_} :=.
Definition False' : Prop := impossible@{Prop;+}.

Definition not_sortpoly@{sa s;+} (A:Univ@{sa;_}) := A -> impossible@{s;+}.
Definition not' : Prop -> Prop := not_sortpoly@{Prop Prop;+}.

Definition notT := not_sortpoly@{Type Prop;+}.

Inductive and_sortpoly@{sa sb s;+}
  (A : Univ@{sa;_}) (B : Univ@{sb;_}) : Univ@{s;_} :=
    conj_sortpoly : A -> B -> and_sortpoly A B.

Definition and' : Prop -> Prop -> Prop := and_sortpoly@{Prop Prop Prop;+}.
Definition conj' : forall A B : Prop, A -> B -> and_sortpoly A B
  := conj_sortpoly@{Prop Prop Prop;+}.

Section Conjunction.
  Sort sa sb se.

  Constraint se->sa.
  Constraint se->sb.

  Variables (A : Univ@{sa;_}) (B : Univ@{sb;_}).

  Theorem proj1_sortpoly' : and_sortpoly@{sa sb se;+} A B -> A.
  Proof.
    destruct 1; trivial.
  Qed.

  Theorem proj2_sortpoly'@{+} : and_sortpoly@{sa sb se;+} A B -> B.
  Proof.
    destruct 1; trivial.
  Qed.

End Conjunction.

Definition proj1' : forall A B : Prop, and_sortpoly A B -> A
  := proj1_sortpoly'@{Prop Prop Prop; +}.
Definition proj2' : forall A B : Prop, and_sortpoly A B -> B
  := proj2_sortpoly'@{Prop Prop Prop; +}.

Unset Collapse Sorts ToType.

Inductive or_sortpoly@{+;+}
  (A : Univ) (B : Univ) : Univ@{_;_} :=
  | or_introl_sortpoly : A -> or_sortpoly A B
  | or_intror_sortpoly : B -> or_sortpoly A B.

Definition or' : Prop -> Prop -> Prop := or_sortpoly@{Prop Prop Prop;_ _ _}.
Definition or_introl' : forall A B : Prop, A -> or' A B
  := or_introl_sortpoly@{Prop Prop Prop;_ _ _}.
Definition or_intror' : forall A B : Prop, B -> or' A B
  := or_intror_sortpoly@{Prop Prop Prop;_ _ _}.

Definition iff_sortpoly@{sa sb s;la lb l u}
  (A : Univ@{sa;la}) (B : Univ@{sb;lb}) : Univ@{s;l} :=
  and_sortpoly@{sb sa s;u u l} (A -> B) (B -> A).
Definition iff' : Prop -> Prop -> Prop :=
  iff_sortpoly@{Prop Prop Prop;_ _ _ _}.

(* Refman example *)

Polymorphic Definition le@{i j} (A : Type@{i}) : Type@{j} := A.
Check le@{+}.

(* These Checks must fail *)
Fail Check le@{_ _ _ +}.
Fail Check iff_sortpoly@{_ _ _ _}.
(* Shouldn't this be equivalent to `iff_sortpoly@{+;_ _ _ _}` ? Not yet at least.
  See discussion about this topic in PR #22621 (github.com/rocq-prover/rocq/pull/22621).
 *)

(* Changed `univ_name_list` *)
Print le@{+}.
About le@{+}.
Fail Print le@{_ _ _ +}.
