(** PARSER TESTS *)

(** Check correct separation of identifiers followed by unicode symbols *)
Notation "x ⊕ w" := (plus x w) (at level 30).
Check fun x => x⊕x.

(** Check Greek letters *)
Definition test_greek : nat -> nat := fun Δ => Δ.
Parameter ℝ : Set.
Parameter π : ℝ.

(** Check indices *)
Definition test_indices : nat -> nat := fun x₁ => x₁.
Definition π₂ := @snd.

(** More unicode in identifiers *)
Definition αβ_áà_אב := 0.

Notation "C 'ᵒᵖ'" := C (at level 30).

(** UNICODE IN STRINGS *)

Require Import List Ascii String.
Open Scope string_scope.

Definition test_string := "azertyαβ∀ééé".
Eval compute in length test_string.
 (** last six "chars" are unicode, hence represented by 2 bytes,
     except the forall which is 3 bytes *)

Fixpoint string_to_list s :=
  match s with
    | EmptyString => nil
    | String c s => c :: string_to_list s
  end.

Eval compute in (string_to_list test_string).
 (** for instance, α is \206\177 whereas ∀ is \226\136\128 *)
Close Scope string_scope.



(** INTERFACE TESTS *)

Require Import Utf8.

(** Printing of unicode notation, in *goals* *)
Lemma test : forall A:Prop, A -> A.
Proof.
auto.
Qed.

(** Parsing of unicode notation, in *goals* *)
Lemma test2 : ∀A:Prop, A → A.
Proof.
intro.
intro.
auto.
Qed.

(** Printing of unicode notation, in *response* *)
Check fun (X:Type)(x:X) => x.

(** Parsing of unicode notation, in *response* *)
Check ∀Δ, Δ → Δ.
Check ∀x, x=0 ∨ x=0 → x=0.


(** ISSUES: *)

Notation "x ≠ y" := (x<>y) (at level 70).

Notation "x ≤ y" := (x<=y) (at level 70, no associativity).

(** First Issue : ≤ is attached to "le" of nat, not to notation <= *)

Require Import ZArith.
Open Scope Z_scope.
Locate "≤". (* still le, not Z.le *)
Notation "x ≤ y" := (x<=y) (at level 70, no associativity).
Locate "≤".
Close Scope Z_scope.

(** ==> How to proceed modularly ? *)


(** Second Issue : notation for -> generates useless parenthesis
   if followed by a binder *)

Check 0≠0 → ∀x:nat,x=x.

(** Example of real situation : *)

Definition pred : ∀x, x≠0 → ∃y, x = S y.
Proof.
destruct x.
destruct 1; auto.
intros _.
exists x; auto.
Defined.

Print pred.



