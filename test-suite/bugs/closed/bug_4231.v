(* File reduced by coq-bug-finder from original input, then from 981 lines to 33 lines *)
(* coqc version 8.5beta2 (May 2015) compiled on May 5 2015 15:20:21 with OCaml 4.01.0
   coqtop version 8.5beta2 (May 2015) *)

Axiom ap : forall {A B:Type} (f:A -> B) {x y:A} (p:x = y), f x = f y.

Definition Sect {A B : Type} (s : A -> B) (r : B -> A) :=
  forall x : A, r (s x) = x.

Class IsEquiv {A B : Type} (f : A -> B) := BuildIsEquiv {
  equiv_inv : B -> A ;
  eisretr : Sect equiv_inv f;
  eissect : Sect f equiv_inv;
  eisadj : forall x : A, eisretr (f x) = ap f (eissect x)
}.

Definition Lift@{i j} (A : Type@{i}) : Type@{j}
  := Eval hnf in let enforce_lt := Type@{i} : Type@{j} in A.

Definition lower {A} : Lift A -> A := fun x => x.

Definition lift2 {A B} (f : forall x : A, B x) : forall x : Lift A, Lift (B (lower x))
  := f.

Global Instance lift_isequiv {A B} (f : A -> B) {H : IsEquiv f} : @ IsEquiv _ _ (lift2 f).
(* Used to be: *)
(* Toplevel input, characters 95-102:
Error:
In environment
A : Type
B : Type
f : A -> B
H : IsEquiv f
The term "lift2 f" has type "Lift A -> Lift B"
while it is expected to have type "Lift A -> ?T0" (cannot instantiate
"?T0" because "x" is not in its scope: available arguments are
"A" "B" "f" "H"). *)
Abort.
