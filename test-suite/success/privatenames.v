
Set Warnings "+generated-names".

(* Check that refine policy of redefining previous names make these names private *)

Goal forall x y, x+y=0.
intro x.
refine (fun x => _).
Fail Check x0.
Check x.
Abort.

(* Example from Emilio *)

Goal forall b : False, b = b.
intro b.
refine (let b := I in _).
Fail destruct b0.
Abort.

(* Example from Cyprien *)

Goal True -> True.
Proof.
  refine (fun _ => _).
  Fail exact t.
Abort.

(* Example from Jason *)

Goal False -> False.
intro H.
abstract exact H.
Qed.

(* Variant *)

Goal False -> False.
intro.
Fail abstract exact H.
Abort.

(* Example from Jason *)

Goal False -> False.
intro H.
let H' := H in abstract exact H'. (* Name H' is from Ltac here, so it preserves the privacy *)
Qed.

(* Variant *)

Goal False -> False.
intro.
Fail let H' := H in abstract exact H'.
Abort.

(* Indirectly testing preservation of names by move (derived from Jason) *)

Inductive nat2 := S2 (_ _ : nat2).
Goal forall t : nat2, True.
  intro t.
  let IHt1 := fresh "IHt1" in
  let IHt2 := fresh "IHt2" in
  induction t as [? IHt1 ? IHt2].
  Fail exact IHt1.
Abort.

(* Example on "pose proof" (from Jason) *)

Goal False -> False.
intro; pose proof I as H0.
Fail exact H.
Abort.

(* Testing the approach for which non alpha-renamed quantified names are user-generated *)

Section foo.
Context (b : True).
Goal forall b : False, b = b.
Fail destruct b0.
Abort.

Goal forall b : False, b = b.
now destruct b.
Qed.
End foo.

(* Test stability of "fix" *)

Lemma a : forall n, n = 0.
Proof.
fix 1.
Check a. (* name a is canonical *)
fix 1.
Fail Check a0. (* name a0 is not canonical *)
Set Warnings "-generated-names".
Check a0. (* name a0 exists *)
Set Warnings "+generated-names".
Abort.

(* Test stability of "induction" *)

Lemma a : forall n : nat, n = n.
Proof.
induction n.
- auto.
- Check n. (* name n is canonical *)
  Check IHn. (* name IHn is canonical *)
Abort.

Inductive I := C : I -> I -> I.

Lemma a : forall n : I, n = n.
Proof.
induction n.
Check n1. (* name n1 is canonical *)
Check n2. (* name n2 is canonical *)
apply f_equal2.
+ apply IHn1. (* name IHn1 is canonical *)
+ apply IHn2. (* name IHn2 is canonical *)
Qed.

Lemma b : forall n1 n : I, n = n.
Proof.
induction n.
Fail Check n3. (* expected n1 is now n2 hence not canonical *)
Fail Check IHn1. (* name IHn1 is not canonical, because n1 renamed to n2 *)
Fail Check n2. (* expected n2 is now n3 not canonical *)
Fail Check IHn2. (* name IHn2 is not canonical, because n2 renamed to n3 *)
Set Warnings "-generated-names".
Check n3. (* Check names exist *)
Check IHn1.
Check n2.
Check IHn2.
Set Warnings "+generated-names".
Abort.

Lemma b : forall n2 n : I, n = n.
Proof.
induction n.
Check n1. (* name n1 is not canonical *)
Check IHn1. (* name IHn1 is canonical *)
Fail Check n3. (* expected n2 is now n3 hence not canonical *)
Fail Check IHn2. (* name IHn2 is not canonical, because n2 renamed to n3 *)
Set Warnings "-generated-names".
Check n3.
Check IHn2.
Set Warnings "+generated-names".
Abort.

(* Testing remember *)

Lemma c : 0 = 0.
Proof.
remember 0 as x.
Check Heqx. (* Heqx is canonical *)
Abort.

Lemma c : forall Heqx, Heqx -> 0 = 0.
Proof.
intros.
remember 0 as x.
Fail Check Heqx0. (* Heqx0 is not canonical *)
Abort.
