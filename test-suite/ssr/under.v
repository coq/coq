Require Import ssreflect.

Axiom admit : False.

(** Testing over for the 1-var case *)
Lemma test_over_1_1 : forall i : nat, False.
intros.
evar (I : Type); evar (R : Type); evar (x2 : I -> R).
assert (H : i + 2 * i - i = x2 i).
  unfold x2 in *; clear x2;
  unfold R in *; clear R;
  unfold I in *; clear I.
  apply Under_from_eq.
  Fail done.

  over.
  case: admit.
Qed.

Lemma test_over_1_2 : forall i : nat, False.
intros.
evar (I : Type); evar (R : Type); evar (x2 : I -> R).
assert (H : i + 2 * i - i = x2 i).
  unfold x2 in *; clear x2;
  unfold R in *; clear R;
  unfold I in *; clear I.
  apply Under_from_eq.
  Fail done.

  by rewrite over.
  case: admit.
Qed.

(** Testing over for the 2-var case *)

Lemma test_over_2_1 : forall i j : nat, False.
intros.
evar (I : Type); evar (J : Type); evar (R : Type); evar (x2 : I -> J -> R).
assert (H : i + 2 * j - i = x2 i j).
  unfold x2 in *; clear x2;
  unfold R in *; clear R;
  unfold J in *; clear J;
  unfold I in *; clear I.
  apply Under_from_eq.
  Fail done.

  Fail over. (* Bug: doesn't work so we have to make a beta-expansion by hand *)
  rewrite -[i + 2 * j - i]/((fun x y => x + 2 * y - x) i j). (* todo: automate? *)
  over.
  case: admit.
Qed.

Lemma test_over_2_2 : forall i j : nat, False.
intros.
evar (I : Type); evar (J : Type); evar (R : Type); evar (x2 : I -> J -> R).
assert (H : i + 2 * j - i = x2 i j).
  unfold x2 in *; clear x2;
  unfold R in *; clear R;
  unfold J in *; clear J;
  unfold I in *; clear I.
  apply Under_from_eq.
  Fail done.

  rewrite over.
  Fail done. (* Bug: doesn't work so we have to make a beta-expansion by hand *)
  rewrite -[i + 2 * j - i]/((fun x y => x + 2 * y - x) i j). (* todo: automate? *)
  done.
  case: admit.
Qed.

(** Testing under for the 1-var case *)

Inductive body :=
 mk_body : bool -> nat -> nat -> body.

Axiom big : (nat -> body) -> nat.

Axiom eq_big :
 forall P Q F G,
(forall x, P x = Q x :> bool) ->
 (forall x, (P x =true -> F x = G x : Type)) ->
  big (fun x => mk_body (P x) (F x) x) = big (fun toto => mk_body (Q toto) (F toto) toto).

Axiom leb : nat -> nat -> bool.

Axiom addnC : forall p q : nat, p + q = q + p.

Lemma test_under_eq_big :
  (big (fun x => mk_body (leb x 3) (S x + x) x))
 = 3.
Proof.
 Set Debug Ssreflect.
 under i : {1}[in LHS]eq_big.

  { over. }
  { move=> Pi; by rewrite addnC over. }

 rewrite /=.

 case: admit.
Qed.
Unset Debug Ssreflect.

(** 2-var test

Erik: Note that this axiomatization does not faithfully follow that of
mathcomp’s implementation of matrices. We may want to refine this test
once [eq_mx] has been integrated in mathcomp. *)

Axiom I_ : nat -> Type.

(* Inductive matrix (R : Type) (m n : nat) : Type := Matrix (_ : list (I_ m * I_ n * R)). *)
Inductive matrix (R : Type) (m n : nat) : Type := Matrix (_ : I_ m -> I_ n -> R).

Axiom mx_of_fun : forall (R : Type) (m n : nat),
  unit -> (I_ m -> I_ n -> R) -> matrix R m n.

Axiom eq_mx : forall (R : Type) m n (k : unit) (F1 F2 : I_ m -> I_ n -> R),
  (forall foo bar, F1 foo bar = F2 foo bar) ->
  (mx_of_fun R m n k (fun a b => F1 a b)) = (mx_of_fun R m n k (fun c d => F2 c d)).
Arguments eq_mx [R m n k F1] F2 _.

Definition fun_of_mx (R : Type) (m n : nat) (M : matrix R m n) :=
  let: Matrix _ _ _ F := M in F.

Coercion fun_of_mx : matrix >-> Funclass.

Definition addmx : forall (m n : nat) (A B : matrix nat m n), matrix nat m n :=
  fun m n A B => mx_of_fun nat m n tt (fun x y => A x y + B x y).
Arguments addmx [m n].

Lemma test_under_eq_mx (m n : nat) (A B C : matrix nat m n) :
  addmx (addmx A B) C = addmx C (addmx A B).
Proof.
(* Set Debug Ssreflect. *)
under i j : [addmx C _ in RHS]eq_mx.
  by rewrite addnC over.
done.
Qed.
