Unset Guard Checking.
Set Sized Typing.

(** Some basic arithmetic definitions *)

Definition succ (n: nat) := S n.

Definition pred (n : nat) :=
  match n with
  | O => O
  | S n => n
  end.

Fixpoint plus n m :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.

Fixpoint minus n m :=
  match n with
  | O => O
  | S n' =>
    match m with
    | O => n
    | S m' => minus n' m'
    end
  end.

Fixpoint div x y :=
  match x with
  | O => O
  | S x' => S (div (minus x' y) y)
  end.

Fixpoint mult x y :=
  match x with
  | O => O
  | S x' => plus y (mult x' y)
  end.

Fixpoint isEven n :=
  match n with
  | O => true
  | S O => false
  | S (S n') => isEven n'
  end.

Fixpoint isOdd n :=
  match n with
  | O => false
  | S O => true
  | S (S n') => isOdd n'
  end.

(** Recursive functions on lists. *)

Definition head T default (l: list T) :=
  match l with
  | nil => default
  | cons x _ => x
  end.

Definition tail T (l: list T) :=
  match l with
  | nil => nil
  | cons _ l' => l'
  end.

Fixpoint append T (l1 l2: list T) :=
  match l1 with
  | nil => l2
  | cons x l => cons x (append T l l2)
  end.

Fixpoint reverse T (l: list T) :=
  match l with
  | nil => nil
  | cons x l' => append (reverse l') (cons x nil)
  end.

(** Recursive functions on coinductive streams. *)

CoInductive Stream (T: Set) : Type :=
  Cons: T -> Stream T -> Stream T.

CoFixpoint zip T U z (s1 s2: Stream T) : Stream U :=
  match s1 with
  | Cons _ h1 t1 =>
    match s2 with
    | Cons _ h2 t2 =>
      Cons U (z h1 h2) (zip T U z t1 t2)
    end
  end.

CoFixpoint everyOther T (s : Stream T) :=
  match s with
  | Cons _ _ t1 =>
    match t1 with
    | Cons _ h2 t2 => Cons T h2 (everyOther T t2)
    end
  end.

(** Definitions that fail because recursive arguments cannot have a successor size. *)

(* Terminates, but fails *)
Fail Fixpoint toZero n :=
  match n with
  | O => O
  | S n' => toZero O
  end.

(* Does not terminate and fails *)
Fail Fixpoint loopNat n :=
  match n with
  | O => O
  | S n' => loopNat (S n')
  end.

(* Terminates, but fails. *)
Fail Fixpoint decr n :=
  match n with
  | O => O
  | S O => O
  | S (S n') => decr (S n')
  end.

(** These illustrate the differences in scoping. *)

(* This fails because stage variables outside of a fixpoint
  are all set to infinity when typechecking the fixpoint
  and so the type of [id] is [nat^∞ -> nat^∞]. *)
Fail Definition outer :=
  let id x := x in
  fix f n :=
    match n with
    | O => O
    | S n' => f (id n')
    end.

(* If we don't set the outer stage variables to infinity,
  this nonterminating definition would typecheck. *)
Fail Definition outerSucc :=
  let succ x := S x in
  fix f n :=
    match n with
    | O => O
    | S n' => f (succ n')
    end.

(* This succeeds because [id] is defined inside of the fixpoint. *)
Definition inner :=
  fix f n :=
    let id x := x in
    match n with
    | O => O
    | S n' => f (id n')
    end.

(* As a consequence, this nonterminating definition does not typecheck. *)
Fail Definition innerSucc :=
  fix f n :=
    let succ x := S x in
    match n with
    | O => O
    | S n' => f (succ n')
    end.

(** Large definitions of inductive types requiring delta reduction in fixpoint types *)
(** We ensure that:
  * Each usage of [N] instantiates a different stage annotation;
  * Usages of [N] actually are given stage annotations; and
  * Nested large definitions assign stage annotations to its inner definitions.
 **)

(* Relative *)

Definition rel1 :=
  let N := nat in
  fix f (n: N) :=
    let id (x: N) := x in
    id (S (id n)).

Fail Definition rel2 :=
  let N := nat in
  fix f (n: N) :=
    let succ (x: N) := S x in
    match n with
    | O => O
    | S n' => f (succ n')
    end.

Definition rel2 :=
  let N := nat in
  let NN := (N, N) in
  fix f (n: fst NN) :=
    match n with
    | O => O
    | S n' => f n'
    end.

(* Local *)

Section local.

Let N := nat.
Let NN := (N, N).

Definition var1 :=
  fix f (n: N) :=
    let id (x: N) := x in
    id (S (id n)).

Fail Definition var2 :=
  fix f (n: N) :=
    let succ (x: N) := S x in
    match n with
    | O => O
    | S n' => f (succ n')
    end.

Definition var3 :=
  fix f (n: fst NN) :=
    match n with
    | O => O
    | S n' => f n'
    end.

End local.

(* Global *)

Definition N := nat.
Definition NN := (N, N).

Definition const1 :=
  fix f (n: N) :=
    let id (x: N) := x in
    id (S (id n)).

Fail Definition const2 :=
  fix f (n: N) :=
    let succ (x: N) := S x in
    match n with
    | O => O
    | S n' => f (succ n')
    end.

Definition const3 :=
  fix f (n: fst NN) :=
    match n with
    | O => O
    | S n' => f n'
    end.

(** Definitions that illustrate size-preservation. *)

(* [Definition] itself does not preserve size of types. *)
Definition id1 (x: nat) := x.
Fail Fixpoint f (n: nat) :=
  match n with
  | O => O
  | S n' => f (id1 n')
  end.

(* [Fixpoint] does preserve size of types. *)
Fixpoint id2 (x: nat) := x.
Fixpoint g (n: nat) :=
  match n with
  | O => O
  | S n' => g (id2 n')
  end.

(* [Definition] defining a fixpoint also preserves size. *)
Definition id3 := fix id' (x: nat) := x.
Fixpoint h (n: nat) :=
  match n with
  | O => O
  | S n' => h (id3 n')
  end.

(* Local definitions preserve size as well when expected. *)
Section localSize.
Let id1 (x: nat) := x.
Let id2 := fix id' (x: nat) := x.
Fail Fixpoint j (n: nat) :=
  match n with
  | O => O
  | S n' => j (id1 n')
  end.
Fixpoint k (n: nat) :=
  match n with
  | O => O
  | S n' => k (id2 n')
  end.
End localSize.
