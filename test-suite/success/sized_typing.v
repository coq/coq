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

Fixpoint leb n m :=
  match n, m with
    | O, _ => true
    | _, O => false
    | S n', S m' => leb n' m'
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

Fixpoint count T (l: list T) :=
  match l with
  | nil => O
  | cons x l => S (count T l)
  end.

Fixpoint append T (l1 l2: list T) :=
  match l1 with
  | nil => l2
  | cons x l => cons x (append T l l2)
  end.

Fixpoint reverse T (l: list T) :=
  match l with
  | nil => nil
  | cons x l' => append T (reverse T l') (cons x nil)
  end.

Fixpoint filter T (f: T -> bool) (l: list T) :=
  match l with
  | nil => nil
  | cons x l' =>
    if (f x) then
      cons x (filter T f l')
    else
      filter T f l'
  end.

Fixpoint quicksort l :=
  match l with
  | nil => nil
  | cons hd tl => append nat
    (quicksort (filter nat (fun x => (leb x hd)) tl))
    (cons hd (quicksort (filter nat (fun x => negb (leb x hd)) tl)))
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

(** Constraint scoping. *)
(** `outer` used to fail since constraints weren't passed around, but not anymore *)

Definition outer :=
  let id x := x in
  fix f n :=
    match n with
    | O => O
    | S n' => f (id n')
    end.

Fail Definition outerSucc :=
  let succ x := S x in
  fix f n :=
    match n with
    | O => O
    | S n' => f (succ n')
    end.

Definition inner :=
  fix f n :=
    let id x := x in
    match n with
    | O => O
    | S n' => f (id n')
    end.

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

(** Definitions that ensure that mutual inductive types have different annotations. *)

Section mutual.

Variables A B: Set.

Inductive tree: Set := node: A -> forest -> tree
with forest: Set :=
  | leaf: B -> forest
  | fcons: tree -> forest -> forest.

(* This has type tree^∞ -> tree^∞. *)
Definition id_tree (tr: tree) := tr.

(* Let fcons: tree^s1 -> forest^s2 -> forest^s2+1.
  Since (id_tree tr): tree^∞, ∞⊑s1, but this doesn't affect the type of useless1,
  which would be forest^ι -> forest^ι, UNLESS s1 = s2, in which case
  its type would end up being forest^ι -> forest^∞. *)
Fixpoint useless1 (fr: forest) :=
  match fr with
  | fcons tr fr => fcons (id_tree tr) (useless1 fr)
  | _ => fr
  end.

(* If useless1 preserves size as we expect it to, this would typecheck.
  If not, then this would fail typechecking,
  since (useless2 fr): forest^∞ and we try to pass it to useless2. *)
Fixpoint useless2 (fr: forest) :=
  match fr with
  | fcons tr fr => fcons tr (useless2 (useless1 fr))
  | _ => fr
  end.

End mutual.

(** A simple mutual fixpoint. *)
Fixpoint even_mutual n :=
  match n with
  | O => true
  | S n' => odd_mutual n'
  end
  with odd_mutual n :=
  match n with
  | O => false
  | S n' => even_mutual n'
  end.

(** A longer example modelling simply-typed lambda calculus with capture-avoiding substitution. *)

Require Import Strings.String.

Module stlc.

Parameter names: list string.
Parameter fresh: True -> string.

Inductive STLCA: Type :=
  | unit: STLCA
  | arr (A b: STLCA): STLCA.

Inductive STLCE: Type :=
  | vare (v: string): STLCE
  | lambdae (v: string) (A: STLCA) (body: STLCE): STLCE
  | appe (e1: STLCE) (e2: STLCE): STLCE.

Fixpoint size (e: STLCE): nat :=
  match e with
  | vare _ => 1
  | lambdae _ _ body => 1 + (size body)
  | appe e1 e2 => 1 + (size e1) + (size e2)
  end.

(* We assume [new] to be unbound in e. *)
Fixpoint freshen (old: string) (new: string) (e: STLCE) :=
  match e with
  | vare n => if (n =? old)%string then vare new else e
  | appe e1 e2 => appe (freshen old new e1) (freshen old new e2)
  | lambdae n A body => lambdae n A (freshen old new body)
  end.

Fixpoint subst (name: string) (v: STLCE) (exp: STLCE) {struct exp} :=
  match exp with
  | vare n => if (n =? name)%string then v else exp
  | appe e1 e2 => appe (subst name v e1) (subst name v e2)
  | lambdae n A body =>
    if (n =? name)%string then exp else
    let n' := fresh I in
    lambdae n' A (subst name v (freshen n n' body))
  end.

End stlc.
