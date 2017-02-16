(* Cases with let-in in constructors types *)

Inductive t : Set :=
    k : let x := t in x -> x.

Print t_rect.

Record TT : Type := CTT { f1 := 0 : nat; f2: nat; f3 : f1=f1 }.

Eval cbv in fun d:TT => match d return 0 = 0 with CTT a _ b => b end.
Eval lazy in fun d:TT => match d return 0 = 0 with CTT a _ b => b end.

(* Do not contract nested patterns with dependent return type *)
(* see bug #1699 *)

Require Import Arith.

Definition proj (x y:nat) (P:nat -> Type) (def:P x) (prf:P y) : P y :=
  match eq_nat_dec x y return P y with
  | left eqprf =>
    match eqprf in (_ = z) return (P z) with
    | refl_equal => def
    end
  | _ => prf
 end.

Print proj.

(* Use notations even below aliases *)

Require Import List.

Fixpoint foo (A:Type) (l:list A) : option A :=
  match l with
  | nil => None
  | x0 :: nil => Some x0
  | x0 :: (x1 :: xs) as l0 => foo A l0
  end.

Print foo.

(* Accept and use notation with binded parameters *)

Inductive I (A: Type) : Type := C : A -> I A.
Notation "x <: T" := (C T x) (at level 38).

Definition uncast A (x : I A) :=
match x with
 | x <: _ => x
end.

Print uncast.

(* Do not duplicate the matched term *)

Axiom A : nat -> bool.

Definition foo' :=
  match A 0 with
    | true => true
    | x => x
  end.

Print foo'.

(* Was bug #3293 (eta-expansion at "match" printing time was failing because
   of let-in's interpreted as being part of the expansion)  *)

Variable b : bool.
Variable P : bool -> Prop.
Inductive B : Prop := AC : P b -> B.
Definition f : B -> True.

Proof.
intros [].
destruct b as [|] ; intros _ ; exact Logic.I.
Defined.

Print f.

(* Test notations with local definitions in constructors *)

Inductive J := D : forall n m, let p := n+m in nat -> J.
Notation "{{ n , m , q }}" := (D n m q).

Check fun x : J => let '{{n, m, _}} := x in n + m.
Check fun x : J => let '{{n, m, p}} := x in n + m + p.

(* Cannot use the notation because of the dependency in p *)

Check fun x => let '(D n m p q) := x in n+m+p+q.

(* This used to succeed, being interpreted as "let '{{n, m, p}} := ..." *)

Fail Check fun x : J => let '{{n, m, _}} p := x in n + m + p.
