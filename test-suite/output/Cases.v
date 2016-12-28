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

Axiom b : bool.
Axiom P : bool -> Prop.
Inductive B : Prop := AC : P b -> B.
Definition f : B -> True.

Proof.
intros [x].
destruct b as [|] ; exact Logic.I.
Defined.

Print f.

(* Was enhancement request #5142 (error message reported on the most
   general return clause heuristic) *)

Inductive gadt : Type -> Type :=
| gadtNat : nat -> gadt nat
| gadtTy : forall T, T -> gadt T.

Fail Definition gadt_id T (x: gadt T) : gadt T :=
  match x with
  | gadtNat n => gadtNat n
  end.

(* A variant of #5142 (see Satrajit Roy's example on coq-club (Oct 17, 2016)) *)

Inductive type:Set:=Nat.
Inductive tbinop:type->type->type->Set:= TPlus : tbinop Nat Nat Nat.
Inductive texp:type->Set:=
 |TNConst:nat->texp Nat
 |TBinop:forall t1 t2 t, tbinop t1 t2 t->texp t1->texp t2->texp t.
Definition typeDenote(t:type):Set:= match t with Nat => nat end.

(* We expect a failure on TBinop *)
Fail Fixpoint texpDenote t (e:texp t):typeDenote t:=
  match e with
  | TNConst n => n
  | TBinop t1 t2 _ b e1 e2 => O
  end.

