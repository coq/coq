(* Cases with let-in in constructors types *)

Unset Printing Allow Match Default Clause.

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

(* Test notations with local definitions in constructors *)

Inductive J := D : forall n m, let p := n+m in nat -> J.
Notation "{{ n , m , q }}" := (D n m q).

Check fun x : J => let '{{n, m, _}} := x in n + m.
Check fun x : J => let '{{n, m, p}} := x in n + m + p.

(* Cannot use the notation because of the dependency in p *)

Check fun x => let '(D n m p q) := x in n+m+p+q.

(* This used to succeed, being interpreted as "let '{{n, m, p}} := ..." *)

Fail Check fun x : J => let '{{n, m, _}} p := x in n + m + p.

(* Test use of idents bound to ltac names in a "match" *)

Lemma lem1 : forall k, k=k :>nat * nat.
let x := fresh "aa" in
let y := fresh "bb" in
let z := fresh "cc" in
let k := fresh "dd" in
refine (fun k : nat * nat => match k as x return x = x with (y,z) => eq_refl end).
Qed.
Print lem1.

Lemma lem2 : forall k, k=k :> bool.
let x := fresh "aa" in
let y := fresh "bb" in
let z := fresh "cc" in
let k := fresh "dd" in
refine (fun k => if k as x return x = x then eq_refl else eq_refl).
Qed.
Print lem2.

Lemma lem3 : forall k, k=k :>nat * nat.
let x := fresh "aa" in
let y := fresh "bb" in
let z := fresh "cc" in
let k := fresh "dd" in
refine (fun k : nat * nat => let (y,z) as x return x = x := k in eq_refl).
Qed.
Print lem3.

Lemma lem4 x : x+0=0.
match goal with |- ?y = _ => pose (match y with 0 => 0 | S n => 0 end) end.
match goal with |- ?y = _ => pose (match y as y with 0 => 0 | S n => 0 end) end.
match goal with |- ?y = _ => pose (match y as y return y=y with 0 => eq_refl | S n => eq_refl end) end.
match goal with |- ?y = _ => pose (match y return y=y with 0 => eq_refl | S n => eq_refl end) end.
match goal with |- ?y + _ = _ => pose (match y with 0 => 0 | S n => 0 end) end.
match goal with |- ?y + _ = _ => pose (match y as y with 0 => 0 | S n => 0 end) end.
match goal with |- ?y + _ = _ => pose (match y as y return y=y with 0 => eq_refl | S n => eq_refl end) end.
match goal with |- ?y + _ = _ => pose (match y return y=y with 0 => eq_refl | S n => eq_refl end) end.
Show.
Abort.

Lemma lem5 (p:nat) : eq_refl p = eq_refl p.
let y := fresh "n" in (* Checking that y is hidden *)
  let z := fresh "e" in (* Checking that z is hidden *)
  match goal with
  |- ?y = _ => pose (match y as y in _ = z return y=y /\ z=z with eq_refl => conj eq_refl eq_refl end)
  end.
let y := fresh "n" in
  let z := fresh "e" in
  match goal with
  |- ?y = _ => pose (match y in _ = z return y=y /\ z=z with eq_refl => conj eq_refl eq_refl end)
  end.
let y := fresh "n" in
  let z := fresh "e" in
  match goal with
  |- eq_refl ?y = _ => pose (match eq_refl y in _ = z return y=y /\ z=z with eq_refl => conj eq_refl eq_refl end)
  end.
let p := fresh "p" in
  let z := fresh "e" in
  match goal with
  |- eq_refl ?p = _ => pose (match eq_refl p in _ = z return p=p /\ z=z with eq_refl => conj eq_refl eq_refl end)
  end.
Show.

Set Printing Allow Match Default Clause.

(***************************************************)
(* Testing strategy for factorizing cases branches *)

(* Factorization + default clause *)
Check fun x => match x with Eq => 1 | _ => 0 end.

(* No factorization *)
Unset Printing Factorizable Match Patterns.
Check fun x => match x with Eq => 1 | _ => 0 end.
Set Printing Factorizable Match Patterns.

(* Factorization but no default clause *)
Unset Printing Allow Match Default Clause.
Check fun x => match x with Eq => 1 | _ => 0 end.
Set Printing Allow Match Default Clause.

(* No factorization in printing all mode *)
Set Printing All.
Check fun x => match x with Eq => 1 | _ => 0 end.
Unset Printing All.

(* Several clauses *)
Inductive K := a1|a2|a3|a4|a5|a6.
Check fun x => match x with a3 | a4 => 3 | _ => 2 end.
Check fun x => match x with a3 => 3 | a2 | a1 => 4 | _ => 2 end.
Check fun x => match x with a4 => 3 | a2 | a1 => 4 | _ => 2 end.
Check fun x => match x with a3 | a4 | a1 => 3 | _ => 2 end.

(* Test redundant clause within a disjunctive pattern *)
Fail Check fun n m => match n, m with 0, 0 | _, S _ | S 0, _ | S (S _ | _), _ => false end.
