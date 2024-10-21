From Stdlib Require Import ssreflect ssrbool ssrfun.
From Stdlib Require Import ListDef.

Import Nat.

Fixpoint filter A (f : A -> bool) (l:list A) : list A :=
  match l with
  | nil => nil
  | x :: l => if f x then x::(filter A f l) else filter A f l
  end.
Arguments filter {_}.

Definition partition {X : Type}
                     (test : X -> bool)
                     (l : list X)
                   : list X * list X
  := (filter test l, filter (fun x => negb (test x)) l).

Section Fold_Right_Recursor.
  Variables (A : Type) (B : Type).
  Variable f : B -> A -> A.
  Variable a0 : A.

  Fixpoint fold_right (l:list B) : A :=
    match l with
      | nil => a0
      | cons b t => f b (fold_right t)
    end.
End Fold_Right_Recursor.
Arguments fold_right {_ _}.

Definition fold (A B: Type) f l b:= @fold_right B A f b l.

Theorem partition_fst: forall (X : Type)  (test : X -> bool) (l : list X),
                         fold_right andb true (map test (fst (partition test l))) = true.
Proof.
  move => ? test.
  elim => [|x xs IHxs] //.
  case H: eqb (test x) true.  (* <-- anomaly here! *)
Abort.
