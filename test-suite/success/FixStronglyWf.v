(* Examples of fixpoints with loops in erasable subterms *)

(* Loop in erasable local definition *)
Fail Fixpoint foo (n : nat) :=
  let g := foo n in
  0.

(* Loop in erasable branch *)
Fail Fixpoint foo (n : nat) :=
  match 0 with
  | 0 => 0
  | S x => foo n
  end.

(* Loop in inert type *)
Fail Fixpoint foo (n : nat) :=
  forall x : foo n, True.

(* Loop in erasable (and inert) types *)

Fail Fixpoint foo (n : nat) :=
  let _ := fun x : foo n => 0 in True.

Fail Fixpoint foo (n : nat) :=
  (fun _ : foo n = foo n => True) eq_refl.

Fail Fixpoint foo (n : nat) :=
  0 : id (fun _ => nat) (foo n).

(* Competition between an internally bound recursive argument and an
   invalid argument; also checks that it does not depend on order *)

Fail Fixpoint foo p (n : nat) :=
  match n with
  | 0 => 0
  | S x =>
    foo p (id (fun y =>
      match p with
      | true => y
      | false => n
      end) x)
  end.

Fail Fixpoint foo p (n : nat) :=
  match n with
  | 0 => 0
  | S x =>
    foo p (id (fun y =>
      match p with
      | true => n
      | false => y
      end) x)
  end.

(* These one are presumably inoffensive but we continue to reject them *)

Fail Fixpoint foo1 (n : nat) :=
  forall x : foo1 = foo1, True.

Fail Fixpoint foo2 (n : nat) :=
  eq foo2 foo2.

(* Should we allow the following? This is practically uninteresting but a priori ok *)

Fail Fixpoint foo (n : nat) :=
  forall n, forall x : foo n = foo n, True.

Fail Fixpoint foo (n : nat) :=
  forall n, eq (foo n) (foo n).

(* Loop after one step of reduction *)

Fail Fixpoint foo (n : nat) :=
  (fun f p => (fun _ => True) (foo p)) n.

Fail Fixpoint foo (n : nat) :=
  (if true then fun p => if true then True else foo n
   else fun p => True) n.

(* Loop in dead branch *)

Fail Fixpoint foo n :=
  match n with
  | 0 => 0
  | S n =>
      (fix aux n :=
       match n with
       | 0 => foo n
       | S n => aux n
       end) (S n)
  end.

(* Loop in inert erasable subterm *)

Fail Fixpoint g (n:nat) : Prop :=
  (fun x : g n -> True => True) (fun y : g n => I).
