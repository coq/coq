
Axiom foo : forall (x y z t : nat), nat.

Arguments foo {_} _ [z] t.
Check (foo 1).
Arguments foo {_} _ {z} {t}.
Fail Arguments foo {_} _ [z] {t}.
Check (foo 1).

Definition foo1 [m] n := n + m.
Check (foo1 1).

Inductive vector {A : Type} : nat -> Type :=
| vnil : vector 0
| vcons : A -> forall {n'}, vector n' -> vector (S n').

Arguments vector A : clear implicits.

Require Import TestSuite.jmeq.

Definition head_subproof A n (v : vector A (S n)) (a : A) n'
    (v' : vector A n') (eqn : S n' = S n) (eqv : JMeq (vcons a v') v) :=
  let H : S n = S n -> n' = n :=
    match eqn in _ = n'' return n'' = S n -> n' = n with
    | eq_refl =>
        fun eqSn' : S n' = S n =>
          let eqn' : n' = n :=
            f_equal (fun e => match e with  0 => n' | S n0 => n0 end) eqSn' in
          eq_ind_r (fun n'' => n'' = n)
            (eq_ind_r
               (fun n' =>
                  forall v', S n' = S n -> JMeq (vcons a v') v -> n = n)
               (fun (v' : vector A n) _ _ => eq_refl) eqn' v'
               eqn eqv)
            eqn'
    end in
  H eq_refl.

Definition head {A : Type} {n : nat} (v : vector A (S n)) :=
  let case_nil (eqn : O = S n) _ :=
    False_rect (vector A n)
      (False_ind False
         (eq_ind O (fun e => match e with O => True | S _ => False end)
            I (S n) eqn)) in
  let case_cons (a : A) n' (v' : vector A n')
        (eqn : eq (S n') (S n)) (eqv : JMeq (vcons a v') v) :=
      eq_rect n' (vector A) v' n
        (head_subproof A n v a n' v' eqn eqv) in
  match
    v as v' in vector _ n' return eq n' (S n) -> JMeq v' v -> vector A n
  with
  | vnil => case_nil
  | @vcons _ a n' v' => case_cons a n' v'
  end (eq_refl (S n)) (JMeq_refl v).

Fixpoint app {A : Type} {n m : nat} (v : vector A n) (w : vector A m) : vector A (n + m) :=
  match v in vector _ n return vector A (n + m) with
    | vnil => w
    | vcons a v' => vcons a (app v' w)
  end.

(* Test sharing information between different hypotheses *)

Parameters (a:_) (b:a=0).

(* These examples were failing due to a lifting wrongly taking let-in into account *)

Definition foo6 (x:=1) : forall {n:nat}, n=n := fun n => eq_refl.

Fixpoint foo7 (x:=1) (n:nat) {p:nat} {struct n} : nat.
Abort.

(* Some example which should succeed with local implicit arguments *)

Inductive A {P:forall m {n}, n=m -> Prop} := C : P 0 eq_refl -> A.
Inductive B (P:forall m {n}, n=m -> Prop) := D : P 0 eq_refl -> B P.

Inductive A' {P:forall m [n], n=m -> Prop} := C' : P 0 eq_refl -> A'.
Inductive A'' [P:forall m {n}, n=m -> Prop] (b : bool):= C'' : P 0 eq_refl -> A'' b.
Inductive A''' (P:forall m [n], n=m -> Prop) (b : bool):= C''' : P 0 eq_refl -> A''' P b.

Definition F (id: forall [A] [x : A], A) := id.
Definition G := let id := (fun [A] (x : A) => x) in id.
Fail Definition G' := let id := (fun {A} (x : A) => x) in id.
