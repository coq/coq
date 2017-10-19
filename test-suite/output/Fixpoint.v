Require Import List.

Check
  (fix F (A B : Set) (f : A -> B) (l : list A) {struct l} :
   list B := match l with
             | nil => nil
             | a :: l => f a :: F _ _ f l
             end).

(* V8 printing of this term used to failed in V8.0 and V8.0pl1 (cf BZ#860) *)
Check
  let fix f (m : nat) : nat :=
    match m with
    | O => 0
    | S m' => f m'
    end
  in f 0.

Require Import ZArith_base Omega.
Open Scope Z_scope.

Inductive even: Z -> Prop :=
| even_base: even 0
| even_succ: forall n, odd (n - 1) -> even n
with odd: Z -> Prop :=
| odd_succ: forall n, even (n - 1) -> odd n.

(* Check printing of fix *)
Ltac f id1 id2 := fix id1 2 with (id2 n (H:odd n) {struct H} : n >= 1).
Print Ltac f.

(* Incidentally check use of fix in proofs *)
Lemma even_pos_odd_pos: forall n, even n -> n >= 0.
Proof.
fix even_pos_odd_pos 2 with (odd_pos_even_pos n (H:odd n) {struct H} : n >= 1).
 intros.
 destruct H.
   omega.
   apply odd_pos_even_pos in H.
   omega.
 intros.
 destruct H.
  apply even_pos_odd_pos in H.
  omega.
Qed.

CoInductive Inf := S { projS : Inf }.
Definition expand_Inf (x : Inf) := S (projS x).
CoFixpoint inf := S inf.
Eval compute in inf.
