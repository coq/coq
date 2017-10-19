Require Import TestSuite.admit.
(* Check that inversion of names of mutual inductive fixpoints works *)
(* (cf BZ#1031) *)

Inductive tree : Set :=
| node : nat -> forest -> tree
with forest    : Set :=
| leaf : forest
| cons : tree    -> forest   -> forest
    .
Definition copy_of_compute_size_forest :=
fix copy_of_compute_size_forest (f:forest) : nat :=
  match f with
  | leaf => 1
  | cons t f0 => copy_of_compute_size_forest f0 + copy_of_compute_size_tree t
  end
with copy_of_compute_size_tree (t:tree) : nat :=
  match t with
  | node _ f => 1 + copy_of_compute_size_forest f
  end for copy_of_compute_size_forest
.
Eval simpl in (copy_of_compute_size_forest leaf).


(* Another interesting case: Hrec has to occurrences: one cannot be folded
   back to f while the second can. *)
Parameter g : (nat->nat)->nat->nat->nat.

Definition f (n n':nat) :=
  nat_rec (fun _ => nat -> nat)
    (fun x => x)
    (fun k Hrec => g Hrec (Hrec k))
    n n'.

Goal forall a b, f (S a) b = b.
intros.
simpl.
admit.
Qed. (* Qed will fail if simpl performs eta-expansion *)

(* Yet another example. *)

Require Import List.

Goal forall A B (a:A) l f (i:B), fold_right f i ((a :: l))=i.
simpl.
admit.
Qed. (* Qed will fail if simplification is incorrect (de Bruijn!) *)

(* Check that maximally inserted arguments do not break interpretation
   of references in simpl, vm_compute etc. *)

Arguments fst {A} {B} p.

Goal fst (0,0) = 0.
simpl fst.
Fail set (fst _).
Abort.

Goal fst (0,0) = 0.
vm_compute fst.
Fail set (fst _).
Abort.

Goal let f x := x + 0 in f 0 = 0.
intro.
vm_compute f.
Fail set (f _).
Abort.

(* This is a change wrt 8.4 (waiting to know if it breaks script a lot or not)*)

Goal 0+0=0.
Fail simpl @eq.
Abort.

(* Check reference by notation in simpl *)

Goal 0+0 = 0.
simpl "+".
Fail set (_ + _).
Abort.

(* Check occurrences *)

Record box A := Box { unbox : A }.

Goal unbox _ (unbox _ (unbox _ (Box _ (Box _ (Box _ True))))) =
     unbox _ (unbox _ (unbox _ (Box _ (Box _ (Box _ True))))).
simpl (unbox _ (unbox _ _)) at 1.
match goal with |- True = unbox _ (unbox _ (unbox _ (Box _ (Box _ (Box _ True))))) => idtac end.
Undo 2.
Fail simpl (unbox _ (unbox _ _)) at 5.
simpl (unbox _ (unbox _ _)) at 1 4.
match goal with |- True = unbox _ (Box _ True) => idtac end.
Undo 2.
Fail simpl (unbox _ (unbox _ _)) at 3 4. (* Nested and even overlapping *)
simpl (unbox _ (unbox _ _)) at 2 4.
match goal with |- unbox _ (Box _ True) = unbox _ (Box _ True) => idtac end.
Abort.

(* Check interpretation of ltac variables (was broken in 8.5 beta 1 and 2 *)

Goal 2=1+1.
match goal with |- (_ = ?c) => simpl c end.
match goal with |- 2 = 2 => idtac end. (* Check that it reduced *)
Abort.
