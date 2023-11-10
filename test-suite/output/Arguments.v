(* coq-prog-args: ("-top" "Arguments") *)
Arguments Nat.sub n m : simpl nomatch.
About Nat.sub.
Arguments Nat.sub n / m : simpl nomatch.
About Nat.sub.
Arguments Nat.sub !n / m : simpl nomatch.
About Nat.sub.
Arguments Nat.sub !n !m /.
About Nat.sub.
Arguments Nat.sub !n !m.
About Nat.sub.
Definition pf (D1 C1 : Type) (f : D1 -> C1) (D2 C2 : Type) (g : D2 -> C2) := 
  fun x => (f (fst x), g (snd x)).
Declare Scope foo_scope.
Declare Scope bar_scope.
Delimit Scope foo_scope with F.
Arguments pf {D1%_F C1%_type} f [D2 C2] g x : simpl never.
About pf.
Definition fcomp A B C f (g : A -> B) (x : A) : C := f (g x).
Arguments fcomp {_ _ _}%_type_scope f g x /.
About fcomp.
Definition volatile := fun x : nat => x.
Arguments volatile / _.
About volatile.
Set Implicit Arguments.
Section S1.
Variable T1 : Type.
Section S2.
Variable T2 : Type.
Fixpoint f (x : T1) (y : T2) n (v : unit) m {struct n} : nat :=
  match n, m with
  | 0,_ => 0
  | S _, 0 => n
  | S n', S m' => f x y n' v m' end.
About f.
Global Arguments f x y !n !v !m.
About f.
End S2.
About f.
End S1.
About f.
Eval cbn in forall v, f 0 0 5 v 3 = 2.
Eval cbn in f 0 0 5 tt 3 = 2.
Arguments f : clear implicits and scopes.
About f.
Record r := { pi :> nat -> bool -> unit }.
Notation "$" := 3 (only parsing) : foo_scope.
Notation "$" := true (only parsing) : bar_scope.
Delimit Scope bar_scope with B.
Arguments pi _ _%_F _%_B.
Check (forall w : r, pi w $ $ = tt).
Fail Check (forall w : r, w $ $ = tt).
Axiom w : r.
Arguments w  x%_F y%_B : extra scopes.
Check (w $ $ = tt).
Fail Arguments w  _%_F _%_B.

Definition volatilematch (n : nat) :=
  match n with
  | O => O
  | S p => p
  end.

Arguments volatilematch / n : simpl nomatch.
About volatilematch.
Eval simpl in fun n => volatilematch n.

Module Formatting.

Parameter A : Type.
Parameter f : forall (xxxxxxxxxxxxxx : A) (xxxxxxxxxxxxxx' : nat) (xxxxxxxxxxxxxx'' : nat) (xxxxxxxxxxxxxx''' : nat), xxxxxxxxxxxxxx' + xxxxxxxxxxxxxx' + xxxxxxxxxxxxxx'' = 0.
Print f.

End Formatting.
