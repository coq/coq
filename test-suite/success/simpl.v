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


(* Another interesting case: Hrec has two occurrences: one cannot be folded
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
match goal with [ |- g (f a) (f a a) b = b ] => idtac end.
admit.
Qed.

(* Yet another example. *)

Require Import TestSuite.list.

Goal forall A B (a:A) l f (i:B), fold_right f i ((a :: l))=i.
intros.
simpl.
match goal with [ |- f0 a (fold_right f0 i l) = i ] => idtac end.
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

Module FurtherAppliedPrimitiveProjections.
Set Primitive Projections.
Record T := { u : nat -> nat }.
Goal {| u:= fun x => x |}.(u) 0 = 0.
simpl u.
match goal with |- 0 = 0 => idtac end. (* Check that it reduced *)
Abort.
End FurtherAppliedPrimitiveProjections.

Module BugUniverseMutualFix.
Set Universe Polymorphism.
Fixpoint foo1@{u v} (A : Type@{u}) n : Type@{v} := match n with 0 => A | S n => (foo2 A n * A)%type end
with foo2@{u v} (A : Type@{u}) n : Type@{v} := match n with 0 => A | S n => (foo1 A n * A)%type end.
Set Printing Universes.
Definition bar@{u} (A : Type@{u}) n := foo1@{u u} A n.
Goal forall n, bar unit (S n) = unit.
simpl.
Abort.
End BugUniverseMutualFix.

Module PolyUniverses.
(* An example showing that the cache needs to take universes into account *)
Set Universe Polymorphism.
Record cell T S := Cell { hd : T; tl : S }.
Arguments Cell {_ _}.
Arguments hd {_ _}.
Arguments tl {_ _}.
Notation "x ::: y" := (Cell x y) (at level 60).
Definition ilist T n := @Nat.iter n Type (cell T) unit.
Fixpoint imap@{u u0 u1 u2} (T:Type@{u}) (S:Type@{u0}) (f : T -> S) n : ilist@{u2 u1} T n -> ilist@{u0 u1} S n :=
 match n with
 | 0 => fun l => tt
 | S n => fun l => f l.(hd) ::: imap _ _ f _ l.(tl)
 end.
Lemma imap_eq (T S : Type) (f g : T -> S) :
  forall n, forall x, @imap _ _ f n x = @imap _ _ g n x.
induction n. intro; auto.
intros [].
Abort.

End PolyUniverses.

Module WithLet.

Section S.
Variable a : nat.
Let b := 0.
Variable c : nat.
Fixpoint f n :=
  match n with
  | 0 => a + b + c
  | S n => f n
  end.
End S.

Definition f' a c n := f a c n.

Lemma L a c n : f' a c (S n) = f a c (S n).
simpl.
match goal with [ |- f' a c n = f a c n ] => idtac end.
Abort.

End WithLet.

Module WithLetMutual.

Section S.
Context (a : nat) (b := 0) (c : nat).
Fixpoint f n := match n with 0 => a + b + c | S n => g n end
with g n := match n with 0 => a + b + c | S n => f n end.
End S.

Definition f' a c n := f a c n.

Lemma L a c n : f' a c (S n) = f a c (S n).
simpl.
match goal with [ |- g a c n = g a c n ] => idtac end.
Abort.

End WithLetMutual.

Module IotaTrigger1.

Definition a x := match x with true => tt | false => tt end.
Definition b x (y : unit) := a x.
Definition c x := b x tt.
Goal a true = tt. simpl. match goal with [ |- tt = tt ] => idtac end. Abort.
Goal b true = fun _ => tt. simpl. match goal with [ |- b true = _ ] => idtac end. Abort.
Goal c true = tt. simpl. match goal with [ |- tt = tt ] => idtac end. Abort.

End IotaTrigger1.

Module IotaTrigger2.

Definition a x := match x with true => fun _ => tt | false => fun _ => tt end tt.
Definition b x (y : unit) := a x.
Definition c x := b x tt.
Goal a true = tt. simpl. match goal with [ |- tt = tt ] => idtac end. Abort.
Goal b true = fun _ => tt. simpl. match goal with [ |- b true = _ ] => idtac end. Abort.
Goal c true = tt. simpl. match goal with [ |- tt = tt ] => idtac end. Abort.

End IotaTrigger2.

Module IotaTrigger3.

Fixpoint f_fix_fun n := match n with 0 => fun _ : unit => true | S n => f_fix_fun n end.
Definition test_fix_fun n := f_fix_fun n.
Goal test_fix_fun 2 = fun _ => true. simpl. match goal with [ |- (fun _ => true) = _ ] => idtac end. Abort.
Goal forall x, test_fix_fun (S x) = fun _ => true. intro. simpl. match goal with [ |- test_fix_fun x = _ ] => idtac end. Abort.
(* REDUCED *)

Definition test_fix_fun_partial n (x:unit) := f_fix_fun n.
Goal test_fix_fun_partial 2 = fun _ _ => true. simpl. match goal with [ |- test_fix_fun_partial 2 = _ ] => idtac end. Abort.
Goal forall x, test_fix_fun_partial (S x) = fun _ _ => true. intro. simpl. match goal with [ |- test_fix_fun_partial (S x) = _ ] => idtac end. Abort.
(* NOT REDUCED: design choice that it is not enough fully applied to trigger the reduction *)
(* remark: the presence of an inner "fun" does not matter *)

Fixpoint f_fix n := match n with 0 => fun _ : unit => true | S n => f_fix n end.
Definition test_fix n := f_fix n tt.
Goal test_fix 2 = true. simpl. match goal with [ |- test_fix 2 = _ ] => idtac end. Abort.
Goal forall x, test_fix (S x) = true. intro. simpl. match goal with [ |- test_fix (S x) = _ ] => idtac end. Abort.
(* NOT REDUCED: design choice that we couldn't refold to test_fix after reduction *)

Fixpoint f_mutual_fix n := match n with 0 => true | S n => g n end
with g n := match n with 0 => true | S n => f_mutual_fix n end.
Definition test_mutual_fix n := f_mutual_fix n.
Goal test_mutual_fix 2 = true. simpl. match goal with [ |- true = _ ] => idtac end. Abort.
Goal forall x, test_mutual_fix (S x) = true. intro. simpl. match goal with [ |- g x = _ ] => idtac end. Abort.
(* REDUCED: design choice that mutual fixpoints refold to last encapsulating name *)

Definition test_mutual_fix_partial n (x:unit) := f_mutual_fix n.
Goal test_mutual_fix_partial 2 = fun _ => true. simpl. match goal with [ |- test_mutual_fix_partial 2 = _ ] => idtac end. Abort.
Goal forall x, test_mutual_fix_partial (S x) = fun _ => true. intro. simpl. match goal with [ |- test_mutual_fix_partial (S x) = _ ] => idtac end. Abort.
(* NOT REDUCED: design choice that it is not enough fully applied to trigger the reduction *)
(* Moreover, was failing between #17993 and #18243 (see #18239) *)

Fixpoint f_mutual_fix_cut n := match n with 0 => fun _ : unit => true | S n => g_cut n end
with g_cut n := match n with 0 => fun _ : unit => true | S n => f_mutual_fix_cut n end.
Definition test_mutual_fix_cut n := f_mutual_fix_cut n tt.
Goal test_mutual_fix_cut 2 = true. simpl. match goal with [ |- true = _ ] => idtac end. Abort.
Goal forall x, test_mutual_fix_cut (S x) = true. intro. simpl. match goal with [ |- g_cut x tt = _ ] => idtac end. Abort.
(* REDUCED: by consistency with test_mutual_fix, which itself already differs from the case of a unary fix (new behavior from #18243) *)

Definition test_mutual_fix_cut_partial n (x:unit) := f_mutual_fix_cut n x.
Goal test_mutual_fix_cut_partial 2 = fun _ => true. simpl. match goal with [ |- test_mutual_fix_cut_partial 2 = _ ] => idtac end. Abort.
Goal forall x, test_mutual_fix_cut_partial (S x) = fun _ => true. intro. simpl. match goal with [ |- test_mutual_fix_cut_partial (S x) = _ ] => idtac end. Abort.
(* NOT REDUCED: by consistency with test_fix_fun_partial and test_mutual_fix_cut_partial *)
(* Moreover was failing before #18243 (see #18239) *)

Definition f_case n := match n with 0 => fun _ : unit => true | S n => fun _ => true end.
Definition test_case n := f_case n tt.
Goal test_case 2 = true. simpl. match goal with [ |- true = _ ] => idtac end. Abort.
(* REDUCED *)

End IotaTrigger3.

Module Bug4056.

CoInductive stream {A:Type} : Type :=
  | scons: A->stream->stream.

Definition stream_unfold {A} (s: @ stream A) := match s with
| scons a s' => (a, scons a s')
end.

Section A.
  CoFixpoint inf_stream1 (x:nat) (n:nat) :=
    scons n (inf_stream1 x (n+x)).
End A.

Section B.
  Variable (x:nat).
  CoFixpoint inf_stream2 (n:nat) :=
    scons n (inf_stream2 (n+x)).
End B.

Goal (forall x n, stream_unfold (inf_stream1 x n) = stream_unfold (inf_stream2 x n)).
(* simpl was exposing the cofix on the rhs but not the lhs *)
intros. simpl.
match goal with [ |- (n, scons n (inf_stream1 x (n + x))) = (n, scons n (inf_stream2 x (n + x))) ] => idtac end.
Abort.

Section C.
  Variable (x:nat).
  CoFixpoint mut_stream1 (n:nat) := scons n (mut_stream2 (n+x))
  with mut_stream2 (n:nat) :=  scons n (mut_stream1 (n+x)).
End C.

Goal (forall x n, stream_unfold (mut_stream1 x n) = stream_unfold (mut_stream2 x n)).
intros. simpl.
match goal with [ |- (n, scons n (mut_stream2 x (n + x))) = (n, scons n (mut_stream1 x (n + x))) ] => idtac end.
Abort.

Definition inf_stream2_copy n := inf_stream2 n. (* inversible *)
Definition mut_stream2_copy n := mut_stream2 n. (* inversible only towards mut_stream1/mut_stream2 *)

Goal (forall x n, stream_unfold (inf_stream2_copy x n) = stream_unfold (mut_stream2_copy x n)).
intros. simpl.
match goal with [ |- (n, scons n (inf_stream2_copy x (n + x))) = (n, scons n (mut_stream1 x (n + x))) ] => idtac end.
Abort.

End Bug4056.

Module RefoldingOfNeverConstantInArgOfDestructor.

Arguments Nat.add : simpl never.
Goal forall n, (S n + 1) * n = 0.
intros. simpl.
match goal with [ |- n + (n + 1) * n = 0 ] => idtac end.
Abort.

End RefoldingOfNeverConstantInArgOfDestructor.
