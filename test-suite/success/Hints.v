(* Checks syntax of Hints commands *)
(* Checks that qualified names are accepted *)

(* New-style syntax *)
Hint Resolve refl_equal: core arith.
Hint Immediate trans_equal.
Hint Unfold sym_equal: core.
Hint Constructors eq: foo bar.
Hint Extern 3 (_ = _) => apply refl_equal: foo bar.

(* Old-style syntax *)
Hint Resolve refl_equal sym_equal.
Hint Resolve refl_equal sym_equal: foo.
Hint Immediate refl_equal sym_equal.
Hint Immediate refl_equal sym_equal: foo.
Hint Unfold fst sym_equal.
Hint Unfold fst sym_equal: foo.

(* What's this stranged syntax ? *)
Hint Destruct h6 := 4 Conclusion (_ <= _) => fun H => apply H.
Hint Destruct h7 := 4 Discardable Hypothesis (_ <= _) => fun H => apply H.
Hint Destruct h8 := 4 Hypothesis (_ <= _) => fun H => apply H.

(* Checks that local names are accepted *)
Section A.
  Remark Refl : forall (A : Set) (x : A), x = x.
  Proof. exact @refl_equal. Defined.
  Definition Sym := sym_equal.
  Let Trans := trans_equal.

  Hint Resolve Refl: foo.
  Hint Resolve Sym: bar.
  Hint Resolve Trans: foo2.

  Hint Immediate Refl.
  Hint Immediate Sym.
  Hint Immediate Trans.

  Hint Unfold Refl.
  Hint Unfold Sym.
  Hint Unfold Trans.

  Hint Resolve Sym Trans Refl.
  Hint Immediate Sym Trans Refl.
  Hint Unfold Sym Trans Refl.

End A.

Axiom a : forall n, n=0 <-> n<=0.

Hint Resolve -> a.
Goal forall n, n=0 -> n<=0.
auto.
Qed.


(* This example comes from Chlipala's ltamer *)
(* It used to fail from r12902 to r13112 since type_of started to call *)
(* e_cumul (instead of conv_leq) which was not able to unify "?id" and *)
(* "(fun x => x) ?id" *)

Notation "e :? pf" := (eq_rect _ (fun X : Set => X) e _ pf)
  (no associativity, at level 90).

Axiom cast_coalesce :
  forall (T1 T2 T3 : Set) (e : T1) (pf1 : T1 = T2) (pf2 : T2 = T3),
  ((e :? pf1) :? pf2) = (e :? trans_eq pf1 pf2).

Hint Rewrite cast_coalesce : ltamer.
