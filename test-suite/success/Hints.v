(* Checks syntax of Hints commands *)
(* Checks that qualified names are accepted *)

(* New-style syntax *)
Hint Resolve eq_refl: core arith.
Hint Immediate eq_trans.
Hint Unfold eq_sym: core.
Hint Constructors eq: foo bar.
Hint Extern 3 (_ = _) => apply eq_refl: foo bar.

(* Old-style syntax *)
Hint Resolve eq_refl eq_sym.
Hint Resolve eq_refl eq_sym: foo.
Hint Immediate eq_refl eq_sym.
Hint Immediate eq_refl eq_sym: foo.
Hint Unfold fst eq_sym.
Hint Unfold fst eq_sym: foo.

(* Checks that local names are accepted *)
Section A.
  Remark Refl : forall (A : Set) (x : A), x = x.
  Proof. exact @eq_refl. Defined.
  Definition Sym := eq_sym.
  Let Trans := eq_trans.

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
