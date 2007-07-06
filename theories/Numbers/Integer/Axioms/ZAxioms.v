Require Export ZDomain.

Module Type IntSignature.
Declare Module Export DomainModule : DomainSignature.
Open Local Scope ZScope.

Parameter Inline O : Z.
Parameter Inline S : Z -> Z.
Parameter Inline P : Z -> Z.

Notation "0" := O : ZScope.

Add Morphism S with signature E ==> E as S_wd.
Add Morphism P with signature E ==> E as P_wd.

Axiom S_inj : forall x y : Z, S x == S y -> x == y.
Axiom S_P : forall x : Z, S (P x) == x.

Axiom induction :
  forall Q : Z -> Prop,
    pred_wd E Q -> Q 0 ->
    (forall x, Q x -> Q (S x)) ->
    (forall x, Q x -> Q (P x)) -> forall x, Q x.

End IntSignature.

Module IntProperties (Export IntModule : IntSignature).
Module Export DomainPropertiesModule := DomainProperties DomainModule.
Open Local Scope ZScope.

Ltac induct n :=
  try intros until n;
  pattern n; apply induction; clear n;
  [unfold NumPrelude.pred_wd;
  let n := fresh "n" in
  let m := fresh "m" in
  let H := fresh "H" in intros n m H; qmorphism n m | | |].

Theorem P_inj : forall x y, P x == P y -> x == y.
Proof.
intros x y H.
setoid_replace x with (S (P x)); [| symmetry; apply S_P].
setoid_replace y with (S (P y)); [| symmetry; apply S_P].
now rewrite H.
Qed.

Theorem P_S : forall x, P (S x) == x.
Proof.
intro x.
apply S_inj.
now rewrite S_P.
Qed.

(* The following tactics are intended for replacing a certain
occurrence of a term t in the goal by (S (P t)) or by (P (S t)).
Unfortunately, this cannot be done by setoid_replace tactic for two
reasons. First, it seems impossible to do rewriting when one side of
the equation in question (S_P or P_S) is a variable, due to bug 1604.
This does not work even when the predicate is an identifier (e.g.,
when one tries to rewrite (Q x) into (Q (S (P x)))). Second, the
setoid_rewrite tactic, like the ordinary rewrite tactic, does not
allow specifying the exact occurrence of the term to be rewritten. Now
while not in the setoid context, this occurrence can be specified
using the pattern tactic, it does not work with setoids, since pattern
creates a lambda abstractuion, and setoid_rewrite does not work with
them. *)

Ltac rewrite_SP t set_tac repl thm :=
let x := fresh "x" in
set_tac x t;
setoid_replace x with (repl x); [| symmetry; apply thm];
unfold x; clear x.

Tactic Notation "rewrite_S_P" constr(t) :=
rewrite_SP t ltac:(fun x t => (set (x := t))) (fun x => (S (P x))) S_P.

Tactic Notation "rewrite_S_P" constr(t) "at" integer(k) :=
rewrite_SP t ltac:(fun x t => (set (x := t) in |-* at k)) (fun x => (S (P x))) S_P.

Tactic Notation "rewrite_P_S" constr(t) :=
rewrite_SP t ltac:(fun x t => (set (x := t))) (fun x => (P (S x))) P_S.

Tactic Notation "rewrite_P_S" constr(t) "at" integer(k) :=
rewrite_SP t ltac:(fun x t => (set (x := t) in |-* at k)) (fun x => (P (S x))) P_S.

(* One can add tactic notations for replacements in assumptions rather
than in the goal. For the reason of many possible variants, the core
of the tactic is factored out. *)

Section Induction.

Variable Q : Z -> Prop.
Hypothesis Q_wd : pred_wd E Q.

Add Morphism Q with signature E ==> iff as Q_morph.
Proof Q_wd.

Theorem induction_n :
  forall n, Q n ->
    (forall m, Q m -> Q (S m)) ->
    (forall m, Q m -> Q (P m)) -> forall m, Q m.
Proof.
induct n.
intros; now apply induction.
intros n IH H1 H2 H3; apply IH; try assumption. apply H3 in H1; now rewrite P_S in H1.
intros n IH H1 H2 H3; apply IH; try assumption. apply H2 in H1; now rewrite S_P in H1.
Qed.

End Induction.

Ltac induct_n k n :=
  try intros until k;
  pattern k; apply induction_n with (n := n); clear k;
  [unfold NumPrelude.pred_wd;
  let n := fresh "n" in
  let m := fresh "m" in
  let H := fresh "H" in intros n m H; qmorphism n m | | |].

End IntProperties.
