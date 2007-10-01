Axiom succ_pred : forall x : Z, S (P x) == x.
Add Morphism P with signature E ==> E as pred_wd.

Theorem pred_inj : forall x y, P x == P y -> x == y.
Proof.
intros x y H.
setoid_replace x with (S (P x)); [| symmetry; apply succ_pred].
setoid_replace y with (S (P y)); [| symmetry; apply succ_pred].
now rewrite H.
Qed.

Theorem pred_succ : forall x, P (S x) == x.
Proof.
intro x.
apply succ_inj.
now rewrite succ_pred.
Qed.

(* The following tactics are intended for replacing a certain
occurrence of a term t in the goal by (S (P t)) or by (P (S t)).
Unfortunately, this cannot be done by setoid_replace tactic for two
reasons. First, it seems impossible to do rewriting when one side of
the equation in question (succ_pred or pred_succ) is a variable, due to bug 1604.
This does not work even when the predicate is an identifier (e.g.,
when one tries to rewrite (A x) into (A (S (P x)))). Second, the
setoid_rewrite tactic, like the ordinary rewrite tactic, does not
allow specifying the exact occurrence of the term to be rewritten. Now
while not in the setoid context, this occurrence can be specified
using the pattern tactic, it does not work with setoids, since pattern
creates a lambda abstractuion, and setoid_rewrite does not work with
them. *)

Ltac rewrite_succP t set_tac repl thm :=
let x := fresh "x" in
set_tac x t;
setoid_replace x with (repl x); [| symmetry; apply thm];
unfold x; clear x.

Tactic Notation "rewrite_succ_pred" constr(t) :=
rewrite_succP t ltac:(fun x t => (set (x := t))) (fun x => (S (P x))) succ_pred.

Tactic Notation "rewrite_succ_pred" constr(t) "at" integer(k) :=
rewrite_succP t ltac:(fun x t => (set (x := t) in |-* at k)) (fun x => (S (P x))) succ_pred.

Tactic Notation "rewrite_pred_succ" constr(t) :=
rewrite_succP t ltac:(fun x t => (set (x := t))) (fun x => (P (S x))) pred_succ.

Tactic Notation "rewrite_pred_succ" constr(t) "at" integer(k) :=
rewrite_succP t ltac:(fun x t => (set (x := t) in |-* at k)) (fun x => (P (S x))) pred_succ.

(* One can add tactic notations for replacements in assumptions rather
than in the goal. For the reason of many possible variants, the core
of the tactic is factored out. *)

