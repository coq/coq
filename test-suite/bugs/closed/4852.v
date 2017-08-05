(** BZ 4852 : unsatisfactory Extraction Implicit for a fixpoint defined via wf *)

Require Import Coq.Lists.List.
Import ListNotations.
Require Import Omega.

Definition wfi_lt := well_founded_induction_type Wf_nat.lt_wf.

Tactic Notation "wfinduction" constr(term) "on" ne_hyp_list(Hs) "as" ident(H) :=
  let R := fresh in
  let E := fresh in
  remember term as R eqn:E;
  revert E; revert Hs;
  induction R as [R H] using wfi_lt;
  intros; subst R.

Hint Rewrite @app_comm_cons @app_assoc @app_length : app_rws.

Ltac solve_nat := autorewrite with app_rws in *; cbn in *; omega.

Notation "| x |" := (length x) (at level 11, no associativity, format "'|' x '|'").

Definition split_acc (ls : list nat) : forall acc1 acc2,
    (|acc1| = |acc2| \/ |acc1| = S (|acc2|)) ->
    { lss : list nat * list nat |
      let '(ls1, ls2) := lss in |ls1++ls2| = |ls++acc1++acc2| /\ (|ls1| = |ls2| \/ |ls1| = S (|ls2|))}.
Proof.
  induction ls as [|a ls IHls]. all:intros acc1 acc2 H.
  { exists (acc1, acc2). cbn. intuition reflexivity. }
  destruct (IHls (a::acc2) acc1) as [[ls1 ls2] (H1 & H2)]. 1:solve_nat.
  exists (ls1, ls2). cbn. intuition solve_nat.
Defined.

Definition join(ls : list nat) : { rls : list nat | |rls| = |ls| }.
Proof.
  wfinduction (|ls|) on ls as IH.
  case (split_acc ls [] []). 1:solve_nat.
  intros (ls1 & ls2) (H1 & H2).
  destruct ls2 as [|a ls2].
  - exists ls1. solve_nat.
  - unshelve eelim (IH _ _ ls1 eq_refl). 1:solve_nat. intros rls1 H3.
    unshelve eelim (IH _ _ ls2 eq_refl). 1:solve_nat. intros rls2 H4.
    exists (a :: rls1 ++ rls2). solve_nat.
Defined.

Require Import ExtrOcamlNatInt.
Extract Inlined Constant length => "List.length".
Extract Inlined Constant app => "List.append".

Extraction Inline wfi_lt.
Extraction Implicit wfi_lt [1 3].
Recursive Extraction join. (* was: Error: An implicit occurs after extraction *)
Extraction TestCompile join.

