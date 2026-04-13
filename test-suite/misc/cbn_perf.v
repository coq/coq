(* -*- mode: coq; coq-prog-args: ("-allow-rewrite-rules") -*- *)

(* Performance probes for the closure-based [cbn] implementation.

   Each block below isolates one performance hazard from [ppedrot-cbn.md].
   The [Instructions] prefix records a machine-independent-ish instruction
   count in the test log.  The parameter sweeps are deliberately small enough
   for the success suite, but they vary the dimensions that should distinguish
   the desired complexity from the bad one called out in the review. *)

Ltac mk_nat n :=
  lazymatch n with
  | O => constr:(O)
  | S ?n' => let t := mk_nat n' in constr:(S t)
  end.

Ltac mk_nat_fun n :=
  lazymatch n with
  | O => constr:(fun x : nat => x)
  | S ?n' =>
    let f := mk_nat_fun n' in
    constr:(fun x : nat => S (f x))
  end.

Ltac setup_nat_goal t := enough (t = O) by exact I.

(* 1. Deep beta/zeta chains where a large argument is threaded but never
      inspected.  Desired scaling is mainly in [fuel]; repeated eager
      substitution/lifting shows up as dependence on [arg_size * fuel]. *)
Fixpoint beta_zeta_chain (fuel : nat) (x : nat) : nat :=
  match fuel with
  | O => O
  | S fuel' => (fun y : nat => let z := y in beta_zeta_chain fuel' z) x
  end.

Goal True.
Proof.
  let big := mk_nat 50 in setup_nat_goal constr:(beta_zeta_chain 20 big).
  Instructions cbn.
Abort.

Goal True.
Proof.
  let big := mk_nat 100 in setup_nat_goal constr:(beta_zeta_chain 20 big).
  Instructions cbn.
Abort.

Goal True.
Proof.
  let big := mk_nat 100 in setup_nat_goal constr:(beta_zeta_chain 40 big).
  Instructions cbn.
Abort.

(* 2. Recursive fixpoints carrying a large invariant parameter.  The review
      predicts bad behaviour when refolding forces that parameter at each
      recursive step, i.e. roughly [param_size * fuel]. *)
Fixpoint carry_invariant (big fuel : nat) : nat :=
  match fuel with
  | O => O
  | S fuel' => carry_invariant big fuel'
  end.

Goal True.
Proof.
  let big := mk_nat 50 in setup_nat_goal constr:(carry_invariant big 30).
  Instructions cbn.
Abort.

Goal True.
Proof.
  let big := mk_nat 100 in setup_nat_goal constr:(carry_invariant big 30).
  Instructions cbn.
Abort.

Goal True.
Proof.
  let big := mk_nat 100 in setup_nat_goal constr:(carry_invariant big 60).
  Instructions cbn.
Abort.

CoInductive stream : Set :=
| scons : nat -> stream -> stream.

CoFixpoint cofix_carry (big : nat) : stream := scons O (cofix_carry big).

Fixpoint nth_stream (fuel : nat) (s : stream) : nat :=
  match fuel with
  | O => match s with scons n _ => n end
  | S fuel' => match s with scons _ tail => nth_stream fuel' tail end
  end.

Goal True.
Proof.
  let big := mk_nat 50 in setup_nat_goal constr:(nth_stream 30 (cofix_carry big)).
  Instructions cbn.
Abort.

Goal True.
Proof.
  let big := mk_nat 100 in setup_nat_goal constr:(nth_stream 30 (cofix_carry big)).
  Instructions cbn.
Abort.

(* 3. Equality/progress checks on delayed closures.  [simpl nomatch] exercises
      the path that compares pre- and post-unfolding states to decide whether
      progress was made.  Re-forcing an unused large parameter gives the same
      [param_size * fuel] signature. *)
Fixpoint nomatch_progress (fuel : nat) (big : nat) (b : bool) : bool :=
  match fuel with
  | O => if b then true else false
  | S fuel' => nomatch_progress fuel' big b
  end.
Arguments nomatch_progress : simpl nomatch.

Goal True.
Proof.
  let big := mk_nat 50 in
  enough (forall b : bool, nomatch_progress 30 big b = b) by exact I.
  Instructions cbn.
Abort.

Goal True.
Proof.
  let big := mk_nat 100 in
  enough (forall b : bool, nomatch_progress 30 big b = b) by exact I.
  Instructions cbn.
Abort.

Goal True.
Proof.
  let big := mk_nat 100 in
  enough (forall b : bool, nomatch_progress 60 big b = b) by exact I.
  Instructions cbn.
Abort.

(* 4. Recursion over constructors with unused fields.  The payloads contain a
      delayed substitution for [x]; [walk] only follows tails.  Internal stack
      zipping that materializes constructor fields makes the instruction count
      depend on [payload_size * length]. *)
Inductive cell : Set :=
| stop : cell
| node : nat -> cell -> cell.

Fixpoint walk (c : cell) : nat :=
  match c with
  | stop => O
  | node _ tail => walk tail
  end.

Ltac mk_cell_fun len payload_size :=
  lazymatch len with
  | O => constr:(fun x : nat => stop)
  | S ?len' =>
    let payload := mk_nat_fun payload_size in
    let tail := mk_cell_fun len' payload_size in
    constr:(fun x : nat => node (payload x) (tail x))
  end.

Goal True.
Proof.
  let big := mk_nat 20 in
  let c := mk_cell_fun 20 20 in
  setup_nat_goal constr:(walk (c big)).
  Instructions cbn.
Abort.

Goal True.
Proof.
  let big := mk_nat 20 in
  let c := mk_cell_fun 20 40 in
  setup_nat_goal constr:(walk (c big)).
  Instructions cbn.
Abort.

Goal True.
Proof.
  let big := mk_nat 20 in
  let c := mk_cell_fun 40 40 in
  setup_nat_goal constr:(walk (c big)).
  Instructions cbn.
Abort.

(* 5. Strong [cbn] over stuck case/fix structures with delayed components.
      Failed refolding should not first force a raw structure and then traverse
      the original delayed components again. *)
Definition stuck_case (branch x : nat) : nat :=
  (fun y : nat => match x with O => y | S _ => y end) branch.

Goal True.
Proof.
  let branch := mk_nat 50 in
  enough (forall x : nat, stuck_case branch x = stuck_case branch x) by exact I.
  Instructions cbn.
Abort.

Goal True.
Proof.
  let branch := mk_nat 100 in
  enough (forall x : nat, stuck_case branch x = stuck_case branch x) by exact I.
  Instructions cbn.
Abort.

Goal True.
Proof.
  let branch := mk_nat 200 in
  enough (forall x : nat, stuck_case branch x = stuck_case branch x) by exact I.
  Instructions cbn.
Abort.

Goal True.
Proof.
  let branch := mk_nat 50 in
  enough (((fun y : nat =>
              (fix stuck_fix (n : nat) : nat :=
                 match n with O => y | S n' => stuck_fix n' end)) branch)
          = ((fun y : nat =>
                (fix stuck_fix (n : nat) : nat :=
                   match n with O => y | S n' => stuck_fix n' end)) branch)) by exact I.
  Instructions cbn.
Abort.

Goal True.
Proof.
  let branch := mk_nat 100 in
  enough (((fun y : nat =>
              (fix stuck_fix (n : nat) : nat :=
                 match n with O => y | S n' => stuck_fix n' end)) branch)
          = ((fun y : nat =>
                (fix stuck_fix (n : nat) : nat :=
                   match n with O => y | S n' => stuck_fix n' end)) branch)) by exact I.
  Instructions cbn.
Abort.

(* 6. Rewrite-rule reduction still forces candidate arguments eagerly.  The
      first rule fails and the second succeeds, so a delayed [S big] argument
      is a direct probe of the eager matching path. *)
#[unfold_fix] Symbol rw_head : nat -> nat.
Rewrite Rules rw_head_rew :=
| rw_head O => O
| rw_head (S ?n) => O.

Goal True.
Proof.
  let big := mk_nat 50 in setup_nat_goal constr:((fun y : nat => rw_head y) (S big)).
  Instructions cbn.
Abort.

Goal True.
Proof.
  let big := mk_nat 100 in setup_nat_goal constr:((fun y : nat => rw_head y) (S big)).
  Instructions cbn.
Abort.

Goal True.
Proof.
  let big := mk_nat 200 in setup_nat_goal constr:((fun y : nat => rw_head y) (S big)).
  Instructions cbn.
Abort.

(* 7. Local definition unfolding under binders.  The local let is outside the
      products but used below them; eager lifting traverses the large body when
      the local definition is unfolded in that deeper context. *)
Goal True.
Proof.
  let big := mk_nat 100 in
  enough (let local_big := big in forall a b c d : nat,
    (match local_big with O => O | S _ => O end) = O) by exact I.
  Instructions cbn.
Abort.

Goal True.
Proof.
  let big := mk_nat 100 in
  enough (let local_big := big in forall a b c d : nat,
    (match local_big with O => O | S _ => O end) +
    (match local_big with O => O | S _ => O end) = O) by exact I.
  Instructions cbn.
Abort.

Goal True.
Proof.
  let big := mk_nat 200 in
  enough (let local_big := big in forall a b c d : nat,
    (match local_big with O => O | S _ => O end) +
    (match local_big with O => O | S _ => O end) = O) by exact I.
  Instructions cbn.
Abort.
