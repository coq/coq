(** * One-Step Reduction *)
(** We have the following criteria:

   - Performance Criterion: 1-step delta on k constants should
     Õ(output term size)

   - Performance Criterion: 1-step iota should be Õ(output term size)

   - Performance Criterion: 1-step beta on k arguments of the same
     application node where each argument is mentioned multiple times
     should be Õ(input term size + output term size) *)

(** These are quite hard to benchmark.  Ultimately this is because Coq
    doesn't expose a satisfactory one-step reduction. (But maybe you
    claim the thing to do is to just bench the version that we can
    hack up in Coq, even when we know most of the time isn't spent in
    the single step of reduction?) I think it's hard to construct them
    in a way where you're actually benching the single step. If we do
    it via Ltac match + constr hacks, I expect we incur overhead in
    retypechecking and Ltac matching (I suppose I might be wrong, but
    we'd have to be dealing with truly enormous terms before we expect
    one-step reduction to take more than 0.0004 seconds (Coq can only
    measure down to 0.001). Alternatively, we could do a non-one-step
    reduction when there's only one step to do, but it's not clear to
    me to what extent this is benching what we want to
    bench. Alternatively we could try to bench a conversion problem
    where there's just one step of reduction to do, but again I think
    we'll end up just measuring the conversation overhead. *)

Notation "'subst!' v 'for' x 'in' f" := (match v with x => f end) (only parsing, at level 200).

Ltac uconstr_beta1 term :=
  lazymatch term with
  | ((fun x => ?f) ?v) => uconstr:(subst! v for x in f)
  end.

Ltac uconstr_zeta1 term :=
  lazymatch term with
  | (let x := ?v in ?f) => uconstr:(subst! v for x in f)
  end.

Ltac beta1 term :=
  lazymatch term with
  | ((fun x => ?f) ?v) => constr:(subst! v for x in f)
  end.

Ltac zeta1 term :=
  lazymatch term with
  | (let x := ?v in ?f) => constr:(subst! v for x in f)
  end.

(** The easiest thing to do is to check conversion problems, and check
    full β/ι/ζ/δ in cases where there's only one step to do. *)

(** We can construct a term that is expensive to typecheck, and use it
    in places where we want to see whether or not we're incuring
    retypechecking. *)

Fixpoint fact (n : nat) := match n with 0 => 1 | S n' => n * fact n' end.
Fixpoint walk (n : nat) : unit := match n with 0 => tt | S n => walk n end.
Definition skip (n : nat) : unit := tt.
Inductive value := the (A : Type) (_ : A).
Arguments the : clear implicits.
Notation slown n := (the (walk (fact n) = tt) (eq_refl tt)) (only parsing).
Time Definition slow := slown 9.
(* Finished transaction in 1.069 secs (1.052u,0.016s) (successful) *)
Notation fastn n := (the (skip (fact n) = tt) (eq_refl tt)) (only parsing).
Definition fast := fastn 9.
Axiom Ax_fst : forall {A B}, A * B -> A.
Axiom Ax_snd : forall {A B}, A * B -> B.
Fixpoint big_tree {A} (v : A) (n : nat) : A
  := match n with
     | 0 => Ax_fst (v, v)
     | S n => big_tree (Ax_fst (v, v)) n
     end.
Definition big_slow (n : nat) := Eval cbv [big_tree] in big_tree slow n.
Definition big_fast (n : nat) := Eval cbv [big_tree] in big_tree fast n.
(** Tell conversion to unfold [slow] and [fast] early, so that we
    don't run the risk of trying to unfold [fact] during conversion
    when we don't want to. *)
Strategy -10 [slow fast].

Ltac test_slow with_abstract n :=
  optimize_heap;
  let v := (eval cbv [big_slow] in (big_slow n)) in
  restart_timer;
  let v2 := (eval cbv delta [slow] in v) in
  finish_timing ("Tactic call δ-1-slow");
  time "unify-slow" unify v v2;
  lazymatch with_abstract with
  | true => let __ := constr:(ltac:(time "abstract-unify-slow" abstract exact_no_check (eq_refl v)) : v = v2) in
            idtac
  | false => idtac
  end.

Ltac test_fast with_abstract n :=
  optimize_heap;
  let v := (eval cbv [big_fast] in (big_fast n)) in
  restart_timer;
  let v2 := (eval cbv delta [fast] in v) in
  finish_timing ("Tactic call δ-1-fast");
  time "unify-fast" unify v v2;
  lazymatch with_abstract with
  | true => let __ := constr:(ltac:(time "abstract-unify-fast" abstract exact_no_check (eq_refl v)) : v = v2) in
            idtac
  | false => idtac
  end.
(* Goal True. *)
(*   idtac 1; test_slow true 1; test_fast true 1; *)
(*     idtac 2; test_slow true 2; test_fast true 2; *)
(*       idtac 14; test_slow false 14; test_fast false 14; *)
(*         idtac 15; test_slow false 15; test_fast false 15. *)
(* Abort. *)
(* 1
Tactic call δ-1-slow ran for 0. secs (0.u,0.s)
Tactic call unify-slow ran for 0. secs (0.u,0.s) (success)
Tactic call abstract-unify-slow ran for 2.003 secs (2.003u,0.s) (success)
Tactic call δ-1-fast ran for 0. secs (0.u,0.s)
Tactic call unify-fast ran for 0. secs (0.u,0.s) (success)
Tactic call abstract-unify-fast ran for 0. secs (0.u,0.s) (success)
2
Tactic call δ-1-slow ran for 0. secs (0.u,0.s)
Tactic call unify-slow ran for 0. secs (0.u,0.s) (success)
Tactic call abstract-unify-slow ran for 4.125 secs (4.125u,0.s) (success)
Tactic call δ-1-fast ran for 0. secs (0.u,0.s)
Tactic call unify-fast ran for 0. secs (0.u,0.s) (success)
Tactic call abstract-unify-fast ran for 0. secs (0.u,0.s) (success)
14
Tactic call δ-1-slow ran for 0.051 secs (0.051u,0.s)
Tactic call unify-slow ran for 0.579 secs (0.579u,0.s) (success)
Tactic call δ-1-fast ran for 0.051 secs (0.051u,0.s)
Tactic call unify-fast ran for 0.594 secs (0.594u,0.s) (success)
15
Tactic call δ-1-slow ran for 0.106 secs (0.106u,0.s)
Tactic call unify-slow ran for 1.326 secs (1.302u,0.023s) (success)
Tactic call δ-1-fast ran for 0.106 secs (0.107u,0.s)
Tactic call unify-fast ran for 1.364 secs (1.356u,0.007s) (success)
*)

(** Now we set up a similar test for β reduction, using variants with
    1 and 2 arguments. *)
Fixpoint big_tree2 (n : nat) {A} (v1 v2 : A) : A
  := match n with
     | 0 => Ax_fst (v1, v2)
     | S n => big_tree2 n (Ax_fst (v1, v2)) (Ax_snd (v1, v2))
     end.
Definition big_slow_beta1 (n : nat) := Eval cbv [big_tree2 slow] in id (fun v => big_tree2 n v v) slow.
Definition big_fast_beta1 (n : nat) := Eval cbv [big_tree2 fast] in id (fun v => big_tree2 n v v) fast.
Definition big_slow_beta2 (n : nat) := Eval cbv [big_tree2 slow] in id (big_tree2 n) slow slow.
Definition big_fast_beta2 (n : nat) := Eval cbv [big_tree2 fast] in id (big_tree2 n) fast fast.

Ltac beta_id v :=
  lazymatch v with
  | id ?f ?x => constr:(f x)
  | id ?f ?x ?y => constr:(f x y)
  end.

Ltac test_slow1 with_abstract n :=
  optimize_heap;
  let v := (eval cbv [big_slow_beta1] in (big_slow_beta1 n)) in
  let v := beta_id v in
  restart_timer;
  let v2 := (eval cbv beta in v) in
  finish_timing ("Tactic call β-1-slow1");
  time "unify-slow1" unify v v2;
  lazymatch with_abstract with
  | true => let __ := constr:(ltac:(time "abstract-unify-slow1" abstract exact_no_check (eq_refl v)) : v = v2) in
            idtac
  | false => idtac
  end.

Ltac test_slow2 with_abstract n :=
  optimize_heap;
  let v := (eval cbv [big_slow_beta2] in (big_slow_beta2 n)) in
  let v := beta_id v in
  restart_timer;
  let v2 := (eval cbv beta in v) in
  finish_timing ("Tactic call β-1-slow2");
  time "unify-slow2" unify v v2;
  lazymatch with_abstract with
  | true => let __ := constr:(ltac:(time "abstract-unify-slow2" abstract exact_no_check (eq_refl v)) : v = v2) in
            idtac
  | false => idtac
  end.

Ltac test_fast1 with_abstract n :=
  optimize_heap;
  let v := (eval cbv [big_fast_beta1] in (big_fast_beta1 n)) in
  let v := beta_id v in
  restart_timer;
  let v2 := (eval cbv beta in v) in
  finish_timing ("Tactic call β-1-fast1");
  time "unify-fast1" unify v v2;
  lazymatch with_abstract with
  | true => let __ := constr:(ltac:(time "abstract-unify-fast1" abstract exact_no_check (eq_refl v)) : v = v2) in
            idtac
  | false => idtac
  end.

Ltac test_fast2 with_abstract n :=
  optimize_heap;
  let v := (eval cbv [big_fast_beta2] in (big_fast_beta2 n)) in
  let v := beta_id v in
  restart_timer;
  let v2 := (eval cbv beta in v) in
  finish_timing ("Tactic call β-1-fast2");
  time "unify-fast2" unify v v2;
  lazymatch with_abstract with
  | true => let __ := constr:(ltac:(time "abstract-unify-fast2" abstract exact_no_check (eq_refl v)) : v = v2) in
            idtac
  | false => idtac
  end.
(* Goal True. *)
(*   idtac 1; test_slow1 true 1; test_fast1 true 1; test_slow2 true 1; test_fast2 true 1; *)
(*     idtac 2; test_slow1 true 2; test_fast1 true 2; test_slow2 true 2; test_fast2 true 2; *)
(*       idtac 14; test_slow1 false 14; test_fast1 false 14; test_slow2 false 14; test_fast2 false 14; *)
(*         idtac 15; test_slow1 false 15; test_fast1 false 15; test_slow2 false 15; test_fast2 false 15. *)
(* Abort. *)
(* 1
Tactic call β-1-slow1 ran for 0. secs (0.u,0.s)
Tactic call unify-slow1 ran for 0. secs (0.u,0.s) (success)
Tactic call abstract-unify-slow1 ran for 3.062 secs (3.062u,0.s) (success)
Tactic call β-1-fast1 ran for 0. secs (0.u,0.s)
Tactic call unify-fast1 ran for 0. secs (0.u,0.s) (success)
Tactic call abstract-unify-fast1 ran for 0. secs (0.u,0.s) (success)
Tactic call β-1-slow2 ran for 0. secs (0.u,0.s)
Tactic call unify-slow2 ran for 0. secs (0.u,0.s) (success)
Tactic call abstract-unify-slow2 ran for 4.096 secs (4.096u,0.s) (success)
Tactic call β-1-fast2 ran for 0. secs (0.u,0.s)
Tactic call unify-fast2 ran for 0. secs (0.u,0.s) (success)
Tactic call abstract-unify-fast2 ran for 0. secs (0.u,0.s) (success)
2
Tactic call β-1-slow1 ran for 0. secs (0.u,0.s)
Tactic call unify-slow1 ran for 0. secs (0.u,0.s) (success)
Tactic call abstract-unify-slow1 ran for 5.15 secs (5.15u,0.s) (success)
Tactic call β-1-fast1 ran for 0. secs (0.u,0.s)
Tactic call unify-fast1 ran for 0. secs (0.u,0.s) (success)
Tactic call abstract-unify-fast1 ran for 0. secs (0.u,0.s) (success)
Tactic call β-1-slow2 ran for 0. secs (0.u,0.s)
Tactic call unify-slow2 ran for 0. secs (0.u,0.s) (success)
Tactic call abstract-unify-slow2 ran for 6.177 secs (6.173u,0.003s) (success)
Tactic call β-1-fast2 ran for 0. secs (0.u,0.s)
Tactic call unify-fast2 ran for 0. secs (0.u,0.s) (success)
Tactic call abstract-unify-fast2 ran for 0.001 secs (0.001u,0.s) (success)
14
Tactic call β-1-slow1 ran for 0.046 secs (0.046u,0.s)
Tactic call unify-slow1 ran for 0.576 secs (0.576u,0.s) (success)
Tactic call β-1-fast1 ran for 0.046 secs (0.046u,0.s)
Tactic call unify-fast1 ran for 0.592 secs (0.592u,0.s) (success)
Tactic call β-1-slow2 ran for 0.047 secs (0.047u,0.s)
Tactic call unify-slow2 ran for 0.589 secs (0.589u,0.s) (success)
Tactic call β-1-fast2 ran for 0.049 secs (0.049u,0.s)
Tactic call unify-fast2 ran for 0.624 secs (0.624u,0.s) (success)
15
Tactic call β-1-slow1 ran for 0.097 secs (0.097u,0.s)
Tactic call unify-slow1 ran for 1.319 secs (1.303u,0.015s) (success)
Tactic call β-1-fast1 ran for 0.098 secs (0.098u,0.s)
Tactic call unify-fast1 ran for 1.322 secs (1.306u,0.016s) (success)
Tactic call β-1-slow2 ran for 0.098 secs (0.098u,0.s)
Tactic call unify-slow2 ran for 1.331 secs (1.327u,0.003s) (success)
Tactic call β-1-fast2 ran for 0.098 secs (0.098u,0.s)
Tactic call unify-fast2 ran for 1.348 secs (1.348u,0.s) (success)
*)

(** Now we set up a similar test for ζ reduction, using variants with
    1 and 2 arguments. *)
Definition big_slow_zeta1 (n : nat) := Eval cbv beta iota delta [big_tree2 slow] in let v := slow in big_tree2 n v v.
Definition big_fast_zeta1 (n : nat) := Eval cbv beta iota delta [big_tree2 fast] in let v := fast in big_tree2 n v v.
Definition big_slow_zeta2 (n : nat) := Eval cbv beta iota delta [big_tree2 slow] in let v1 := slow in let v2 := slow in big_tree2 n v1 v2.
Definition big_fast_zeta2 (n : nat) := Eval cbv beta iota delta [big_tree2 fast] in let v1 := fast in let v2 := fast in big_tree2 n v1 v2.

Ltac test_slow_zeta1 with_abstract n :=
  optimize_heap;
  let v := (eval cbv beta iota delta [big_slow_zeta1] in (big_slow_zeta1 n)) in
  restart_timer;
  let v2 := (eval cbv zeta in v) in
  finish_timing ("Tactic call ζ-1-slow1");
  time "unify-slow1" unify v v2;
  lazymatch with_abstract with
  | true => let __ := constr:(ltac:(time "abstract-unify-slow1" abstract exact_no_check (eq_refl v)) : v = v2) in
            idtac
  | false => idtac
  end.

Ltac test_slow_zeta2 with_abstract n :=
  optimize_heap;
  let v := (eval cbv beta iota delta [big_slow_zeta2] in (big_slow_zeta2 n)) in
  restart_timer;
  let v2 := (eval cbv zeta in v) in
  finish_timing ("Tactic call ζ-2-slow2");
  time "unify-slow2" unify v v2;
  lazymatch with_abstract with
  | true => let __ := constr:(ltac:(time "abstract-unify-slow2" abstract exact_no_check (eq_refl v)) : v = v2) in
            idtac
  | false => idtac
  end.

Ltac test_fast_zeta1 with_abstract n :=
  optimize_heap;
  let v := (eval cbv beta iota delta [big_fast_zeta1] in (big_fast_zeta1 n)) in
  restart_timer;
  let v2 := (eval cbv zeta in v) in
  finish_timing ("Tactic call ζ-1-fast1");
  time "unify-fast1" unify v v2;
  lazymatch with_abstract with
  | true => let __ := constr:(ltac:(time "abstract-unify-fast1" abstract exact_no_check (eq_refl v)) : v = v2) in
            idtac
  | false => idtac
  end.

Ltac test_fast_zeta2 with_abstract n :=
  optimize_heap;
  let v := (eval cbv beta iota delta [big_fast_zeta2] in (big_fast_zeta2 n)) in
  restart_timer;
  let v2 := (eval cbv zeta in v) in
  finish_timing ("Tactic call ζ-2-fast2");
  time "unify-fast2" unify v v2;
  lazymatch with_abstract with
  | true => let __ := constr:(ltac:(time "abstract-unify-fast2" abstract exact_no_check (eq_refl v)) : v = v2) in
            idtac
  | false => idtac
  end.

Goal True.
  Optimize Heap.
  Instructions idtac 4; test_slow_zeta1 true 4; test_fast_zeta1 true 4; test_slow_zeta2 true 4; test_fast_zeta2 true 4.
Abort.
