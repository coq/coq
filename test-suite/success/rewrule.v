(* -*- mode: coq; coq-prog-args: ("-allow-rewrite-rules") -*- *)

(* Simple first example *)
Symbol pplus : nat -> nat -> nat.
Notation "a ++ b" := (pplus a b).

Rewrite Rules plus_rew :=
| ?n ++ 0 => ?n
| ?n ++ S ?n' => S (?n ++ ?n')
| 0 ++ ?n => ?n
| S ?n ++ ?n' => S (?n ++ ?n').

Check eq_refl : 5 ++ 10 = 15.
Check (fun _ _ => eq_refl) : forall n n', 2 + n ++ 3 + n' = 5 + (n ++ n').

(* Test deep pattern matching *)
Eval lazy  in fun n n' => 2 + n ++ 3 + n'.
Eval cbv   in fun n n' => 2 + n ++ 3 + n'.
Eval cbn   in fun n n' => 2 + n ++ 3 + n'.
Eval simpl in fun n n' => 2 + n ++ 3 + n'. (* Does not reduce *)

(* Example with more pattern constructions and higher-order in patterns *)
#[unfold_fix] Symbol raise : forall P: Type, P.

Rewrite Rules raise_rew :=
  raise (forall (x : ?A), ?P) => fun x => raise ?P

| raise (?A * ?B) => (raise ?A, raise ?B)

| raise unit => tt

| match raise bool as b return ?P with
    true => _ | false => _
  end => raise ?P@{b := raise bool}

| match raise nat as n return ?P with
    0 => ?p | S n => ?p'
  end => raise ?P@{n := raise nat}

| match raise (@eq ?A ?a ?b) as e in _ = b return ?P with
  | eq_refl => _
  end => raise ?P@{b := _; e := raise (?a = ?b)}

| match raise (list ?A) as l return ?P with
  | nil => _ | cons _ _ => _
  end => raise ?P@{l := raise (list ?A)}

| match raise False as e return ?P with
  end => raise ?P@{e := raise False}

| match raise (?A + ?B) as e return ?P with
  | inl _ => _ | inr _ => _
  end => raise ?P@{e := raise (?A + ?B)}.
(* There is currently no way to write these rules without the universe inconcistency *)

Eval simpl in match raise bool with true | false => 0 end. (* Does not reduce *)

Eval lazy in match (raise nat * 5 + 3 :: 0 :: nil)%list with cons 0 l => tt | _ => tt end.

Eval lazy in raise nat + 5.
Eval cbv in raise nat + 5.
Eval cbn in raise nat + 5.
Eval simpl in raise nat + 5. (* Does not reduce *)





Set Primitive Projections.
Record primprod (A B : Type) := { fst: A; snd: B }.

(* Example with even more pattern constructions, mostly for terms *)
Universe idu.
#[unfold_fix, universes(polymorphic)] Symbol id@{q| |} : forall A : Type@{q|idu}, A -> A.

Rewrite Rules id_rew :=
| @{q|u+|+} |- id _ Type@{q|u} => Type@{q|u}

| @{q|u+|+} |- id Type@{q|u} (forall (x : ?A), ?P) => forall x, id Type@{q|u} ?P
| id (forall (x : ?A), ?P) ?f => fun (x : ?A) => id ?P (?f x)

| @{u+} |- id Type@{u} (?A * ?B)%type => (id Type@{u} ?A * id Type@{u} ?B)%type
| id (?A * ?B) (?a, ?b) => (id _ ?a, id _ ?b)

| id _ unit => unit
| id _ tt => tt

| id _ nat => nat
| id _ 0 => 0
| id _ (S ?n) => S (id _ ?n)
| id _ (fun (n : ?A) => S ?n) => fun n => S (id _ ?n)
| id (primprod ?A ?B) {| fst := ?a; snd := ?b |} => {| fst := id _ ?a; snd := id _ ?b |}.

Fail Rewrite Rule id_rew_fail := Datatypes.id _ ?x => ?x. (* Subterm not recognised as pattern: Datatypes.id *)
Fail Rewrite Rule id_rew_fail := 0 => 0. (* Head head-pattern is not a symbol. *)
Fail Rewrite Rule id_rew_fail := id _ (?x ?y) => ?x ?y. (* Subterm not recognised as pattern: ?x *)
Fail Rewrite Rule id_rew_fail := id _ _ => ?x. (* Unknown existential variable. *)
Fail Rewrite Rule id_rew_fail := @{u} |- id _ ?x => ?x. (* Not all universe level variables appear in the pattern. *)
Fail Rewrite Rule id_rew_fail := id _ (?x, ?x) => ?x. (* Variable ?x is bound multiple times in the pattern (holes number 1 and 2). *)
Fail Rewrite Rule id_rew_fail := @{u+} |- id _ (Type@{u}, Type@{u}) => ?x. (* Universe variable u is bound multiple times in the pattern (holes number 0 and 1). *)
Fail Rewrite Rule id_rew_fail := id _ (?x, ?y) => (?x, ?y). (* The replacement term contains unresolved implicit arguments: (?x, ?y) *)
Fail Rewrite Rule id_rew_fail := id _ Type => Type. (* Universe rewrule.xxx is unbound. *)
Fail Rewrite Rule id_rew_fail := id _ (forall x, ?P) => ?P. (* Cannot interpret ?P in current context: no binding for x. *)


Symbol idS : forall (A : SProp), A -> A.
Inductive unitS : SProp := ttS.
Rewrite Rule id_rew' := idS _ ttS => ttS.
(* Warning: This subpattern is irrelevant and can never be matched against. *)

Symbol vararity : forall n, (fix f n := match n with 0 => unit | S n => unit -> f n end) n.
Check vararity (4 + _) tt tt tt _.
Rewrite Rule vararity_rew := id _ (vararity _) => 0.
(* Warning: This subpattern has a yet unknown type, which may be a product type, but pattern-matching is not done modulo eta, so this rule may not trigger at required times *)

Module MLTTmap.

Symbol map : forall A B, (A -> B) -> list A -> list B.

Rewrite Rule map_rew :=
| map _ _ (fun x => x) ?l => ?l
| map _ ?C ?f (map ?A _ ?g ?l) => map ?A ?C (fun x => ?f (?g x)) ?l
| map ?A ?B ?f (@nil _) => @nil ?B
| map ?A ?B ?f (@cons _ ?a ?l) => @cons ?B (?f ?a) (map _ _ ?f ?l).

Definition idA {A: Type} := fun (x : A) => x.

Eval lazy  in fun l => (map _ _ idA l).
Eval cbv   in fun l => (map _ _ idA l).
Eval cbn   in fun l => (map _ _ idA l).
Eval simpl in fun l => (map _ _ idA l). (* Does not reduce *)

Eval lazy in fun l => (map _ _ (fun f x => f x) l).
(* Does not reduce because there is no support for eta *)

End MLTTmap.

(* Example where ignore holes are necessary *)
Symbol J : forall (A : Type) (a : A) (P : A -> Type), P a -> forall (a' : A), @eq A a a' -> P a'.
Rewrite Rule a := J _ _ _ ?H _ (@eq_refl _ _) => ?H.


Module omega.
(* Example of a broken extension *)
#[unfold_fix] Symbol omega : nat.
Rewrite Rule omega_rew := match omega with S n => ?P | 0 => _ end => ?P@{n := omega}.
Theorem omega_spec : S omega = omega.
Proof.
  symmetry.
  change omega with (Nat.pred omega) at 2.
  remember omega as omeg eqn:e.
  destruct omeg. 2: reflexivity.
  apply (f_equal (fun n => match n with 0 => 0 | S _ => 1 end)) in e.
  apply e.
Qed.

Theorem omega_contradiction : False.
Proof.
  assert (forall n, S n = n -> False) as X.
  2: eapply X, omega_spec.
  induction n.
  1: discriminate.
  now intros [=].
Qed.

Fail Timeout 1 Eval lazy in omega + 0.
End omega.


Module stream.

(* Subtle interaction between rewriting and the guard-checker *)
Inductive stream := T (_ : stream).

Fixpoint f s : False := f match s with T s' => s' end.
Fixpoint g s : False := match s with T s' => g s' end.

Rewrite Rule raise_rew_stream :=
| match raise _ as s return ?P with T _ => _ end => raise ?P@{s := raise _}.

Goal forall s, f s = g s.
  unfold f, g.
  induction s. assumption.
Defined.

Eval lazy in g (raise _).
Fail Timeout 1 Eval lazy in f (raise _).

End stream.

Module context.
(* Test whether context extensions work correctly (here, with constructor arrguments)*)
Symbol id : forall A, A -> A.
Axioms (aa ee : nat).
Inductive A := C (a := aa) (b : unit) (c := (a, b)) (d : True) (e := ee).

Rewrite Rule raise_rew_C := match raise _ with C a b c d e => id (_ * _) ?P end => ?P@{a := _; b := raise _; c := _; d := raise _; e := _}.

Eval lazy  in match raise _ with C a b c d e => id _ (a, b, c, d, e) end.
Eval cbv   in match raise _ with C a b c d e => id _ (a, b, c, d, e) end.
Eval cbn   in match raise _ with C a b c d e => id _ (a, b, c, d, e) end.
Eval simpl in match raise _ with C a b c d e => id _ (a, b, c, d, e) end.
End context.

(* Non-confluent rules prove False *)
Symbol Devil : bool -> bool.

Rewrite Rule devil :=
| Devil ?b => false
| Devil true => true.

Lemma Devil_false b : Devil b = false.
Proof. reflexivity. Defined.

Lemma Devil_true : Devil true = true.
Proof. reflexivity. Defined.

Lemma ministry_of_truth : true = false.
Proof.
  transitivity (Devil true).
  - symmetry;exact Devil_true.
  - apply Devil_false.
Defined.

Corollary contradiction : False.
Proof.
  pose proof ministry_of_truth; discriminate.
Defined.

Definition successor_of_nothing : nat :=
  match ministry_of_truth in eq _ b return if b then bool else nat with
    eq_refl => false
  end.

(* Such mistyped terms would break the VM, hence why it must be disabled *)
Eval vm_compute in pred successor_of_nothing.

Definition ignore {A} (x:A) := tt.

Definition beginning_of_the_world : ignore (pred successor_of_nothing) = tt.
Proof. lazy;reflexivity. Qed.

Lemma end_of_the_world : tt = tt.
Proof.
  vm_compute.
  exact beginning_of_the_world.
Defined.
(* This computation would run in the VM from the kernel, which is dangerous *)


(* Having a common supertype is not enough to preserve SR *)
Universe u.
Symbol idTy@{i} : Type@{i} -> Type@{u}.

Rewrite Rule idTy_id := idTy ?t => ?t.
(* Warning: This rewrite rule breaks subject reduction (universe inconsistency). *)

Definition U : Type@{u} := idTy Type@{u}.
Check U : U.

Definition id'@{i} : Type@{i} -> Type@{u} := fun (t: Type@{i}) => t.
Fail Definition U' : Type@{u} := id' Type@{u}.

Require Import TestSuite.hurkens.
Goal False.
  apply (TypeNeqSmallType.paradox U eq_refl).
Defined.


(* Test substitution on context extensions *)
Definition a : 0 = 0.
  set (test := let n := 0 in @eq_trans _ n n n (raise _) (raise _)).
  lazy delta in test.
  lazy beta in test.
  set (test_lazy := test).
  lazy delta zeta in test_lazy.
  set (test_cbv := test).
  cbv delta zeta in test_cbv.
  set (test_cbn := test).
  cbn delta zeta in test_cbn.
  set (test_simpl := test).
  unfold test in test_simpl. simpl in test_simpl.
Abort.

Definition test_subst_context :=
  Eval cbv delta zeta in
  let n := 0 in
  match raise (n = n) in (_ = a) return (n = a) with
  | eq_refl => raise _
  end.
