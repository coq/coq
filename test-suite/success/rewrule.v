Symbol pplus : nat -> nat -> nat.
Notation "a ++ b" := (pplus a b).

Rewrite Rules plus_rew := ?n ++ 0 ==> ?n
with ?n ++ S ?n' ==> S (?n ++ ?n')
with 0 ++ ?n ==> ?n
with S ?n ++ ?n' ==> S (?n ++ ?n').

Check eq_refl : 5 ++ 10 = 15.
Check (fun _ _ => eq_refl) : forall n n', 2 + n ++ 3 + n' = 5 + (n ++ n').
Check (fun _ _ _ => eq_refl) : forall n n' n'', 2 + n ++ 1 + n' ++ 2 + n'' = 5 + (n ++ n' ++ n'').

Eval lazy in fun n n' => 2 + n ++ 3 + n'.
Eval cbv in fun n n' => 2 + n ++ 3 + n'.
Eval cbn in fun n n' => 2 + n ++ 3 + n'.
Eval simpl in fun n n' => 2 + n ++ 3 + n'.

#[unfold_fix] Symbol raise : forall P: Type, P.

Rewrite Rules raise_rew :=
  raise (forall (x : ?A), ?P) ==> fun (x : ?A) => raise ?P

with
  raise (?A * ?B) ==> (raise ?A, raise ?B)

with
  raise unit ==> tt

with
  match raise bool as b return ?P with
    true => _ | false => _
  end ==> raise ?P@{b := raise bool}

with
  match raise nat as n return ?P with
    0 => ?p | S n => ?p'
  end ==> raise ?P@{n := raise nat}

with
  match raise (@eq ?A ?a ?b) as e in _ = b return ?P with
  | eq_refl => _
  end ==> raise ?P@{b := _; e := raise (?a = ?b)}

with
  match raise (list ?A) as l return ?P with
  | nil => _ | cons _ _ => _
  end ==> raise ?P@{l := raise (list ?A)}

with
  match raise False as e return ?P with
  end ==> raise ?P@{e := raise False}

with
  match raise (?A + ?B) as e return ?P with
  | inl _ => _ | inr _ => _
  end ==> raise ?P@{e := raise (?A + ?B)}.


Eval simpl in match raise bool with true | false => 0 end.

Eval lazy in match (raise nat * 5 + 3 :: 0 :: nil)%list with cons 0 l => tt | _ => tt end.

Eval lazy in raise nat + 5.
Eval cbv in raise nat + 5.
Eval cbn in raise nat + 5.
Eval simpl in raise nat + 5.

(* Set Primitive Projections. *)
Record prod (A B : Type) := { fst: A; snd: B}.

#[unfold_fix] Symbol id : forall A, A -> A.


Rewrite Rules id_rew :=
  id _ Type ==> Type

with
  id _ (forall (x : ?A), ?P) ==> forall (x : ?A), id _ ?P
with
  id (forall x, ?P) (fun (x : ?A) => ?f) ==> fun (x : ?A) => id ?P ?f

with
  id _ (?A * ?B)%type ==> (id _ ?A * id _ ?B)%type
with
  id (?A * ?B) (?a, ?b) ==> (id _ ?a, id _ ?b)

with
  id _ unit ==> unit
with
  id _ tt ==> tt

with
  id _ nat ==> nat
with
  id _ 0 ==> 0
with
  id _ (S ?n) ==> S (id _ ?n)
.


Symbol cast : forall A B, A -> B.
Notation "<< B <== A >> t" := (cast A B t) (at level 10).

Rewrite Rules cast_rew :=
  << forall (y : ?C), ?D <== forall (x: ?A), ?B >> ?f
  ==> fun (y : ?C) => let x := << _ <== _ >> y in << ?D <== ?B@{x := x} >> (?f x)

with
  << Type <== Type >> ?t ==> ?t

with
  << nat <== bool >> _ ==> raise nat
with
  << bool <== nat >> _ ==> raise bool
.


Module MLTTmap.

Symbol map : forall A B, (A -> B) -> list A -> list B.

Rewrite Rule map_rew :=
     map _ _ (fun x => x) ?l ==> ?l
with map _ ?C ?f (map ?A _ ?g ?l) ==> map ?A ?C (fun x => ?f (?g x)) ?l
with map ?A ?B ?f (@nil _) ==> @nil ?B
with map ?A ?B ?f (@cons _ ?a ?l) ==> @cons ?B (?f ?a) (map _ _ ?f ?l).

Definition idA {A: Type} := fun (x : A) => x.

Eval lazy in fun l => (map _ _ idA l).
Eval cbv in fun l => (map _ _ idA l).
Eval cbn in fun l => (map _ _ idA l).
Eval simpl in fun l => (map _ _ idA l).

End MLTTmap.



Symbol J : forall (A : Type) (a : A) (P : A -> Type), P a -> forall (a' : A), @eq A a a' -> P a'.
Rewrite Rule a := J _ _ _ ?H _ (@eq_refl _ _) ==> ?H.


#[unfold_fix] Symbol omega : nat.
Rewrite Rule omega_rew := match omega with S n => ?P | 0 => _ end ==> ?P@{n := omega}.
Theorem omega_spec : S omega = omega.
Proof.
  symmetry.
  change omega with (Nat.pred omega) at 2.
  remember omega as omeg eqn:e.
  destruct omeg. 2: reflexivity.
  apply (f_equal (fun n => match n with 0 => 0 | S _ => 1 end)) in e.
  apply e.
Qed.

Fail Timeout 1 Eval lazy in omega + 0.




Module stream.

Inductive stream := T (_ : stream).

Fixpoint f s : False := f match s with T s' => s' end.
Fixpoint g s : False := match s with T s' => g s' end.

Rewrite Rule raise_rew' := match raise _ as s return ?P with T _ => _ end ==> raise ?P@{s := raise _}.

Goal forall s, f s = g s.
  intro s0. unfold f, g. cbn.
  induction s0. cbn. auto.
Defined.

Eval lazy in g (raise _).
Fail Timeout 1 Eval lazy in f (raise _).

End stream.


Symbol id2 : forall A, A -> A.
Axioms (aa ee : nat).
Inductive annoying := C (a := aa) (b : unit) (c := (a, b)) (d : True) (e := ee).

Rewrite Rule raise_rew'' := match raise _ with C a b c d e => id2 _ ?P end ==> ?P@{a := aa; b := raise _; c := (aa, raise unit); d := raise _; e := ee}.

Eval lazy in match raise _ with C a b c d e => id2 _ (a, b, c, d, e) end.
Eval cbv in match raise _ with C a b c d e => id2 _ (a, b, c, d, e) end.
Eval cbn in match raise _ with C a b c d e => id2 _ (a, b, c, d, e) end.
Eval simpl in match raise _ with C a b c d e => id2 _ (a, b, c, d, e) end.


Module SuccPred.
#[unfold_fix] Symbols P S : nat -> nat.
Rewrite Rule P_rew :=
  P (S ?n) ==> ?n
with S (P ?n) ==> ?n
with S ?n ++ ?m ==> S (?n ++ ?m)
with ?n ++ S ?m ==> S (?n ++ ?m)
with P ?n ++ ?m ==> P (?n ++ ?m)
with ?n ++ P ?m ==> P (?n ++ ?m)
.

Eval lazy in fun n => S (S (S n)) ++ P (P (P n)).

End SuccPred.


Definition operator := unit.
Symbol op : operator -> operator.
Symbols plus mult : operator.
Rewrite Rules op_rew :=
  op (op ?op) ==> ?op
with op plus ==> mult
with op mult ==> plus.





Symbol pmult : nat -> nat -> nat.
Notation "a ** b" := (pmult a b) (at level 8).

Rewrite Rules pmult_rew := _ ** 0 ==> 0
with ?n ** (S ?n') ==> (?n ** ?n') ++ ?n
with 0 ** _ ==> 0
with (S ?n) ** ?n' ==> ?n' ++ (?n ** ?n').

Fixpoint fact (n : nat) :=
  match n with 0 => 1 | S n => (S n) ** (fact n) end.

Fixpoint fact' (n : nat) :=
  match n with 0 => 1 | S n => (S n) * (fact' n) end.

Time Eval lazy in fact' 7.
Time Eval lazy in fact 7.

Symbol mod5 : nat -> nat.
Rewrite Rules mod5_rew :=
  mod5 (S (S (S (S (S ?n))))) ==> mod5 ?n
with mod5 0 ==> 0
with mod5 1 ==> 1
with mod5 2 ==> 2
with mod5 3 ==> 3
with mod5 4 ==> 4
.
Eval lazy in (fun n => mod5 (4 ** (3 ++ n))).

Rewrite Rule plus_assoc := ?n ++ ?m ++ ?p ==> (?n ++ ?m) ++ ?p.

From Coq Require Import ssreflect.

Lemma add_comm m n : m ++ n = n ++ m.
Proof.
  induction n; cbn; auto.
Qed.

Inductive vector {A : Type} | : nat -> Type :=
| vnil : vector 0
| vcons {n} : A -> vector n -> vector (S n).
Arguments vector : clear implicits.


Symbol vapp : forall {A n m}, vector A n -> vector A m -> vector A (n ++ m).
Arguments vapp {_ _ _}.

Rewrite Rules vapp_rew := vapp (m := 0) ?v _ ==> ?v
with vapp (n := 0) _ ?v' ==> ?v'
with @vapp ?A (S ?n) ?m (vcons ?a ?v) ?v' ==> @vcons ?A _ ?a (@vapp ?A ?n ?m ?v ?v').

Fixpoint vapp' {A n m} (v : vector A n) (v' : vector A m) : vector A (n ++ m) :=
  match v with
  | vnil => v'
  | vcons a v => vcons a (vapp' v v')
  end.

Lemma vapp'_vapp {A n m} (v : vector A n) (v' : vector A m) : vapp' v v' = vapp v v'.
Proof.
  induction v => //=.
  now f_equal.
Qed.

Lemma vapp_nil {A n} (v : vector A 0) (v' : vector A n) : vapp v v' = v'.
Proof.
  reflexivity.
Qed.

Lemma vapp_nil_r {A n} (v : vector A n) (v' : vector A 0) : vapp v v' = v.
Proof.
  cbn.
  refine (match v' with vnil => _ end).
  induction v => //=.
Qed.

Lemma vapp_assoc {A n m p} (v : vector A n) (v' : vector A m) (v'' : vector A p) :
  vapp v (vapp v' v'') = vapp (vapp v v') v''.
Proof.
  induction v => //. idtac => /=. idtac => /=.
  now f_equal.
Qed.

Definition vhead {A n} (v : vector A (S n)) : A :=
  match v with vcons a _ => a end.

Lemma vheadapp {A n m} (v : vector A (S n)) (v' : vector A m) : vhead (vapp v v') = vhead v.
  refine (
    match v in vector _ (S n) return vhead (vapp v v') = vhead v with vcons a v => _ end
  ).
  reflexivity.
Qed.

Fixpoint vtail_default {A} a {n} (v : vector A n) := match v with vnil => a | vcons a v => vtail_default a v end.

Definition vtail {A n} (v : vector A (S n)) : A :=
  match v with
  | vcons a v => vtail_default a v
  end.

Lemma vtail_vtail_default {A n} (v : vector A (S n)) a : vtail_default a v = vtail v.
Proof.
  refine (match v in vector _ (S n) with vcons a v => _ end).
  reflexivity.
Qed.

Lemma vtailapp {A n m} (v : vector A n) (v' : vector A (S m)) : vtail (n := n ++ m) (vapp v v') = vtail v'.
Proof.
  induction v => //=.
  erewrite <- vtail_vtail_default in IHv.
  apply IHv.
Qed.


Symbol brk : bool -> bool -> bool.
Rewrite Rules brk_rew := brk true ?b ==> true
with brk ?b true ==> false.

Lemma f0 : False.
  cut { b | brk true b = brk b true}.
  2: exists true; reflexivity.
  intros [b H].
  cbn in H.
  discriminate.
Qed.


Definition f b (H : brk true b = brk b true) : False :=
  eq_ind true (fun e => if e then True else False) I false H.

Eval lazy in (f true eq_refl). (* = I : False *)


Universe u.
Symbol idTy@{i} : Type@{i} -> Type@{u}.

Rewrite Rule idTy_id := idTy ?t ==> ?t.


Definition U : Type@{u} := idTy Type@{u}.
Check U : U.

Definition id'@{i} : Type@{i} -> Type@{u} := fun (t: Type@{i}) => t.
Fail Definition U' : Type@{u} := id' Type@{u}.

Require Import Coq.Logic.Hurkens.
Check TypeNeqSmallType.paradox U eq_refl : False.

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
