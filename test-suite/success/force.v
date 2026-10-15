(* Force primitive regression tests. *)

Require Import Corelib.Force Ltac2.Ltac2.
Set Default Proof Mode "Classic".

Fail Check (block 0).
Fail Check (unblock 0).
Fail Check (run 0 (fun x => x)).

(**** UNIVERSES ****)

Definition check_run@{u1 u2} : forall (T : Type@{u1}) (K : Type@{u2}), Blocked T -> (T -> K) -> K := fun T K b k => __run@{Type Type;u1 u2} T K b k.
Inductive sunit : SProp := sitt.
Fail Check (__run@{SProp Type;Set Set} sunit nat (__block@{SProp;Set} sunit sitt) (fun _ => 0)).
Goal True.
Proof.
  ltac2:(
    let c := Constr.Unsafe.make
      (Constr.Unsafe.PRun 'sunit 'nat
        '(__block@{SProp;Set} sunit sitt)
        '(fun _ : sunit => 0)) in
    match Constr.Unsafe.check c with
    | Val _ => fail
    | Err _ => ()
    end).
  exact I.
Qed.
Definition check_Blocked@{u} : Type@{u} -> Type@{u} := Blocked.
Definition check_block@{u} : forall (T : Type@{u}), T -> Blocked@{Type;u} T := fun T x => __block@{Type;u} T x.
Fail Definition check_unblock@{u} : forall (T : Type@{u}), Blocked@{Type;u} T -> T := fun T x => __unblock x.

Module RunUniverseConversion.
  Universe u v.
  Constraint u < v.
  Axiom b : Blocked@{Type;Set} nat.
  Goal __run@{Type Type;Set u} nat nat b (fun x => x) =
       __run@{Type Type;Set v} nat nat b (fun x => x).
  Proof. reflexivity. Qed.
  Goal (let z := __run@{Type Type;Set u} nat nat b (fun x => x) in z) =
       __run@{Type Type;Set v} nat nat b (fun x => x).
  Proof. reflexivity. Qed.
End RunUniverseConversion.

Module EConstrUniverseComparison.
  Universe u v.
  Constraint u < v.

  (* Regression tests for the [EConstr.eq_constr_universes] fast path. *)
  Goal True.
  Proof.
    Fail constr_eq (__block@{Type;u} nat 0) (__block@{Type;v} nat 0).
    exact I.
  Qed.

  Axiom b : Blocked@{Type;Set} nat.
  Goal True.
  Proof.
    constr_eq (__run@{Type Type;Set u} nat nat b (fun x => x))
              (__run@{Type Type;Set v} nat nat b (fun x => x)).
    exact I.
  Qed.
End EConstrUniverseComparison.

Polymorphic Definition check_block_lazy_univs@{u} (A : Type@{u}) (x : A) := __block@{Type;u} A x.
Definition check_block_lazy_univs_inst : Blocked nat := __block nat 0.

(**** SORTS ****)

#[universes(polymorphic)] Definition type_of@{s;u} {T : Type@{s;u}} (t : T) := T.
Definition unblock_prop_type (b : Blocked@{Prop;_} (tt = tt)) : Blocked Type :=
  __block Type (type_of (__unblock b)).
Definition blocked_prop_type@{u v} : Blocked@{Type;v} Type@{u} := __block@{Type;v} Type@{u} ((tt = tt) : Type@{u}).

(**** EVALUATION ****)

Ltac syn_refl := lazymatch goal with |- ?t = ?t => exact eq_refl end.
Notation LAZY t := (ltac:(let x := eval lazy in t in exact x)) (only parsing).
Notation WHNF t := (ltac:(let x := eval lazy head in t in exact x)) (only parsing).

Definition force_test_idT (A : Type) := A.
Axiom stuck_blocked_nat : Blocked nat.

(* Regression: stuck [__run] reification must keep the return type associated
   with the continuation. *)
Goal LAZY (__run nat nat stuck_blocked_nat (fun x : nat => (x : force_test_idT nat)))
   = __run nat nat stuck_blocked_nat (fun x : nat => x).
Proof. syn_refl. Qed.

Opaque Blocked_ind.
Goal True.
Proof.
  let r := eval lazy in (@Blocked_ind nat (fun _ => nat) (fun x => x) (__block nat 1)) in
  assert (r = @Blocked_ind nat (fun _ => nat) (fun x => x) (__block nat 1)) by reflexivity; exact I.
Qed.
Transparent Blocked_ind.

Goal True.
Proof.
  let r := eval lazy -[Blocked_ind] in (@Blocked_ind nat (fun _ => nat) (fun x => x) (__block nat 1)) in
  assert (r = @Blocked_ind nat (fun _ => nat) (fun x => x) (__block nat 1)) by reflexivity; exact I.
Qed.


Goal WHNF (__block _ 0) = __block _ 0.
Proof. syn_refl. Qed.

Goal LAZY (__block _ 0) = __block _ 0.
Proof. syn_refl. Qed.

Goal WHNF (__block _ (0 + 0)) = __block _ (0 + 0).
Proof. syn_refl. Qed.

Goal LAZY (__block _ (0 + 0)) = __block _ 0.
Proof. syn_refl. Qed.

Goal WHNF (id (__block _ (0 + 0))) = __block _ (0 + 0).
Proof. syn_refl. Qed.

Goal LAZY (id (__block _ (0 + 0))) = __block _ 0.
Proof. syn_refl. Qed.

Goal WHNF (__block _ (__unblock (let x := 0 + 0 in __block _ x))) = __block _ 0.
Proof. syn_refl. Qed.

(* ... *)

Goal LAZY ((fun f => f (1 + 1)) (fun x => __block _ x)) = __block _ 2.
Proof. syn_refl. Qed.

Goal WHNF ((fun f => f (1 + 1)) (fun x => __block _ x)) = __block _ (1 + 1).
Proof. syn_refl. Qed.

Inductive True := I.
Definition id : True -> True := fun x => x.

Definition g := fun x:True => x.
Definition h := fun x:True => x.
Axiom and : True -> True -> True.
Axiom Pr : True -> Prop.

(* [__unblock] is block-local, even when hidden under a lambda. *)
Check (__block _ (__unblock (__block _ (id I = id I)))).
Fail Check ((fun f => f (__block _ (id I = id I))) (fun x => __unblock x)).

(* Non-lexical __run _ _ is just a "projection" *)
Goal WHNF ((fun f => f (__block _ (id I = id I)) (fun x => x)) (fun b k => __run _ _ b k)) = (id I = id I).
Proof. syn_refl. Qed.

Goal WHNF (__block _ (__unblock (let x := (and (g I) (h I)) in __block _ x))) = (__block _ (and I I)).
Proof. syn_refl. Qed.

Goal WHNF (__run _ _ (let x := (fun x : id I = I => True) in __block _ x) (fun x => x)) = (fun x : I = I => True).
Proof. syn_refl. Qed.

Goal WHNF (__run _ _ (let x := forall x : id I = I, True in __block _ x) (fun x => x)) = (forall x : I = I, True).
Proof. syn_refl. Qed.

Goal WHNF (__run _ _ (let x := id I in __block _ (forall u:unit, x = x)) (fun x => x)) = (forall (u:unit), I = I).
Proof. syn_refl. Qed.

Goal WHNF (__run _ _ (let x := 1 + 1 in __block _ x) (fun x => x)) = 2.
Proof. syn_refl. Qed.

Goal WHNF (__run _ _ (__block _ (1+1)) (fun x => x)) = WHNF (match 1 + 1 with S x => S x | 0 => 0 end).
Proof. syn_refl. Qed.

Goal WHNF (__block _ (__run _ _ (let n := I in __block _ n) (fun x : True => x)))
        = (__block _ (__run _ _ (let n := I in __block _ n) (fun x : True => x))).
Proof. syn_refl. Qed.

Goal WHNF (__block _ (__run _ _ (let x := (fun x => x) tt in __block _ x) (fun x => x)))
        = (__block _ (__run _ _ (let x := (fun x => x) tt in __block _ x) (fun x => x))).
Proof. syn_refl. Qed.

Goal WHNF (__block _ (__unblock (let x := (fun x => x) tt in __block _ x))) = __block _ tt.
Proof. syn_refl. Qed.

(*
__block _ (__unblock (let x := (fun x => x) tt in __block _ x)) @ ε | ∅ --{whnf}-->
__block _ @ (__unblock (let x := (fun x => x) tt in __block _ x)) . ε | ∅ --{whnf}-->

  __unblock (let x := (fun x => x) tt in __block _ x) @ ε | ∅ --{id}-->
  __unblock @ (let x := (fun x => x) tt in __block _ x) . ε | ∅ --{id}-->

    let x := (fun x => x) tt in __block _ x @ ε | ∅ --{full}-->
    __block _ x @ ε | ∅[x{full} := <(fun x => x) tt, ∅>] --{full}-->

      x @ ε | ∅[x{full} := <(fun x => x) tt, ∅>] --{id}-->

        (λ x => x) tt @ ε | ∅ --{full}-->
        λ x => x @ tt . ε | ∅ --{full}-->
        x @ ε | ∅[x{full} := <tt, ∅>] --{full}-->

          tt @ ε | ∅ --{full}--> (value)

        tt @ ε | ∅[x{full} := <tt, ∅>] --{full}--> (value)

      tt @ ε | ∅[x{full} := <tt, ∅>] --{id}--> (value, updated closure)

    __block _ tt @ ε | ∅[x{full} := <tt, ∅>] --{full}-->

  __unblock @ __block _ tt . ε | ∅ --{id}-->
  tt @ ε | ∅ --{id}-->

__block _ @ tt . ε | ∅ --{whnf}--> (done)
*)

Goal WHNF (__block _ (__run _ _ (let n := 2 + 2 in __block _ n) (fun x : nat => 2 * 1)))
        = (__block _ (__run _ _ (let n := 2 + 2 in __block _ n) (fun x : nat => 2 * 1))).
        (* = (__block _ ((fun _ : nat => 2 * 1) 4)). *)
Proof. syn_refl. Qed.

Goal WHNF (__block _ (__run _ _ ((fun n => __block _ n) (2 + 2)) (fun x : nat => 2 * 1)))
        = (__block _ (__run _ _ ((fun n => __block _ n) (2 + 2)) (fun x : nat => 2 * 1))).
        (* = (__block _ ((fun _ : nat => 2 * 1) 4)). *)
Proof. syn_refl. Qed.

Inductive n := N | O.
Definition a (x y : n) :=
  match x with
  | N => y
  | O => O
  end.
Goal WHNF (__block _ (__unblock ((fun x => __block _ (a x O)) (a N N)))) = __block _ (a N O).
Proof. syn_refl. Qed.

Goal WHNF (__block _ (__unblock ((fun x => __block _ x) (a N N)))) = __block _ (N).
Proof. syn_refl. Qed.

Goal WHNF (__block _ (__run _ _ ((fun n => __block _ (n + 1)) (2 + 2)) (fun x : nat => 2 * 1)))
        = (__block _ (__run _ _ ((fun n => __block _ (n + 1)) (2 + 2)) (fun x : nat => 2 * 1))).
        (* = (__block _ ((fun _ : nat => 2 * 1) (4 + 1))). *)
Proof. syn_refl. Qed.

Goal WHNF (__block _ (__unblock (let n := 0 + 0 in __block _ (n + n))))
        = __block _ (0 + 0).
Proof. syn_refl. Qed.

Goal WHNF (__block _ (__unblock (let n := 0 + 0 in __block _ (1 + __unblock (let m := 0 + 0 in __block _ (1 + m))))))
        = __block _ (1 + (1 + 0)).
Proof. syn_refl. Qed.

Goal WHNF (__block _ (__unblock (
                      let n := 0 + 0 in
                      __block _ (1 + n + __unblock (
                                     let m := 2 + 2 in
                                     __block _ (1 + m + __unblock (
                                                        let k := 3 + 3 in
                                                        __block _ (1 + n + m + k))))))))
        = __block _ (1 + 0 + (1 + 4 + (1 + 0 + 4 + 6))).
Proof. syn_refl. Qed.

Goal LAZY (__run _ _ (__block _ (1 + 1)) (fun x => x + x)) = 4.
Proof. syn_refl. Qed.

Goal LAZY (__run _ _ (__block _ (1 + 1)) (fun x => x + x)) = 4.
Proof. syn_refl. Qed.

Goal LAZY (__run _ _ (__block _ (1 + 1)) (fun x => x + x)) = 4.
Proof. syn_refl. Qed.

Goal LAZY (__block _ (2 + 2)) = __block _ 4.
Proof. syn_refl. Qed.

Goal LAZY (__run _ _ (__block _ 42) (fun x => x)) = 42.
Proof. syn_refl. Qed.

Goal LAZY (__run _ _ (__block _ (2 + 2)) (fun x => x)) = 4.
Proof. syn_refl. Qed.

Goal LAZY (__run _ _ ((fun _ => __block _ (2 + 2)) tt) (fun x => x)) = 4.
Proof. syn_refl. Qed.

Goal LAZY (__block _ (fun x => (2 + 2) + x)) =
  __block _ (fun x => S (S (S (S x)))).
Proof. syn_refl. Qed.

Goal LAZY (__run _ _ (__block _ (fun x => (2 + 2) + x)) (fun x => x)) = fun x => S (S (S (S x))).
Proof. syn_refl. Qed.

Goal WHNF (__run _ _ (let x := 1 + 1 in __block _ (x + 1)) (fun x => forall y, y = x))
        = forall y, y = 2 + 1.
Proof. syn_refl. Qed.

Set Printing Width 1000.
Section AllArgs.
  Context (b : Blocked (nat -> nat)).

  Fail Check (__unblock b 0).

  Goal LAZY (__run _ _ b (fun x n => n) 0) = __run _ _ b (fun x n => n) 0.
  Proof. syn_refl. Qed.

  Goal WHNF (__run _ _ b (fun x n => n) 0) = __run _ _ b (fun x n => n) 0.
  Proof. syn_refl. Qed.
End AllArgs.

Goal LAZY (__run _ _ (__block _ (fun x => __block _ x)) (fun f x => f x) (0 + 0)) = __block _ (0).
Proof. syn_refl. Qed.

Goal WHNF (__run _ _ (__block _ (fun x => __block _ x)) (fun f x => f x) (0 + 0)) = __block _ (0 + 0).
Proof. syn_refl. Qed.

Axiom F : __run _ _ (let x := id I in __block _ (id x)) (fun x => forall y, y = x).
Goal I=I.
Proof.
  Succeed refine (F I).
  Succeed apply (F I).
  Succeed eapply (F I).
  Succeed exact (F I).
  Succeed eexact (F I).
  exact (F I).
Qed.

Module FunctionTypes.
  (* The example below should not call reduction on [id id R] _at all_! *)
  Inductive D := | d.
  Inductive R := | r (b: D).
  Definition id (x:Set) := x.
  Eval lazy head in __run _ _
    (let f := (fun x : id (id R) => __block _ x) in
     __block _ (__unblock (f (r d))))
    (fun x => x).
End FunctionTypes.

Module Conversion.
  Axiom not : Prop -> Prop.
  Axiom TODO: forall {A:Prop}, A.

  Lemma test p :
    (forall _ : True, __run _ _ (__block _ (not p)) (fun x => x)).
  Proof.
    exact (@TODO (forall _ : True, not p)).
  Qed.
End Conversion.

Module Bla.
  Inductive prop :=.
  Axiom TODO: forall {A}, A.
  Definition reflect (p:prop) : Blocked Prop := match p with end.
  Lemma simplify_ok (p : prop) :
    __run _ _ (reflect p) (fun reflected => False <-> reflected).
  Proof.
    lazy.                       (* Used to fail *)
    destruct p.
  Qed.
End Bla.

(* Double substitution due to [Zrun] *)
Module Ind.
  Axiom P : nat -> Blocked Prop.
  Axiom x : nat.
  Axiom nat_ind_2 : forall P : nat -> Prop, (forall n : nat, True -> P (S n)) -> forall n : nat, P n.

  Goal forall n, (__run _ _ (P n) (fun p => p)).
  Proof.
    refine (@nat_ind_2 (fun n => __run _ _ (P n) (fun p => p)) _).
    intros n IHn.
    (* [Zrun]'s substitution was re-applied to the head in [zip_term] leading to wrong [REL]s. *)
    Fail lazymatch goal with |- context [P (S IHn)] => idtac end.
    lazymatch goal with |- context [P (S n)] => idtac end.
  Abort.
End Ind.

Module Proper.

Require Import Corelib.Classes.RelationClasses.
Require Import Corelib.Classes.Morphisms.
Require Import Corelib.Setoids.Setoid.

(* [Blocked] is primitive; [__unblock b] is only block-local syntax, not a
   global destructor or record field.  Standalone elimination uses [__run]. *)

Require Export Corelib.Force.


#[local] Set Universe Polymorphism.
#[local] Unset Universe Minimization ToSet.

Class Equiv (T : Type) := equiv :  T -> T -> Prop.
Arguments equiv {_ _}.


#[global] Instance Blocked_equiv {T} : Equiv T -> Equiv (Blocked T) :=
  fun equiv a b =>
    equiv (__run T T a (fun x => x)) (__run T T b (fun x => x)).

(* Regression test for conversion of [__run] stacks. The primitive operator
   universe instance is stored under the local closure substitution; conversion
   must apply that substitution before comparing it. *)
Definition unblock_stack_substitution {T} {R : Equiv T} :
  Proper (@equiv (Blocked T) (Blocked_equiv R) ==> @equiv T R)
    (fun x : Blocked T => __run T T x (fun x => x)) :=
  fun x y H => H.

Definition Run_equiv {T K} (R : Equiv K) (k : T -> K) : Equiv (Blocked T) :=
  fun a b => @equiv K R (__run _ _ a k) (__run _ _ b k).

Definition run_stack_substitution {T K} {R : Equiv K} (k : T -> K) :
  forall x y : Blocked T,
    @equiv (Blocked T) (Run_equiv R k) x y ->
    @equiv K R (__run _ _ x k) (__run _ _ y k) :=
  fun x y H => H.

#[global] Instance Blocked_equivalance {T} {R:Equiv T} : Equivalence R -> Equivalence (@equiv (Blocked T) _).
Proof.
  intros H.
  split.
  - destruct H as [H _ _]. repeat intro. apply H.
  - destruct H as [_ H _]. repeat intro. apply H. apply H0.
  - destruct H as [_ _ H]. repeat intro. refine (H _ _ _ _ _); eauto.
Qed.

#[global] Instance block_Proper {T} {R:Equiv T} : Proper (equiv ==> equiv) (fun x : T => __block _ x).
Proof. repeat intro. eauto. Qed.

#[global] Instance unblock_Proper {T} {R:Equiv T} :
  Proper (@equiv (Blocked T) _ ==> @equiv T _)
    (fun x : Blocked T => __run T T x (fun x => x)).
Proof. lazy. repeat intro. exact H. Qed.

Eval compute in @Blocked_ind nat (fun _ => nat) (fun n => S n) (__block _ 0).

Lemma Blocked_eta {T} (t: Blocked T) :
  __block _ (__run T T t (fun x => x)) = t.
Proof.
  refine (@Blocked_ind T (fun t => __block _ (__run T T t (fun x => x)) = t) _ t).
  intro x; reflexivity.
Qed.

End Proper.


(* Port of stdpp telescopes *)
Module Telescopes.
#[local] Set Universe Polymorphism.
#[local] Set Polymorphic Inductive Cumulativity.
Set Printing Universes.

Definition force_type@{u u1} (X : Blocked@{Type;u1} Type@{u}) : Type@{u} :=
  __run Type@{u} Type@{u} X (fun T => T).

Inductive tele@{u u1} : Type@{u1} :=
  | TeleO : tele
  | TeleS {X : Blocked@{Type;u1} Type@{u}} (binder : force_type X -> tele) : tele.

#[global] Arguments TeleS {_} _.

Fixpoint tele_fun (TT : tele) (T : Type) : Type :=
  match TT with
  | TeleO => T
  | TeleS b => forall x, tele_fun (b x) T
  end.

Notation "TT -t> A" :=
  (tele_fun TT A) (at level 99, A at level 200, right associativity).

Definition tele_fold {X Y} {TT : tele} (step : forall {A : Type}, (A -> Y) -> Y) (base : X -> Y)
  : (TT -t> X) -> Y :=
  (fix rec {TT} : (TT -t> X) -> Y :=
     match TT as TT return (TT -t> X) -> Y with
     | TeleO => fun x : X => base x
     | TeleS b => fun f => step (fun x => rec (f x))
     end) TT.
Global Arguments tele_fold {_ _ !_} _ _ _ /.

Record tele_arg_cons {X : Type} (f : X -> Type) : Type := TeleArgCons
  { tele_arg_head : X;
    tele_arg_tail : f tele_arg_head }.
Global Arguments TeleArgCons {_ _} _ _.

Fixpoint tele_arg@{u u1} (t : tele@{u u1}) : Type@{u} :=
  match t with
  | TeleO => unit
  | TeleS f => tele_arg_cons (fun x => tele_arg (f x))
  end.
Global Arguments tele_arg _ : simpl never.


Notation TargO := (tt : tele_arg TeleO) (only parsing).
Notation TargS a b :=
  ((@TeleArgCons _ (fun x => tele_arg (_ x)) a b) : (tele_arg (TeleS _))) (only parsing).
Coercion tele_arg : tele >-> Sortclass.

Lemma tele_arg_ind (P : forall TT, tele_arg TT -> Prop) :
  P TeleO TargO ->
  (forall (T : Blocked Type) (b : force_type T -> tele) x xs, P (b x) xs -> P (TeleS b) (TargS x xs)) ->
  forall TT (xs : tele_arg TT), P TT xs.
Proof.
  intros H0 HS TT. induction TT as [|T b IH]; simpl.
  - intros []. exact H0.
  - intros [x xs]. apply HS. now auto.
Qed.

Fixpoint tele_app {TT : tele} {U} : (TT -t> U) -> TT -> U :=
  match TT as TT return (TT -t> U) -> TT -> U with
  | TeleO => fun F _ => F
  | TeleS r => fun (F : TeleS r -t> U) '(TeleArgCons x b) =>
      tele_app (F x) b
  end.
Global Arguments tele_app {!_ _} & _ !_ /.

Local Coercion tele_app : tele_fun >-> Funclass.

Lemma tele_arg_inv {TT : tele} (a : tele_arg TT) :
  match TT as TT return tele_arg TT -> Prop with
  | TeleO => fun a => a = TargO
  | TeleS f => fun a => exists x a', a = TargS x a'
  end a.
Proof. destruct TT; destruct a; eauto. Qed.
Lemma tele_arg_O_inv (a : TeleO) : a = TargO.
Proof. exact (tele_arg_inv a). Qed.
Lemma tele_arg_S_inv {X : Blocked Type} {f : force_type X -> tele} (a : TeleS f) :
  exists x a', a = TargS x a'.
Proof. exact (tele_arg_inv a). Qed.

Fixpoint tele_map {T U} {TT : tele} : (T -> U) -> (TT -t> T) -> TT -t> U :=
  match TT as TT return (T -> U) -> (TT -t> T) -> TT -t> U with
  | TeleO => fun F : T -> U => F
  | @TeleS X b => fun (F : T -> U) (f : TeleS b -t> T) (x : force_type X) =>
                  tele_map F (f x)
  end.
Global Arguments tele_map {_ _ !_} _ _ /.

Lemma tele_map_app {T U} {TT : tele} (F : T -> U) (t : TT -t> T) (x : TT) :
  (tele_map F t) x = F (t x).
Proof.
  induction TT as [|X f IH]; simpl in x.
  - rewrite (tele_arg_O_inv x). now auto.
  - destruct (tele_arg_S_inv x) as [x' [a' ->]]. simpl.
    rewrite <-IH. now auto.
Qed.

Fixpoint tele_bind {U} {TT : tele} : (TT -> U) -> TT -t> U :=
  match TT as TT return (TT -> U) -> TT -t> U with
  | TeleO => fun F => F tt
  | @TeleS X b => fun (F : TeleS b -> U) (x : force_type X) =>
      tele_bind (fun a => F (TargS x a))
  end.
Global Arguments tele_bind {_ !_} _ /.

Lemma tele_app_bind {U} {TT : tele} (f : TT -> U) x :
  (tele_bind f) x = f x.
Proof.
  induction TT as [|X b IH]; simpl in x.
  - rewrite (tele_arg_O_inv x). now auto.
  - destruct (tele_arg_S_inv x) as [x' [a' ->]]. simpl.
    rewrite IH. now auto.
Qed.

Definition tele_fun_id {TT : tele} : TT -t> TT := tele_bind (fun x => x).

Lemma tele_fun_id_eq {TT : tele} (x : TT) :
  tele_fun_id x = x.
Proof. unfold tele_fun_id. rewrite tele_app_bind. now auto. Qed.

Definition tforall {TT : tele} (Ψ : TT -> Prop) : Prop :=
  tele_fold (fun (T : Type) (b : T -> Prop) => forall x : T, b x) (fun x => x) (tele_bind Ψ).
Global Arguments tforall {!_} _ /.
Definition texist {TT : tele} (Ψ : TT -> Prop) : Prop :=
  tele_fold ex (fun x => x) (tele_bind Ψ).
Global Arguments texist {!_} _ /.

Notation "'forall..' x .. y , P" := (tforall (fun x => .. (tforall (fun y => P)) .. ))
  (at level 200, x binder, y binder, right associativity,
  format "forall.. x .. y , P") : stdpp_scope.
Notation "'∃..' x .. y , P" := (texist (fun x => .. (texist (fun y => P)) .. ))
  (at level 200, x binder, y binder, right associativity,
  format "∃.. x .. y , P") : stdpp_scope.

Lemma tforall_forall {TT : tele} (Ψ : TT -> Prop) :
  tforall Ψ <-> (forall x, Ψ x).
Proof.
  symmetry. unfold tforall. induction TT as [|X ft IH].
  - simpl. split.
    + now auto.
    + intros ? p. rewrite (tele_arg_O_inv p). now auto.
  - simpl. split; intros Hx a.
    + rewrite <-IH. now auto.
    + destruct (tele_arg_S_inv a) as [x [pf ->]].
      revert pf. setoid_rewrite IH. now auto.
Qed.

Lemma texist_exist {TT : tele} (Ψ : TT -> Prop) :
  texist Ψ <-> ex Ψ.
Proof.
  symmetry. induction TT as [|X ft IH].
  - simpl. split.
    + intros [p Hp]. rewrite (tele_arg_O_inv p) in Hp. now auto.
    + intros. now exists TargO.
  - simpl. split; intros [p Hp]; revert Hp.
    + destruct (tele_arg_S_inv p) as [x [pf ->]]. intros ?.
      exists x. rewrite <-(IH x (fun a => Ψ (TargS x a))). eauto.
    + rewrite <-(IH p (fun a => Ψ (TargS p a))).
      intros [??]. eauto.
Qed.

Set Printing Implicit.

Monomorphic Universes u u1.
Goal
  WHNF (__run _ _
    (__block _ (TeleS@{u u1} (X:=__block@{Type;u1} Type@{u} (1 + 1 = 2)) (fun x : 1 + 1 = 2 => TeleO@{u u1})))
    (fun x => x))
  = TeleS@{u u1} (X:=__block@{Type;u1} Type@{u} ( 1 + 1 = 2)) (fun x : 1 + 1 = 2 => TeleO@{u u1}).
Proof. syn_refl. Qed.

End Telescopes.
