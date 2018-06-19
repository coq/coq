From Coq Require Import Utf8 Setoid ssreflect.
Set Default Proof Using "Type".

Local Set Universe Polymorphism.

(** Telescopes *)
Inductive tele : Type :=
  | TeleO : tele
  | TeleS {X} (binder : X → tele) : tele.

Arguments TeleS {_} _.

(** The telescope version of Coq's function type *)
Fixpoint tele_fun (TT : tele) (T : Type) : Type :=
  match TT with
  | TeleO => T
  | TeleS b => ∀ x, tele_fun (b x) T
  end.

Notation "TT -t> A" :=
  (tele_fun TT A) (at level 99, A at level 200, right associativity).

(** A sigma-like type for an "element" of a telescope, i.e. the data it
  takes to get a [T] from a [TT -t> T]. *)
Inductive tele_arg : tele → Type :=
| TargO : tele_arg TeleO
(* the [x] is the only relevant data here *)
| TargS {X} {binder} (x : X) : tele_arg (binder x) → tele_arg (TeleS binder).

Definition tele_app {TT : tele} {T} (f : TT -t> T) : tele_arg TT → T :=
  λ a, (fix rec {TT} (a : tele_arg TT) : (TT -t> T) → T :=
     match a in tele_arg TT return (TT -t> T) → T with
     | TargO => λ t : T, t
     | TargS x a => λ f, rec a (f x)
     end) TT a f.
Arguments tele_app {!_ _} _ !_ /.

Coercion tele_arg : tele >-> Sortclass.
Coercion tele_app : tele_fun >-> Funclass.

(** Inversion lemma for [tele_arg] *)
Lemma tele_arg_inv {TT : tele} (a : TT) :
  match TT as TT return TT → Prop with
  | TeleO => λ a, a = TargO
  | TeleS f => λ a, ∃ x a', a = TargS x a'
  end a.
Proof. induction a; eauto. Qed.
Lemma tele_arg_O_inv (a : TeleO) : a = TargO.
Proof. exact (tele_arg_inv a). Qed.
Lemma tele_arg_S_inv {X} {f : X → tele} (a : TeleS f) :
  ∃ x a', a = TargS x a'.
Proof. exact (tele_arg_inv a). Qed.

(** Operate below [tele_fun]s with argument telescope [TT]. *)
Fixpoint tele_bind {U} {TT : tele} : (TT → U) → TT -t> U :=
  match TT as TT return (TT → U) → TT -t> U with
  | TeleO => λ F, F TargO
  | @TeleS X b => λ (F : TeleS b → U) (x : X), (* b x -t> U *)
                  tele_bind (λ a, F (TargS x a))
  end.
Arguments tele_bind {_ !_} _ /.

(* Show that tele_app ∘ tele_bind is the identity. *)
Lemma tele_app_bind {U} {TT : tele} (f : TT → U) x :
  (tele_app (tele_bind f)) x = f x.
Proof.
  induction TT as [|X b IH]; simpl in *.
  - rewrite (tele_arg_O_inv x). auto.
  - destruct (tele_arg_S_inv x) as [x' [a' ->]]. simpl.
    rewrite IH. auto.
Qed.

(** Notation-compatible telescope mapping *)
(* This adds (tele_app ∘ tele_bind), which is an identity function, around every
   binder so that, after simplifying, this matches the way we typically write
   notations involving telescopes. *)
Notation "'λ..' x .. y , e" :=
  (tele_app (tele_bind (λ x, .. (tele_app (tele_bind (λ y, e))) .. )))
  (at level 200, x binder, y binder, right associativity,
   format "'[  ' 'λ..'  x  ..  y ']' ,  e").

(* The testcase *)
Lemma test {TA TB : tele} {X} (α' β' γ' : X → Prop) (Φ : TA → TB → Prop) x' :
  (forall P Q, ((P /\ Q) = Q) * ((P -> Q) = Q)) ->
  ∀ a b, Φ a b = (λ.. x y, β' x' ∧ (γ' x' → Φ x y)) a b.
Proof.
intros cheat a b.
rewrite !tele_app_bind.
by rewrite !cheat.
Qed.
