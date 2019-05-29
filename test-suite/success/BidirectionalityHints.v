From Coq Require Import Utf8.
Set Default Proof Using "Type".

Module SimpleExamples.

Axiom c : bool -> nat.
Coercion c : bool >-> nat.
Inductive Boxed A := Box (a : A).
Arguments Box {A} & a.
Check Box true : Boxed nat.

(* Here we check that there is no regression due e.g. to refining arguments
   in the wrong order *)
Axiom f : forall b : bool, (if b then bool else nat) -> Type.
Check f true true : Type.
Arguments f & _ _.
Check f true true : Type.

End SimpleExamples.

Module Issue7910.

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

(** An eliminator for elements of [tele_fun].
    We use a [fix] because, for some reason, that makes stuff print nicer
    in the proofs in iris:bi/lib/telescopes.v *)
Definition tele_fold {X Y} {TT : tele} (step : ∀ {A : Type}, (A → Y) → Y) (base : X → Y)
  : (TT -t> X) → Y :=
  (fix rec {TT} : (TT -t> X) → Y :=
     match TT as TT return (TT -t> X) → Y with
     | TeleO => λ x : X, base x
     | TeleS b => λ f, step (λ x, rec (f x))
     end) TT.
Arguments tele_fold {_ _ !_} _ _ _ /.

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
Arguments tele_app {!_ _} & _ !_ /.

Coercion tele_arg : tele >-> Sortclass.
Coercion tele_app : tele_fun >-> Funclass.

(** Operate below [tele_fun]s with argument telescope [TT]. *)
Fixpoint tele_bind {U} {TT : tele} : (TT → U) → TT -t> U :=
  match TT as TT return (TT → U) → TT -t> U with
  | TeleO => λ F, F TargO
  | @TeleS X b => λ (F : TeleS b → U) (x : X), (* b x -t> U *)
                  tele_bind (λ a, F (TargS x a))
  end.
Arguments tele_bind {_ !_} _ /.

(** Telescopic quantifiers *)
Definition tforall {TT : tele} (Ψ : TT → Prop) : Prop :=
  tele_fold (λ (T : Type) (b : T → Prop), ∀ x : T, b x) (λ x, x) (tele_bind Ψ).
Arguments tforall {!_} _ /.
Definition texist {TT : tele} (Ψ : TT → Prop) : Prop :=
  tele_fold ex (λ x, x) (tele_bind Ψ).
Arguments texist {!_} _ /.

Notation "'∀..' x .. y , P" := (tforall (λ x, .. (tforall (λ y, P)) .. ))
  (at level 200, x binder, y binder, right associativity,
  format "∀..  x  ..  y ,  P").
Notation "'∃..' x .. y , P" := (texist (λ x, .. (texist (λ y, P)) .. ))
  (at level 200, x binder, y binder, right associativity,
  format "∃..  x  ..  y ,  P").

(** The actual test case *)
Definition test {TT : tele} (t : TT → Prop) : Prop :=
  ∀.. x, t x ∧ t x.

Notation "'[TEST' x .. z , P ']'" :=
  (test (TT:=(TeleS (fun x => .. (TeleS (fun z => TeleO)) ..)))
        (tele_app (λ x, .. (λ z, P) ..)))
  (x binder, z binder).
Notation "'[TEST2' x .. z , P ']'" :=
  (test (TT:=(TeleS (fun x => .. (TeleS (fun z => TeleO)) ..)))
        (tele_app (TT:=(TeleS (fun x => .. (TeleS (fun z => TeleO)) ..)))
                  (λ x, .. (λ z, P) ..)))
  (x binder, z binder).

Check [TEST (x y : nat), x = y].

Check [TEST2 (x y : nat), x = y].

End Issue7910.
