(* Uselessly long but why not *)

Local Set Universe Polymorphism.

Module tele.
(** Telescopes *)
Inductive tele : Type :=
  | TeleO : tele
  | TeleS {X} (binder : X -> tele) : tele.

Arguments TeleS {_} _.

(** The telescope version of Coq's function type *)
Fixpoint tele_fun (TT : tele) (T : Type) : Type :=
  match TT with
  | TeleO => T
  | TeleS b => forall x, tele_fun (b x) T
  end.

Notation "TT -t> A" :=
  (tele_fun TT A) (at level 99, A at level 200, right associativity).

(** An eliminator for elements of [tele_fun].
    We use a [fix] because, for some reason, that makes stuff print nicer
    in the proofs in iris:bi/lib/telescopes.v *)
Definition tele_fold {X Y} {TT : tele} (step : forall {A : Type}, (A -> Y) -> Y) (base : X -> Y)
  : (TT -t> X) -> Y :=
  (fix rec {TT} : (TT -t> X) -> Y :=
     match TT as TT return (TT -t> X) -> Y with
     | TeleO => fun x : X => base x
     | TeleS b => fun f => step (fun x => rec (f x))
     end) TT.
Arguments tele_fold {_ _ !_} _ _ _ /.

(** A sigma-like type for an "element" of a telescope, i.e. the data it
  takes to get a [T] from a [TT -t> T]. *)
Inductive tele_arg : tele -> Type :=
| TargO : tele_arg TeleO
(* the [x] is the only relevant data here *)
| TargS {X} {binder} (x : X) : tele_arg (binder x) -> tele_arg (TeleS binder).

Definition tele_app {TT : tele} {T} (f : TT -t> T) : tele_arg TT -> T :=
  fun a => (fix rec {TT} (a : tele_arg TT) : (TT -t> T) -> T :=
     match a in tele_arg TT return (TT -t> T) -> T with
     | TargO => fun t : T => t
     | TargS x a => fun f => rec a (f x)
     end) TT a f.
Arguments tele_app {!_ _} _ !_ /.

Coercion tele_arg : tele >-> Sortclass.
Local Coercion tele_app : tele_fun >-> Funclass.

(** Operate below [tele_fun]s with argument telescope [TT]. *)
Fixpoint tele_bind {U} {TT : tele} : (TT -> U) -> TT -t> U :=
  match TT as TT return (TT -> U) -> TT -t> U with
  | TeleO => fun F => F TargO
  | @TeleS X b => fun (F : TeleS b -> U) (x : X) => (* b x -t> U *)
                  tele_bind (fun a => F (TargS x a))
  end.
Arguments tele_bind {_ !_} _ /.

(** Notation-compatible telescope mapping *)
(* This adds (tele_app ∘ tele_bind), which is an identity function, around every
   binder so that, after simplifying, this matches the way we typically write
   notations involving telescopes. *)
Notation "t $ r" := (t r)
  (at level 65, right associativity, only parsing).
Notation "'λ..' x .. y , e" :=
  (tele_app $ tele_bind (fun x => .. (tele_app $ tele_bind (fun y => e)) .. ))
  (at level 200, x binder, y binder, right associativity,
   format "'[  ' 'λ..'  x  ..  y ']' ,  e").

(** Telescopic quantifiers *)
Definition texist {TT : tele} (Ψ : TT -> Prop) : Prop :=
  tele_fold ex (fun x => x) (tele_bind Ψ).
Arguments texist {!_} _ /.

Notation "'∃..' x .. y , P" := (texist (fun x => .. (texist (fun y => P)) .. ))
  (at level 200, x binder, y binder, right associativity,
  format "∃..  x  ..  y ,  P").
End tele.
Import tele.

(* This is like Iris' accessors, but in Prop.  Just to play with telescopes. *)
Definition accessor {X : tele} (α β γ : X -> Prop) : Prop :=
  ∃.. x, α x /\ (β x -> γ x).

(* Working with abstract telescopes. *)
Section tests.
Context {X : tele}.
Implicit Types α β γ : X -> Prop.

Lemma acc_mono_disj α β γ1 γ2 :
  accessor α β γ1 -> accessor α β (λ.. x, γ1 x \/ γ2 x).
Show.
Abort.
End tests.
