(* The second "match" below used to raise an anomaly *)

Class Monad@{d c} (m : Type@{d} -> Type@{c}) : Type :=
  { ret : forall {t : Type@{d}}, t -> m t }.

Record state {S : Type} (t : Type) : Type := mkState { runState : t }.

Global Declare Instance Monad_state : forall S, Monad (@state S).

Class Cava  := {
  constant : bool -> unit;
  constant_vec : unit;
}.

Axiom F : forall {A : Type}, (bool -> A) -> Datatypes.unit.

Fail Instance T : Cava := {

  constant b := match b with
    | true => ret tt
    | false => ret tt
    end;

  constant_vec := @F _ (fun b => match b with
    | true => tt
    | false => tt
  end);

}.
