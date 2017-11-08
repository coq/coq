(* Supporting imp. params. in inductive or fixpoints mutually defined with a notation *)

Reserved Notation "* a" (at level 70).
Inductive P {n : nat} : nat -> Prop :=
| c m : *m
where "* m" := (P m).

Reserved Notation "##".
Inductive I {A:Type} := C : ## where "##" := I.

(* The following was working in 8.6 *)

Require Import Vector.

Reserved Notation "# a" (at level 70).
Fixpoint f {n : nat} (v:Vector.t nat n) : nat :=
  match v with
  | nil _ => 0
  | cons _ _ _ v => S (#v)
  end
where "# v" := (f v).

(* The following was working in 8.6 *)

Reserved Notation "%% a" (at level 70).
Record R :=
  {g : forall {A} (a:A), a=a where "%% x" := (g x);
   k : %% 0 = eq_refl}.

(* An extra example *)

Module A.
Inductive I {A:Type} := C : # 0 -> I where "# I" := (I = I) : I_scope.
End A.
