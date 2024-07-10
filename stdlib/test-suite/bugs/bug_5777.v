From Stdlib.Program Require Import Tactics Utils.
From Stdlib Require Import JMeq Lia.

#[local]
Open Scope program_scope.

Inductive vector (A: Type) : nat -> Type :=
| vcons  {n:nat} : A -> vector A n -> vector A (S n)
| vnil : vector A 0.

Arguments vcons [A n] _ _.
Arguments vnil {A}.

#[program]
Fixpoint drop
         {A:   Type}
         {n:   nat}
         (v:   vector A n)
         (b:   nat | b <= n)
         {struct v}
  : vector A (n - b) :=
  match b, v with
  | 0, v => v
  | S b', vcons _ r => drop r b'
  | _, _ => !
  end.
Next Obligation. lia. Qed.
Next Obligation. lia. Qed.
Next Obligation. Admitted. (* Can we do better? *)
