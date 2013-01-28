Set Implicit Arguments.

Inductive Bit := O | I.

Inductive BitString: nat -> Set :=
| bit: Bit -> BitString 0
| bitStr: forall n: nat, Bit -> BitString n -> BitString (S n).

Definition BitOr (a b: Bit) :=
  match a, b with
  | O, O => O
  | _, _ => I
  end.

(* Should fail with an error; used to failed in 8.4 and trunk with
   anomaly Evd.define: cannot define an evar twice *)

Fail Fixpoint StringOr (n m: nat) (a: BitString n) (b: BitString m) :=
  match a with
  | bit a' =>
      match b with
      | bit b' => bit (BitOr a' b')
      | bitStr b' bT => bitStr b' (StringOr (bit a') bT)
      end
  | bitStr a' aT =>
      match b with
      | bit b' => bitStr a' (StringOr aT (bit b'))
      | bitStr b' bT => bitStr (BitOr a' b') (StringOr aT bT)
      end
  end.
