Declare ML Module "numeral_notation_plugin".
Require Import BinNums.

(** ** Parsing and Printing digit strings as type nat *)

Fixpoint pos_pred_double x :=
  match x with
  | xI p => xI (xO p)
  | xO p => xI (pos_pred_double p)
  | xH => xH
  end.

Definition nat_of_Z x :=
  match x with
  | Z0 => Some O
  | Zpos p =>
      let fix iter p a :=
        match p with
        | xI p0 => a + iter p0 (a + a)
        | xO p0 => iter p0 (a + a)
        | xH => a
        end
      in
      Some (iter p (S O))
  | Zneg p => None
  end.

Fixpoint pos_succ x :=
  match x with
  | xI p => xO (pos_succ p)
  | xO p => xI p
  | xH => xO xH
  end.

Definition Z_succ x :=
  match x with
  | Z0 => Zpos xH
  | Zpos x => Zpos (pos_succ x)
  | Zneg x =>
      match x with
      | xI p => Zneg (xO p)
      | xO p => Zneg (pos_pred_double p)
      | xH => Z0
      end
  end.

Fixpoint Z_of_nat n :=
  match n with
  | O => Z0
  | S p => Z_succ (Z_of_nat p)
  end.

(** The 1st conversion must either have type [Z->nat] or [Z->option nat].
  The 2nd one must either have type [nat->Z] or [nat->option Z]. *)

Numeral Notation nat nat_of_Z Z_of_nat : nat_scope
  (warning after 5000).
