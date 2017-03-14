Require Import EquivDec Equivalence List Program.
Require Import Relation_Definitions.
Import ListNotations.
Generalizable All Variables.

Fixpoint removeV `{eqDecV : @EqDec V eqV equivV}`(x : V) (l : list V) : list V :=
  match l with
  | nil => nil
  | y::tl => if (equiv_dec x y) then removeV x tl else y::(removeV x tl)
  end.

(* Function version *)

Fail Function nubV {V:Type}{eqV:relation V}{equivV:@Equivalence V eqV}{eqDecV : @EqDec V eqV equivV} (l : list V) { measure length l} :=
    match l with
      | nil => nil
      | x::xs => x :: @nubV V eqV equivV eqDecV (removeV x xs)
    end. (* should succeed *)

(* Program version *)

Fail Program Fixpoint nubV `{eqDecV : @EqDec V eqV equivV} (l : list V)
        {  measure (length l) } :=
    match l with
      | nil => nil
      | x::xs => x :: @nubV V eqV equivV eqDecV (removeV x xs) _
    end. (* should succeed *)
(*
-----------------------------------------------------------------
Both versions work with 8.4pl6 and give the expected obligation.

In 8.5 and 8.5pl1:
- Function version gives Error: Conversion test raised an anomaly
- Program version gives:
File "./PbProgram.v", line 14, characters 31-32:
Error: Cannot infer this placeholder of type
"Type" in environment:
V : Type
eqV : relation V
equivV : Equivalence eqV
eqDecV : EqDec V eqV
l : list V*)
