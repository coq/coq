Require Import EquivDec Equivalence List Program.
Require Import Relation_Definitions.
Import ListNotations.
Generalizable All Variables.

Fixpoint removeV `{eqDecV : @EqDec V eqV equivV}`(x : V) (l : list V) : list V
:=
  match l with
  | nil => nil
  | y::tl => if (equiv_dec x y) then removeV x tl else y::(removeV x tl)
  end.

Lemma remove_le {V:Type}{eqV:relation V}{equivV:@Equivalence V eqV}{eqDecV :
@EqDec V eqV equivV} (xs : list V) (x : V) :
  length (removeV x xs) < length (x :: xs).
  Proof. Admitted.

(* Function version *)
Set Printing Universes.

Require Import Recdef.

Function nubV {V:Type}{eqV:relation V}{equivV:@Equivalence V eqV}{eqDecV :
@EqDec V eqV equivV} (l : list V) { measure length l} :=
    match l with
      | nil => nil
      | x::xs => x :: @nubV V eqV equivV eqDecV (removeV x xs)
    end.
Proof. intros. apply remove_le. Qed.

(* Program version *)

Program Fixpoint nubV `{eqDecV : @EqDec V eqV equivV} (l : list V)
        {  measure (@length V l) lt } :=
    match l with
      | nil => nil
      | x::xs => x :: @nubV V eqV equivV eqDecV (removeV x xs) _
    end.
