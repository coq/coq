(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Ltac2.Init.

(** * Boolean operators *)

Ltac2 and x y :=
  match x with
  | true => y
  | false => false
  end.

Ltac2 or x y :=
  match x with
  | true => true
  | false => y
  end.

Ltac2 impl x y :=
  match x with
  | true => y
  | false => true
  end.

Ltac2 neg x :=
  match x with
  | true => false
  | false => true
  end.

Ltac2 xor x y :=
  match x with
  | true
    => match y with
       | true => false
       | false => true
       end
  | false
    => match y with
       | true => true
       | false => false
       end
  end.

Ltac2 eq x y :=
  match x with
  | true
    => match y with
       | true => true
       | false => false
       end
  | false
    => match y with
       | true => false
       | false => true
       end
  end.

(** * Boolean operators with lazy evaluation of the second argument *)

Ltac2 Notation "lazy_and" x(tactic(0)) y(thunk(tactic(0))) : 1 :=
  match x with
  | true => y ()
  | false => false
  end.

Ltac2 Notation "lazy_or" x(tactic(0)) y(thunk(tactic(0))) : 1 :=
  match x with
  | true => true
  | false => y ()
  end.

Ltac2 Notation "lazy_impl" x(tactic(0)) y(thunk(tactic(0))) : 1 :=
  match x with
  | true => y ()
  | false => true
  end.

(** * Notations for if constructs *)

(** if then - this only works for tactics returning a unit since false returns unit *)

(** Note: the arguments are tactic(5) = matches and lets,
    The if term itself is tactic(6) = semicolon tactic sequences *)

Ltac2 Notation "if_bool" cond(tactic(5)) "then" true_tac(thunk(tactic(5))) : 6 :=
  match cond with
  | true => true_tac ()
  | false => ()
end.

(** if then else - the then and else branch can return arbitrary types *)

Ltac2 Notation "if_bool" cond(tactic(5)) "then" true_tac(thunk(tactic(5))) "else" false_tac(thunk(tactic(5))) : 6 :=
  match cond with
  | true => true_tac ()
  | false => false_tac ()
end.
