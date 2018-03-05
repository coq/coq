(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type form=
    Atom of int
  | Arrow of form * form
  | Bot
  | Conjunct of form * form
  | Disjunct of form * form

type proof =
    Ax of int
  | I_Arrow of proof
  | E_Arrow of int*int*proof
  | D_Arrow of int*proof*proof
  | E_False of int
  | I_And of proof*proof
  | E_And of int*proof
  | D_And of int*proof
  | I_Or_l of proof
  | I_Or_r of proof
  | E_Or of int*proof*proof
  | D_Or of int*proof
  | Pop of int*proof

type state

val project: state -> proof

val init_state : ('a * form * 'b)  list -> form -> state

val branching: state -> state list

val success: state -> bool

val pp: state -> Pp.t

val pr_form : form -> Pp.t

val reset_info : unit -> unit

val pp_info : unit -> unit
