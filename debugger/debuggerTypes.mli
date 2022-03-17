(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Debugger-defined types useful for communicating with IDEs *)

(** The type of coqtop goals *)
type goal = {
  goal_id : string;
  (** Unique goal identifier *)
  goal_hyp : Pp.t list;
  (** List of hypotheses *)
  goal_ccl : Pp.t;
  (** Goal conclusion *)
  goal_name : string option;
  (** User-level goal name *)
}

(** Subset of goals to print. *)
type goal_flags = {
   gf_mode : string;
   gf_fg : bool;
   gf_bg : bool;
   gf_shelved : bool;
   gf_given_up : bool;
 }

type 'a pre_goals = {
  fg_goals : 'a list;
  (** List of the focused goals *)
  bg_goals : ('a list * 'a list) list;
  (** Zipper representing the unfocused background goals *)
  shelved_goals : 'a list;
  (** List of the goals on the shelf. *)
  given_up_goals : 'a list;
  (** List of the goals that have been given up *)
}

type goals = goal pre_goals

(* specific return types *)

type subgoals_rty = goals option
type goals_rty = goals option
type db_stack_rty = (string * (string * int list) option) list
type db_vars_rty = (string * Pp.t) list

val read_in_debug : bool ref (* true=msg read in debug false=read at top level *)
