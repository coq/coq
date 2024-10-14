(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** The purpose of the solver is to generate *all* the integer solutions
    of a system of linear equations of the following form:
    1- all the variables are positive
    2- all the coefficients are positive

    We expect the systems and the number of solutions to be small.
    This motivates a simple solver which performs
    1 - interval analysis
    2 - substitutions
    3 - enumeration
*)


(** [system] represents a system of equation.
    Each equation is indexed by a unique identifier [id] (an integer).
*)

type system

(** [var] is the type of variables *)
type var = int

(** [id] are used to identify equations in a system *)
type id = int

(** An equation [eqn] is of the form a1.x1 + ... + an.xn = a0
    where the ai are integer coefficients and xi are variables.
 *)
type eqn

(** [output_equations o l] prints the list of equations *)
val output_equations : out_channel -> eqn list -> unit

(** [empty] is the system with no equation *)
val empty : system

(** [set_constant i c s] returns the equation [i]
    of the system [s] where the constant a0 is set to [c] *)
val set_constant : id -> int -> system -> eqn

(** [make_mon i x a s] augments the system [s]
    with the equation a.x = 0 indexed by i *)
val make_mon : id -> var -> int -> system -> system

(** [merge s1 s2] returns a system [s] such that
    the equation i is obtained by adding
    of the equations s1(i) and s2(i) i.e.
    s(i) = s1(i) + s2(i)
    NB: the operation is only well-defined if
    the variables in s1(i) and s2(i) is disjoint
*)
val merge : system -> system -> system

(** [solution] assigns a value to each variable *)
type solution = (var * int) list

(** [output_solutions o l] outputs the list of solutions *)
val output_solutions : out_channel -> solution list -> unit

(** [solve_and_enum l] solves the system of equations
    and enumerate  all the solutions *)
val solve_and_enum : eqn list -> solution list
