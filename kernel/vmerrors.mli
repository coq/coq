(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type error

val pr_error : error -> Pp.t

val too_large_code : unit -> 'a

val check_compilable_ind : name:Names.Id.t -> mind_nb_args:int -> mind_nb_constant:int -> unit

exception CompileError of error
