(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)


(* [minimize_hyps e s1] gives [s2] s.t. [Id.Set.subset s2 s1] is [true]
 * and [keep_hyps e s1] is equal to [keep_hyps e s2].  Inefficient. *)
val minimize_hyps : Environ.env -> Names.Id.Set.t -> Names.Id.Set.t

(* [minimize_unused_hyps e s1] gives [s2] s.t. [Id.Set.subset s2 s1] is [true]
 * and s.t. calling [clear s1] would do the same as [clear s2].  Inefficient. *)
val minimize_unused_hyps : Environ.env -> Names.Id.Set.t -> Names.Id.Set.t

val process_expr :
  Environ.env -> Vernacexpr.section_subset_descr -> Constr.types list ->
    Names.Id.t list

val name_set : Names.Id.t -> Vernacexpr.section_subset_descr -> unit

val to_string : Vernacexpr.section_subset_descr -> string

val get_default_proof_using : unit -> string option
