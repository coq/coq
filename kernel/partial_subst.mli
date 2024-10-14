(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)


type ('term, 'quality, 'univ) t

val make : int * int * int -> ('term, 'quality, 'univ) t

val add_term : int -> 't -> ('t, 'q, 'u) t -> ('t, 'q, 'u) t
val maybe_add_term : int option -> 't -> ('t, 'q, 'u) t -> ('t, 'q, 'u) t

val add_quality : int -> 'q -> ('t, 'q, 'u) t -> ('t, 'q, 'u) t
val maybe_add_quality : int option -> 'q -> ('t, 'q, 'u) t -> ('t, 'q, 'u) t

val add_univ : int -> 'u -> ('t, 'q, 'u) t -> ('t, 'q, 'u) t
val maybe_add_univ : int option -> 'u -> ('t, 'q, 'u) t -> ('t, 'q, 'u) t

val to_arrays : ('t, 'q, 'u) t -> 't array * 'q array * 'u array

val pr :
    ('t -> Pp.t) -> ('q -> Pp.t) -> ('u -> Pp.t) ->
    ('t, 'q, 'u) t -> Pp.t
