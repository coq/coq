(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Constr

type t
(** Hashconsed constr in an implicit environment,
    keeping variables which have different types and bodies separate.

    For instance the [x] subterms in [fun x : bool => x] and [fun x : nat => x] are different
    (and have different hashes modulo accidental collision)
    and the [x] subterms in [fun (y:nat) (x:bool) => x] and [fun (x:bool) (y:nat) => x] are different
    (one is [Rel 1], the other is [Rel 2])
    but the [x] subterms in [fun (y:nat) (x:bool) => x] and [fun (y:bool) (x:bool) => x] are shared.

    This allows using it as a cache key while typechecking.

    Hashconsing information of subterms is also kept. *)

val self : t -> constr

val kind : t -> (t,t,Sorts.t,UVars.Instance.t,Sorts.relevance) kind_of_term

val refcount : t -> int
(** How many times this term appeared as a subterm of the argument to [of_constr]. *)

val of_constr : Environ.env -> constr -> t

(* May not be used on Rel! (subterms can be rels) *)
val of_kind_nohashcons : (t,t,Sorts.t,UVars.Instance.t,Sorts.relevance) kind_of_term -> t
(** Build a [t] without hashconsing. Its refcount may be 1 even if
    an identical term was already seen.

    May not be used to build [Rel].

    This is intended for the reconstruction of the inductive type when checking CaseInvert. *)

module Tbl : sig
  (** Imperative tables indexed by [HConstr.t].
      The interfaces exposed are the same as [Hashtbl]
      but are not guaranteed to be implemented by [Hashtbl]. *)

  type key = t

  type 'a t

  val find_opt : 'a t -> key -> 'a option

  val add : 'a t -> key -> 'a -> unit

  val create : unit -> 'a t
end

val hcons : t -> Constr.t
