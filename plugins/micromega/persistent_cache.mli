(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Hashtbl

module type PHashtable = sig
  type 'a t
  type key

  (** [open_in f] rebuilds a table from the records stored in file [f].
        As marshaling is not type-safe, it might segfault.
    *)
  val open_in : string -> 'a t

  (** find has the specification of Hashtable.find *)
  val find : 'a t -> key -> 'a

  (** [add tbl key elem] adds the binding [key] [elem] to the table [tbl].
        (and writes the binding to the file associated with [tbl].)
        If [key] is already bound, raises KeyAlreadyBound *)
  val add : 'a t -> key -> 'a -> unit

  (** [memo cache f] returns a memo function for [f] using file [cache] as persistent table.
          Note that the cache will only be loaded when the function is used for the first time *)
  val memo : string -> (key -> 'a) -> key -> 'a

  (** [memo cache cond f] only use the cache if [cond k] holds for the key [k].  *)
  val memo_cond : string -> (key -> bool) -> (key -> 'a) -> key -> 'a
end

module PHashtable (Key : HashedType) : PHashtable with type key = Key.t
