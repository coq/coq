(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Hashtbl

module type PHashtable =
  sig
    type 'a t
    type key

    val create : int -> string -> 'a t
    (** [create i f] creates an empty persistent table
        with initial size i associated with file [f] *)


    val open_in : string -> 'a t
    (** [open_in f] rebuilds a table from the records stored in file [f].
        As marshaling is not type-safe, it migth segault.
    *)

    val find : 'a t -> key -> 'a
    (** find has the specification of Hashtable.find *)

    val add  : 'a t -> key -> 'a -> unit
    (** [add tbl key elem] adds the binding [key] [elem] to the table [tbl].
        (and writes the binding to the file associated with [tbl].)
        If [key] is already bound, raises KeyAlreadyBound *)

    val close : 'a t -> unit
    (** [close tbl] is closing the table.
        Once closed, a table cannot be used.
        i.e, find,add will raise UnboundTable *)

    val memo : string -> (key -> 'a) -> (key -> 'a)
      (** [memo cache f] returns a memo function for [f] using file [cache] as persistent table.
          Note that the cache will only be loaded when the function is used for the first time *)

  end

module PHashtable(Key:HashedType) : PHashtable with type key = Key.t
