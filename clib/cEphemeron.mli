(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Use case:
     You have a data structure that needs to be marshalled but it contains
     unmarshallable data (like a closure, or a file descriptor).  Actually
     you don't need this data to be preserved by marshalling, it just happens
     to be there.
     You could produced a trimmed down data structure, but then, once
     unmarshalled, you can't used the very same code to process it, unless you
     re-inject the trimmed down data structure into the standard one, using
     dummy values for the unmarshallable stuff.
     Similarly you could change your data structure turning all types [bad]
     into [bad option], then just before marshalling you set all values of type
     [bad option] to [None].  Still this pruning may be expensive and you have
     to code it.

   Desiderata:
     The marshalling operation automatically discards values that cannot be
     marshalled or cannot be properly unmarshalled.

   Proposed solution:
     Turn all occurrences of [bad] into [bad key] in your data structure.
     Use [create bad_val] to obtain a unique key [k] for [bad_val], and store
     [k] in the data structure.  Use [get k] to obtain [bad_val].

     An ['a key] can always be marshalled.  When marshalled, a key loses its
     value.  The function [get] raises Not_found on unmarshalled keys.
     
     If a key is garbage collected, the corresponding value is garbage
     collected too (unless extra references to it exist).
     In short no memory management hassle, keys can just replace their
     corresponding value in the data structure.  *)

type 'a key

val create : 'a -> 'a key

(* May raise InvalidKey *)
exception InvalidKey
val get : 'a key -> 'a

(* These never fail. *)
val iter_opt : 'a key -> ('a -> unit) -> unit
val default : 'a key -> 'a -> 'a

val clear : unit -> unit
