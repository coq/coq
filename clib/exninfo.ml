(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Enriched exceptions have an additional field at the end of their usual data
    containing a pair composed of the distinguishing [token] and the backtrace
    information. We discriminate the token by pointer equality. *)

module Store = Store.Make ()

type 'a t = 'a Store.field

type info = Store.t

type iexn = exn * info

let make = Store.field
let add = Store.set
let get = Store.get
let null = Store.empty

exception Unique

let dummy = (Unique, Store.empty)

let current : (int * iexn) list ref = ref []
(** List associating to each thread id the latest exception raised by an
    instrumented raise (i.e. {!raise} from this module). It is shared between
    threads, so we must take care of this when modifying it.

    Invariants: all index keys are unique in the list.
*)

let lock = Mutex.create ()

let rec remove_assoc (i : int) = function
| [] -> []
| (j, v) :: rem as l ->
  if i = j then rem
  else
    let ans = remove_assoc i rem in
    if rem == ans then l
    else (j, v) :: ans

let rec find_and_remove_assoc (i : int) = function
| [] -> dummy, []
| (j, v) :: rem as l ->
  if i = j then (v, rem)
  else
    let (r, ans) = find_and_remove_assoc i rem in
    if rem == ans then (r, l)
    else (r, (j, v) :: ans)

let iraise e =
  let () = Mutex.lock lock in
  let id = Thread.id (Thread.self ()) in
  let () = current := (id, e) :: remove_assoc id !current in
  let () = Mutex.unlock lock in
  raise (fst e)

let raise ?info e = match info with
| None ->
  let () = Mutex.lock lock in
  let id = Thread.id (Thread.self ()) in
  let () = current := remove_assoc id !current in
  let () = Mutex.unlock lock in
  raise e
| Some i ->
  let () = Mutex.lock lock in
  let id = Thread.id (Thread.self ()) in
  let () = current := (id, (e, i)) :: remove_assoc id !current in
  let () = Mutex.unlock lock in
  raise e

let find_and_remove () =
  let () = Mutex.lock lock in
  let id = Thread.id (Thread.self ()) in
  let (v, l) = find_and_remove_assoc id !current in
  let () = current := l in
  let () = Mutex.unlock lock in
  v

let info e =
  let (src, data) = find_and_remove () in
  if src == e then
    (** Slightly unsound, some exceptions may not be unique up to pointer
        equality. Though, it should be quite exceptional to be in a situation
        where the following holds:

        1. An argument-free exception is raised through the enriched {!raise};
        2. It is not captured by any enriched with-clause (which would reset
            the current data);
        3. The same exception is raised through the standard raise, accessing
            the wrong data.
    . *)
    data
  else
    (** Mismatch: the raised exception is not the one stored, either because the
        previous raise was not instrumented, or because something went wrong. *)
    Store.empty
