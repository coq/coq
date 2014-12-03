(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(** Enriched exceptions have an additional field at the end of their usual data
    containing a pair composed of the distinguishing [token] and the backtrace
    information. We discriminate the token by pointer equality. *)

module Store = Store.Make(struct end)

type 'a t = 'a Store.field

type info = Store.t

type iexn = exn * info

let make = Store.field
let add = Store.set
let get = Store.get
let null = Store.empty

exception Unique

let dummy = (Unique, Store.empty)

let current = ref dummy

let iraise e =
  let () = current := e in
  raise (fst e)

let raise ?info e = match info with
| None -> raise e
| Some i -> current := (e, i); raise e

let info e =
  let (src, data) = !current in
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
    let () = current := dummy in
    data
  else
    let () = current := dummy in
    Store.empty
