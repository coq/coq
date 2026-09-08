(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module Stream :
sig

type ('e, 'a) t = private { mutable data : ('e, 'a) node }
and ('e, 'a) node =
| Nil
| Cons of 'a * ('e, 'a) t
| Gen of ('e -> 'a option)

val make : ('e -> 'a option) -> ('e, 'a) t
val force : 'e -> ('e, 'a) t -> unit

end =
struct

type ('e, 'a) t = { mutable data : ('e, 'a) node }
and ('e, 'a) node =
| Nil
| Cons of 'a * ('e, 'a) t
| Gen of ('e -> 'a option)

let make f = { data = Gen f }

let force e s = match s.data with
| Nil -> ()
| Cons (x, s) -> ()
| Gen f as gen ->
  let v = f e in
  match v with
  | None -> s.data <- Nil
  | Some x ->
    let next = { data = gen } in
    s.data <- Cons (x, next)

end

(** Streams equipped with a (non-canonical) location function *)

type ('e, 'a) t = {
  mutable strm : ('e, 'a * Loc.t) Stream.t;
  mutable loc : Loc.t;
  mutable count : int;
}

type position = Position : int * Loc.t * ('e, 'a * Loc.t) Stream.t -> position

let from ?(loc=Loc.(initial ToplevelInput)) f =
  let strm = Stream.make f in
  { strm; loc; count = 0; }

let count s = s.count

let current s =
  Position (s.count, s.loc, s.strm)

let current_loc s = s.loc

let max_peek_loc s =
  let open Stream in
  let rec get_max cur s = match s.data with
  | Nil -> cur
  | Cons ((_, loc), s) -> get_max loc s
  | Gen _ -> cur
  in
  get_max s.loc s.strm

let get_relative_loc n strm =
  let open Stream in
  let () = assert (0 <= n) in
  let rec get_pos n s = match s.data with
  | Nil | Gen _ -> assert false
  | Cons ((_, loc), s) ->
    if Int.equal n 0 then loc
    else get_pos (n - 1) s
  in
  get_pos n strm.strm

let peek e s =
  let s = s.strm in
  let () = Stream.force e s in
  let open Stream in
  match s.data with
  | Nil -> None
  | Cons ((x, _), _) -> Some x
  | Gen _ -> assert false

let npeek e n s =
  let rec npeek n s =
    if Int.equal n 0 then []
    else
      let open Stream in
      let () = Stream.force e s in
      match s.Stream.data with
      | Nil -> []
      | Cons ((x, _), s) ->
        let l = npeek (n - 1) s in
        x :: l
      | Gen _ -> assert false
  in
  npeek n s.strm

let peek_nth e n strm =
  let list = npeek e (n + 1) strm in
  List.nth_opt list n

let junk e strm =
  let s = strm.strm in
  let () = Stream.force e s in
  let open Stream in
  let () = strm.count <- strm.count + 1 in
  match s.data with
  | Nil -> ()
  | Cons ((x, loc), next) ->
    let () = strm.strm <- next in
    strm.loc <- loc
  | Gen _ -> assert false

let rec njunk e len strm =
  if Int.equal len 0 then ()
  else
    let () = junk e strm in
    njunk e (len - 1) strm

let next e strm = match peek e strm with
| None -> None
| Some v ->
  let () = junk e strm in
  Some v

let pos_offset (Position (i, _, _)) = i
let pos_current (Position (_, cur, _)) = cur
let pos_next (Position (_, _, strm)) = match strm.Stream.data with
| Stream.Cons ((_, loc), _) -> loc
| Stream.Nil | Stream.Gen _ -> assert false
