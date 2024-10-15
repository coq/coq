(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Streams equipped with a (non-canonical) location function *)

type ('e,'a) t = {
  strm : ('e,'a) Stream.t;
  (* Give the loc of i-th element (counting from 1) and the empty initial interval if 0 *)
  fun_loc : int -> Loc.t;
  (* Remember max token peeked *)
  mutable max_peek : int;
}

let from ?(loc=Loc.(initial ToplevelInput)) f =
  let loct = Hashtbl.create 207 in
  let loct_func loct i = Hashtbl.find loct i in
  let loct_add loct i loc = Hashtbl.add loct i loc in
  let strm =
    let i = ref 0 in
    Stream.from
      (fun e ->
        match f e with
        | None -> None
        | Some (a,loc) ->
        loct_add loct !i loc; incr i; Some a) in
  let fun_loc i = if i = 0 then loc else loct_func loct (i - 1) in
  { strm; max_peek = 0; fun_loc }

let count strm = Stream.count strm.strm

let current_loc strm =
  strm.fun_loc (Stream.count strm.strm)

let max_peek_loc strm =
  strm.fun_loc strm.max_peek

let interval_loc bp ep strm =
  assert (bp <= ep);
  if ep > strm.max_peek then failwith "Not peeked position";
  if bp == ep then
    Loc.after (strm.fun_loc bp) 0 0
  else
    let loc1 = strm.fun_loc (bp + 1) in
    let loc2 = strm.fun_loc ep in
    Loc.merge loc1 loc2

let get_loc n strm =
  strm.fun_loc (n + 1)

let peek e strm =
  let a = Stream.peek e strm.strm in
  if Option.has_some a then strm.max_peek <- max (Stream.count strm.strm + 1) strm.max_peek;
  a

let npeek e n strm =
  let l = Stream.npeek e n strm.strm in
  strm.max_peek <- max (Stream.count strm.strm + List.length l) strm.max_peek;
  l

let peek_nth e n strm =
  let list = Stream.npeek e (n + 1) strm.strm in
  let rec loop list p =
    match list, p with
      x :: _, 0 -> strm.max_peek <- Stream.count strm.strm + n + 1; x
    | _ :: l, p -> loop l (p - 1)
    | [], p -> strm.max_peek <- Stream.count strm.strm + (n - p); raise Stream.Failure
  in
  loop list n

let junk e strm = Stream.junk e strm.strm
let njunk e len strm = Stream.njunk e len strm.strm

let next e strm = Stream.next e strm.strm
