(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2011     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

(* Queues of a given length *)

open Util

(* - size  is the count of elements actually in the queue
   - depth is the the amount of elements pushed in the queue (and not popped)
   in particular, depth >= size always and depth > size if the queue overflowed
   (and forgot older elements)
 *)

type 'a t = {mutable pos : int;
             mutable size : int;
             mutable depth : int;
             stack : 'a array}

let create depth e =
  {pos = 0;
   size = 1;
   depth = 1;
   stack = Array.create depth e}

(*
let set_depth bs n = bs.depth <- n
*)

let incr_pos bs =
  bs.pos <- if bs.pos = Array.length bs.stack - 1 then 0 else bs.pos + 1

let incr_size bs =
  if bs.size < Array.length bs.stack then bs.size <- bs.size + 1

let decr_pos bs =
  bs.pos <- if bs.pos = 0 then Array.length bs.stack - 1 else bs.pos - 1

let push bs e =
  incr_pos bs;
  incr_size bs;
  bs.depth <- bs.depth + 1;
  bs.stack.(bs.pos) <- e

let pop bs =
  if bs.size > 1 then begin
    bs.size <- bs.size - 1;
    bs.depth <- bs.depth - 1;
    let oldpos = bs.pos in
    decr_pos bs;
    (* Release the memory at oldpos, by copying what is at new pos *)
    bs.stack.(oldpos) <- bs.stack.(bs.pos)
  end

let top bs =
  if bs.size >= 1 then bs.stack.(bs.pos)
  else error "Nothing on the stack"

let app_push bs f =
  if bs.size = 0 then error "Nothing on the stack"
  else push bs (f (bs.stack.(bs.pos)))

let app_repl bs f =
  if bs.size = 0 then error "Nothing on the stack"
  else bs.stack.(bs.pos) <- f (bs.stack.(bs.pos))

let depth bs = bs.depth

let size bs = bs.size
