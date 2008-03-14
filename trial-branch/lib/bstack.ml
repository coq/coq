(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

(* Queues of a given length *)

open Util

type 'a t = {mutable pos : int;
             mutable size : int;
             stack : 'a array}

let create depth e =
  {pos = 0;
   size = 1;
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
  bs.stack.(bs.pos) <- e
	  
let pop bs =
  if bs.size > 1 then begin
    bs.size <- bs.size - 1; 
    let oldpos = bs.pos in
    decr_pos bs;
    (* Release the memory at oldpos, by coyping what is at new pos *)
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

let depth bs = bs.size
