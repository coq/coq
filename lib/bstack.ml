(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Util

type 'a t = {mutable depth : int option;
             mutable stack : 'a list}

let create depth = {depth = depth;
                 stack = []}

let set_depth bs n = bs.depth <- n

let safe_chop_list len l =
  if List.length l <= len then (l,[]) else list_chop len l
        
let push bs e =
  match bs.depth with
    | None -> bs.stack <- e :: bs.stack
    | Some d -> bs.stack <- fst(safe_chop_list d (e :: bs.stack))
	  
let pop bs =
  match bs.stack with
    | [] -> None
    | h::tl -> (bs.stack <- tl; Some h)

let top bs =
  match bs.stack with
    | [] -> None
    | h::_ -> Some h
	  
let app_push bs f =
  match bs.stack with
    | [] -> error "Nothing on the stack"
    | h::_ -> push bs (f h)

let app_repl bs f =
  match bs.stack with
    | [] -> error "Nothing on the stack"
    | h::t -> bs.stack <- (f h)::t

let is_empty bs = bs.stack = []

let depth bs = List.length bs.stack
