(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2013     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

type 'a getter = unit -> 'a
type 'a installer = ('a getter) -> unit

val new_counter :
  'a -> incr:('a -> 'a) -> build:('a -> 'b) -> 'b getter * 'b installer

