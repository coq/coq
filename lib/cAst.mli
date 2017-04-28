(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** The ast type contains generic metadata for AST nodes *)
type 'a t = private {
  v   : 'a;
  loc : Loc.t option;
}

val make : ?loc:Loc.t -> 'a -> 'a t

val map : ('a -> 'b) -> 'a t -> 'b t
val map_with_loc : (?loc:Loc.t -> 'a -> 'b) -> 'a t -> 'b t
val map_from_loc : (?loc:Loc.t -> 'a -> 'b) -> 'a Loc.located -> 'b t

val with_val : ('a -> 'b) -> 'a t -> 'b
val with_loc_val : (?loc:Loc.t -> 'a -> 'b) -> 'a t -> 'b
