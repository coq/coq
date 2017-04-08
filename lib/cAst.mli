(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** The ast type contains generic metadata for AST nodes *)
type 'a ast = private {
  v   : 'a;
  loc : Loc.t option;
}

val make : ?loc:Loc.t -> 'a -> 'a ast

val map : ('a -> 'b) -> 'a ast -> 'b ast
val map_with_loc : (?loc:Loc.t -> 'a -> 'b) -> 'a ast -> 'b ast
val map_from_loc : (?loc:Loc.t -> 'a -> 'b) -> 'a Loc.located -> 'b ast

val with_val : ('a -> 'b) -> 'a ast -> 'b
val with_loc_val : (?loc:Loc.t -> 'a -> 'b) -> 'a ast -> 'b
