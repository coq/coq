(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
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

val eq : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
