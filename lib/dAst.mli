(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Lazy AST node wrapper. Only used for [glob_constr] as of today. *)

type ('a, _) thunk =
| Value : 'a -> ('a, 'b) thunk
| Thunk : 'a Lazy.t -> ('a, [ `thunk ]) thunk

type ('a, 'b) t = ('a, 'b) thunk CAst.t

val get : ('a, 'b) t -> 'a
val get_thunk : ('a, 'b) thunk -> 'a

val make : ?loc:Loc.t -> 'a -> ('a, 'b) t
val delay : ?loc:Loc.t -> (unit -> 'a) -> ('a, [ `thunk ]) t

val map : ('a -> 'b) -> ('a, 'c) t -> ('b, 'c) t
val map_with_loc : (?loc:Loc.t -> 'a -> 'b) -> ('a, 'c) t -> ('b, 'c) t
val map_from_loc : (?loc:Loc.t -> 'a -> 'b) -> 'a Loc.located -> ('b, 'c) t

val with_val : ('a -> 'b) -> ('a, 'c) t -> 'b
val with_loc_val : (?loc:Loc.t -> 'a -> 'b) -> ('a, 'c) t -> 'b
