(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** {5 Basic types} *)

type t = Compat.Loc.t

exception Exc_located of t * exn

type 'a located = t * 'a

(** {5 Location manipulation} *)

(** This is inherited from CAMPL4/5. *)

val unloc : t -> int * int
val make_loc : int * int -> t
val ghost : t
val merge : t -> t -> t
val raise : t -> exn -> 'a

(** {5 Location utilities} *)

val located_fold_left : ('a -> 'b -> 'a) -> 'a -> 'b located -> 'a
val located_iter2 : ('a -> 'b -> unit) -> 'a located -> 'b located -> unit

val down_located : ('a -> 'b) -> 'a located -> 'b
(** Projects out a located object *)

val pr_located : ('a -> Pp.std_ppcmds) -> 'a located -> Pp.std_ppcmds
(** Prints an object surrounded by its commented location *)

(** {5 Backward compatibility} *)

val dummy_loc : t
(** Same as [ghost] *)

val join_loc : t -> t -> t
(** Same as [merge] *)
