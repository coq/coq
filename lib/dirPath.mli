(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** {1 Directory paths = section names paths } *)

type module_ident = Id.t

type t
(** Type of directory paths. Essentially a list of module identifiers. The
    order is reversed to improve sharing. E.g. A.B.C is ["C";"B";"A"] *)

val equal : t -> t -> bool
(** Equality over directory paths. *)

val compare : t -> t -> int
(** Comparison over directory paths. *)

val hash : t -> int
(** Hash over directory paths. *)

val make : module_ident list -> t
(** Create a directory path. (The list must be reversed). *)

val repr : t -> module_ident list
(** Represent a directory path. (The result list is reversed). *)

val empty : t
(** The empty directory path. *)

val is_empty : t -> bool
(** Test whether a directory path is empty. *)

val initial : t
(** Initial "seed" of the unique identifier generator *)

val hcons : t -> t
(** Hashconsing of directory paths. *)

val to_string : t -> string
(** Print non-empty directory paths as ["coq_root.module.submodule"] *)

val print : t -> Pp.t
