(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names

(** Identifiers and names *)
val pr_id : Id.t -> Pp.std_ppcmds
val pr_name : Name.t -> Pp.std_ppcmds

val make_ident : string -> int option -> Id.t
val repr_ident : Id.t -> string * int option

val atompart_of_id : Id.t -> string  (** remove trailing digits *)
val root_of_id : Id.t -> Id.t (** remove trailing digits, ' and _ *)

val add_suffix : Id.t -> string -> Id.t
val add_prefix : string -> Id.t -> Id.t

val has_subscript    : Id.t -> bool
val lift_subscript   : Id.t -> Id.t
val forget_subscript : Id.t -> Id.t

val out_name : Name.t -> Id.t
(** [out_name] associates [id] to [Name id]. Raises [Failure "Nameops.out_name"]
    otherwise. *)

val name_fold : (Id.t -> 'a -> 'a) -> Name.t -> 'a -> 'a
val name_iter : (Id.t -> unit) -> Name.t -> unit
val name_cons : Name.t -> Id.t list -> Id.t list
val name_app : (Id.t -> Id.t) -> Name.t -> Name.t
val name_fold_map : ('a -> Id.t -> 'a * Id.t) -> 'a -> Name.t -> 'a * Name.t


val pr_lab : Label.t -> Pp.std_ppcmds

(** some preset paths *)

val default_library : DirPath.t

(** This is the root of the standard library of Coq *)
val coq_root : module_ident (** "Coq" *)
val coq_string : string (** "Coq" *)

(** This is the default root prefix for developments which doesn't
   mention a root *)
val default_root_prefix : DirPath.t

(** Metavariables *)
val pr_meta : Term.metavariable -> Pp.std_ppcmds
val string_of_meta : Term.metavariable -> string
