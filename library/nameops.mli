(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names

(** Identifiers and names *)

val make_ident : string -> int option -> Id.t
val repr_ident : Id.t -> string * int option

val atompart_of_id : Id.t -> string  (** remove trailing digits *)
val root_of_id : Id.t -> Id.t (** remove trailing digits, ' and _ *)

val add_suffix : Id.t -> string -> Id.t
val add_prefix : string -> Id.t -> Id.t

(** Below, by {i subscript} we mean a suffix composed solely from (decimal) digits. *)

val has_subscript       : Id.t -> bool

val increment_subscript : Id.t -> Id.t
(** Return the same identifier as the original one but whose {i subscript} is incremented.
    If the original identifier does not have a suffix, [0] is appended to it.

    Example mappings:

    [bar]   ↦ [bar0]

    [bar0]  ↦ [bar1]

    [bar00] ↦ [bar01]

    [bar1]  ↦ [bar2]

    [bar01] ↦ [bar01]

    [bar9]  ↦ [bar10]

    [bar09] ↦ [bar10]

    [bar99] ↦ [bar100]
*)

val forget_subscript    : Id.t -> Id.t

module Name : sig

  include module type of struct include Names.Name end

  exception IsAnonymous

  val fold_left : ('a -> Id.t -> 'a) -> 'a -> Name.t -> 'a
  (** [fold_left f na a] is [f id a] if [na] is [Name id], and [a] otherwise. *)

  val fold_right : (Id.t -> 'a -> 'a) -> Name.t -> 'a -> 'a
  (** [fold_right f a na] is [f a id] if [na] is [Name id], and [a] otherwise. *)

  val iter : (Id.t -> unit) -> Name.t -> unit
  (** [iter f na] does [f id] if [na] equals [Name id], nothing otherwise. *)

  val map : (Id.t -> Id.t) -> Name.t -> t
  (** [map f na] is [Anonymous] if [na] is [Anonymous] and [Name (f id)] if [na] is [Name id]. *)

  val fold_left_map : ('a -> Id.t -> 'a * Id.t) -> 'a -> Name.t -> 'a * Name.t
  (** [fold_left_map f a na] is [a',Name id'] when [na] is [Name id] and [f a id] is [(a',id')].
      It is [a,Anonymous] otherwise. *)

  val fold_right_map : (Id.t -> 'a -> Id.t * 'a) -> Name.t -> 'a -> Name.t * 'a
  (** [fold_right_map f na a] is [Name id',a'] when [na] is [Name id] and [f id a] is [(id',a')].
      It is [Anonymous,a] otherwise. *)

  val get_id : Name.t -> Id.t
  (** [get_id] associates [id] to [Name id]. @raise IsAnonymous otherwise. *)

  val pick : Name.t -> Name.t -> Name.t
  (** [pick na na'] returns [Anonymous] if both names are [Anonymous].
      Pick one of [na] or [na'] otherwise. *)

  val cons : Name.t -> Id.t list -> Id.t list
  (** [cons na l] returns [id::l] if [na] is [Name id] and [l] otherwise. *)

  val to_option : Name.t -> Id.t option
  (** [to_option Anonymous] is [None] and [to_option (Name id)] is [Some id] *)

end

val out_name : Name.t -> Id.t
(** @deprecated Same as [Name.get_id] *)

val name_fold : (Id.t -> 'a -> 'a) -> Name.t -> 'a -> 'a
(** @deprecated Same as [Name.fold_right] *)

val name_iter : (Id.t -> unit) -> Name.t -> unit
(** @deprecated Same as [Name.iter] *)

val name_app : (Id.t -> Id.t) -> Name.t -> Name.t
(** @deprecated Same as [Name.map] *)

val name_fold_map : ('a -> Id.t -> 'a * Id.t) -> 'a -> Name.t -> 'a * Name.t
(** @deprecated Same as [Name.fold_left_map] *)

val name_max : Name.t -> Name.t -> Name.t
(** @deprecated Same as [Name.pick] *)

val name_cons : Name.t -> Id.t list -> Id.t list
(** @deprecated Same as [Name.cons] *)

val pr_name : Name.t -> Pp.t
(** @deprecated Same as [Name.print] *)

val pr_id : Id.t -> Pp.t
(** @deprecated Same as [Names.Id.print] *)

val pr_lab : Label.t -> Pp.t

(** some preset paths *)

val default_library : DirPath.t

(** This is the root of the standard library of Coq *)
val coq_root : module_ident (** "Coq" *)
val coq_string : string (** "Coq" *)

(** This is the default root prefix for developments which doesn't
   mention a root *)
val default_root_prefix : DirPath.t

(** Metavariables *)
val pr_meta : Term.metavariable -> Pp.t
val string_of_meta : Term.metavariable -> string
