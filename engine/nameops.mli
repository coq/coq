(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
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

(** Metavariables *)
val pr_meta : Constr.metavariable -> Pp.t
val string_of_meta : Constr.metavariable -> string
