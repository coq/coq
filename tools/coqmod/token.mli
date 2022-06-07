(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module Loc : sig
  (** Locations of tokens. [start] is the Lexing.position value of the begining
      of the token and [finish] is the Lexing.position value of the end of a
      token. *)
  type t
  (* = {start : Lexing.position; finish : Lexing.position} *)

  val to_string :
    ?sep:string ->
    ?range_sep:string ->
    ?line:string ->
    ?lines:string ->
    ?char:string ->
    ?chars:string ->
    t ->
    string
  (** Locations can be converted to strings with some configuarability. If the
        line numbers or coloumn numbers are the same, then the range is printed
        with a single number. If they are different they are printed as [1-4]
        seperated by a [range_sep].

      - [sep] the seperator between lines and coloumns (defaults to [", "])
      - [range_sep] the seperator when printing a range (defaults to ["-"])
      - [line] the singular label for lines (defaults to ["Ln"])
      - [lines] the plural label for lines (defaults to ["Ln"])
      - [char] the singular label for coloumns/characters (defaults to ["Col"])
      - [chars] the plural label for coloumns/characters (defaults to ["Col"]) *)

  val dummy : t
  (** Return a dummy location consisting of [Lexing.dummy_pos] values. *)

  val of_lexbuf : Lexing.lexbuf -> t
  (** The location of a recently parsed token for a given [Lexing.lexbuf]. *)

  val pos_to_sexp : Lexing.position -> Csexp.t
  (** Convert a [Lexing.position] to a [Csexp.t]. *)

  val to_sexp : t -> Csexp.t
  (** Convert a location to a [Csexp.t]. *)
end

module Module : sig
  (** Tokens for modules consist of a location [loc] of the token and a string
    [logical_name] for the value. *)
  type t

  val make : Loc.t -> string -> t
  (** Construct a [Module.t] with given location and logical name. *)

  val to_string : t -> string
  (** Displays the [logical_name] of a module. *)

  val to_sexp : t -> Csexp.t
  (** Convert a module to a [Csexp.t] containing the location and
    [logical_name]. *)
end

(** Abstract type of lexed dependency tokens. *)
type t

val get_filename : t -> string
(** Name of the file the tokens were lexed in. *)

val empty : t
(** Empty token. *)

val set_filename : t -> string -> t
(** Set the filename of a token. *)

val add_from_list : t -> Module.t option -> Module.t list -> t
(** Add a list of modules to a token sharing the same prefix. *)

val add_require : t -> Module.t -> t
(** Add a single module to a token. *)

val add_require_list : t -> Module.t list -> t
(** Add a list of modules to a token. *)

val add_declare_list : t -> Module.t list -> t
(** Add a list of OCaml modules to a token. *)

val add_load : t -> Loc.t -> string -> t
(** Add a physical load to a token. *)

val add_extrdep : t -> Loc.t -> Module.t -> string -> t
(** Add an extra dependency to a token. *)

val to_string : t -> string
(** Convert a token to a string. This will print a readable document. *)

val to_sexp : t -> Csexp.t
(** Convert the token to a [Csexp.t]. *)

val sort_uniq : t -> t
(** Sort the entries of the token unique upto non-location data. *)

module Sexp : sig
  val pp : Format.formatter -> Csexp.t -> unit
  (** Pretty printer for serial expresions of tokens. *)
end
