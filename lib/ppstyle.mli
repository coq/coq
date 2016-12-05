(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Highlighting of printers. Used for pretty-printing terms that should be
    displayed on a color-capable terminal. *)

(** {5 Style tags} *)

(** This API is provisional and will likely be refined. *)
type t = Pp.pp_tag

(** Style tags *)

val make : ?style:Terminal.style -> string list -> t
(** Create a new tag with the given name. Each name must be unique. The optional
    style is taken as the default one. *)

(** {5 Manipulating global styles} *)

val get_style : t -> Terminal.style option
(** Get the style associated to a tag from a format tag. *)

val set_style : t -> Terminal.style option -> unit
(** Set a style associated to a tag. *)

val clear_styles : unit -> unit
(** Clear all styles. *)

val parse_config : string -> unit
(** Add all styles from the given string as parsed by {!Terminal.parse}.
    Unregistered tags are ignored. *)

val dump : unit -> (t * Terminal.style option) list
(** Recover the list of known tags together with their current style. *)

(** {5 Tags} *)

val error_tag : t
(** Tag used by the {!Pp.msg_error} function. *)

val warning_tag : t
(** Tag used by the {!Pp.msg_warning} function. *)

val debug_tag : t
(** Tag used by the {!Pp.msg_debug} function. *)
