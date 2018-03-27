(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type color = [
  `DEFAULT
| `BLACK
| `RED
| `GREEN
| `YELLOW
| `BLUE
| `MAGENTA
| `CYAN
| `WHITE
| `LIGHT_BLACK
| `LIGHT_RED
| `LIGHT_GREEN
| `LIGHT_YELLOW
| `LIGHT_BLUE
| `LIGHT_MAGENTA
| `LIGHT_CYAN
| `LIGHT_WHITE
| `INDEX of int
| `RGB of (int * int * int)
]

type style = {
  fg_color : color option;
  bg_color : color option;
  bold : bool option;
  italic : bool option;
  underline : bool option;
  negative : bool option;
  prefix : string option;
  suffix : string option;
}

val make : ?fg_color:color -> ?bg_color:color ->
  ?bold:bool -> ?italic:bool -> ?underline:bool ->
  ?negative:bool -> ?style:style ->
  ?prefix:string -> ?suffix:string -> unit -> style
(** Create a style from the given flags. It is derived from the optional
    [style] argument if given. *)

val merge : style -> style -> style
(** [merge s1 s2] returns [s1] with all defined values of [s2] overwritten. *)

val diff : style -> style -> style
(** [diff s1 s2] returns the differences between [s1] and [s2]. *)

val repr : style -> int list
(** Generate the ANSI code representing the given style. *)

val eval : style -> string
(** Generate an escape sequence from a style. *)

val reset : string
(** This escape sequence resets all attributes. *)

val reset_style : style
(** The default style *)

val has_style : Unix.file_descr -> bool
(** Whether an output file descriptor handles styles. Very heuristic, only
    checks it is a terminal. *)

val parse : string -> (string * style) list
(** Parse strings describing terminal styles in the LS_COLORS syntax. For
    robustness, ignore meaningless entries and drops undefined styles. *)
