(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
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
}

val make : ?fg_color:color -> ?bg_color:color ->
  ?bold:bool -> ?italic:bool -> ?underline:bool ->
  ?negative:bool -> ?style:style -> unit -> style
(** Create a style from the given flags. It is derived from the optional
    [style] argument if given. *)

val merge : style -> style -> style
(** [merge s1 s2] returns [s1] with all defined values of [s2] overwritten. *)

val eval : style -> string
(** Generate an escape sequence from a style. *)

val reset : string
(** This escape sequence resets all attributes. *)

val has_style : Unix.file_descr -> bool
(** Whether an output file descriptor handles styles. Very heuristic, only
    checks it is a terminal. *)

val parse : string -> (string * style) list
(** Parse strings describing terminal styles in the LS_COLORS syntax. For
    robustness, ignore meaningless entries and drops undefined styles. *)
