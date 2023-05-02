module Align : sig
  type t =
    | Left
    | MidLeft
    | Middle
    | MidRight
    | Right
  (** Type of Alignments. During the justification phase of printing, the
    alignment decides how much space should be left on the left and right of the
    data. *)
end

type sized_string = { str : string; size : int }
(** String with a display size. [size] is usually but not always
    [String.length str] (or rather unicode length but currently no unicode support). *)

type header = sized_string
type row = sized_string list list

(** Print the table with optional alignment parameters. The alignment parametrs
    must have the same shape as the corresponding data. Due to a limitation of
    OCaml, the entire thing has to be thunked in order for optional arguments to
    come at the end. *)
val print : header list
  -> row
  -> row list
  -> ?align_headers:Align.t list
  -> ?align_top:Align.t list list
  -> ?align_rows:Align.t list list
  -> unit
  -> string

type raw_header = string
type raw_row = string list list

val raw_str : string -> sized_string
(** string which displays as itself *)

val raw_row : raw_row -> row

val raw_print : raw_header list
  -> raw_row
  -> raw_row list
  -> ?align_headers:Align.t list
  -> ?align_top:Align.t list list
  -> ?align_rows:Align.t list list
  -> unit
  -> string
(** Print with display size = string length *)
