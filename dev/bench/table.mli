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

type header = string
type row = string list list

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
  -> header
