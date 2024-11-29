(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Ltac2.Init.

Ltac2 @ external print : message -> unit := "rocq-runtime.plugins.ltac2" "print".

Ltac2 @ external of_string : string -> message := "rocq-runtime.plugins.ltac2" "message_of_string".

Ltac2 @ external to_string : message -> string := "rocq-runtime.plugins.ltac2" "message_to_string".

Ltac2 @ external of_int : int -> message := "rocq-runtime.plugins.ltac2" "message_of_int".

Ltac2 @ external of_ident : ident -> message := "rocq-runtime.plugins.ltac2" "message_of_ident".

Ltac2 @ external of_constr : constr -> message := "rocq-runtime.plugins.ltac2" "message_of_constr".
(** Panics if there is more than one goal under focus. *)

Ltac2 @ external of_exn : exn -> message := "rocq-runtime.plugins.ltac2" "message_of_exn".
(** Panics if there is more than one goal under focus. *)

Ltac2 @ external concat : message -> message -> message := "rocq-runtime.plugins.ltac2" "message_concat".

(** Boxing primitives. They are translated to OCaml "Format" boxes,
    see https://ocaml.org/docs/formatting-text **)

Ltac2 @external force_new_line : message := "rocq-runtime.plugins.ltac2" "message_force_new_line".
(** Force writing on a new line after this.
    Warning: partially reinitialises the pretty-printing engine,
    potentially leading to bad printing afterwards.
    Prefer using a break hint inside a vertical box. *)

Ltac2 @external break : int -> int -> message := "rocq-runtime.plugins.ltac2" "message_break".
(** General break hint: [break n i] either prints [n] spaces or splits
    the line adding [i] to the current indentation. *)

Ltac2 @external space : message := "rocq-runtime.plugins.ltac2" "message_space".
(** Breaking space. Equivalent to [break 1 0]. *)

Ltac2 @external hbox : message -> message := "rocq-runtime.plugins.ltac2" "message_hbox".
(** Horizontal box. Break hints in a horizontal box never split the
    line (nested boxes inside the horizontal box may allow line
    splitting). *)

Ltac2 @external vbox : int -> message -> message := "rocq-runtime.plugins.ltac2" "message_vbox".
(** Vertical box. Every break hint in a vertical box splits the line.
    The [int] is added to the current indentation when splitting the line. *)

Ltac2 @external hvbox : int -> message -> message := "rocq-runtime.plugins.ltac2" "message_hvbox".
(** Horizontal/vertical box. Behaves as a horizontal box if it fits on
    a single line, otherwise behaves as a vertical box (using the
    given [int]). *)

Ltac2 @external hovbox : int -> message -> message := "rocq-runtime.plugins.ltac2" "message_hovbox".
(** Horizonal-or-vertical box. Prints as much as possible on each
    line, splitting the line at break hints when there is no more room
    on the line (see "Printing Width" option). The [int] is added to
    the indentation when splitting the line. *)

Module Format.

(** Only for internal use. *)

Ltac2 @ external stop : ('a, 'b, 'c, 'a) format := "rocq-runtime.plugins.ltac2" "format_stop".

Ltac2 @ external string : ('a, 'b, 'c, 'd) format ->
  (string -> 'a, 'b, 'c, 'd) format := "rocq-runtime.plugins.ltac2" "format_string".

Ltac2 @ external int : ('a, 'b, 'c, 'd) format ->
  (int -> 'a, 'b, 'c, 'd) format := "rocq-runtime.plugins.ltac2" "format_int".

Ltac2 @ external constr : ('a, 'b, 'c, 'd) format ->
  (constr -> 'a, 'b, 'c, 'd) format := "rocq-runtime.plugins.ltac2" "format_constr".

Ltac2 @ external ident : ('a, 'b, 'c, 'd) format ->
  (ident -> 'a, 'b, 'c, 'd) format := "rocq-runtime.plugins.ltac2" "format_ident".

Ltac2 @ external literal : string -> ('a, 'b, 'c, 'd) format ->
  ('a, 'b, 'c, 'd) format := "rocq-runtime.plugins.ltac2" "format_literal".

Ltac2 @ external alpha : ('a, 'b, 'c, 'd) format ->
  (('b -> 'r -> 'c) -> 'r -> 'a, 'b, 'c, 'd) format := "rocq-runtime.plugins.ltac2" "format_alpha".

Ltac2 @ external kfprintf : (message -> 'r) -> ('a, unit, message, 'r) format -> 'a :=
  "rocq-runtime.plugins.ltac2" "format_kfprintf".

Ltac2 @ external ikfprintf : ('v -> 'r) -> 'v -> ('a, unit, 'v, 'r) format -> 'a :=
  "rocq-runtime.plugins.ltac2" "format_ikfprintf".

End Format.
