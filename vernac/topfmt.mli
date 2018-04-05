(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Console printing options *)

type pp_global_params = {
  margin : int;
  max_indent : int;
  max_depth : int;
  ellipsis : string }

val dflt_gp : pp_global_params
val deep_gp : pp_global_params
val set_gp : Format.formatter -> pp_global_params -> unit
val set_dflt_gp : Format.formatter -> unit
val get_gp : Format.formatter -> pp_global_params

(** {6 Output functions of pretty-printing. } *)

val with_output_to : out_channel -> Format.formatter

val std_ft  : Format.formatter ref
val err_ft  : Format.formatter ref
val deep_ft : Format.formatter ref

(** {6 For parametrization through vernacular. } *)

val set_depth_boxes : int option -> unit
val get_depth_boxes : unit -> int option

val set_margin : int option -> unit
val get_margin : unit -> int option

(** Console display of feedback, we may add some location information *)
val std_logger   : ?pre_hdr:Pp.t -> Feedback.level -> Pp.t -> unit
val emacs_logger : ?pre_hdr:Pp.t -> Feedback.level -> Pp.t -> unit

(** Color output *)
val default_styles : unit -> unit
val parse_color_config : string -> unit
val dump_tags : unit -> (string * Terminal.style) list

(** Initialization of interpretation of tags *)
val init_terminal_output : color:bool -> unit

(** Error printing *)
(* To be deprecated when we can fully move to feedback-based error
   printing. *)

type execution_phase =
  | ParsingCommandLine
  | Initialization
  | LoadingPrelude
  | LoadingRcFile
  | InteractiveLoop

val pr_loc : Loc.t -> Pp.t
val pr_phase : ?loc:Loc.t -> execution_phase -> Pp.t option
val print_err_exn : execution_phase -> exn -> unit

(** [with_output_to_file file f x] executes [f x] with logging
    redirected to a file [file] *)
val with_output_to_file : string -> ('a -> 'b) -> 'a -> 'b

