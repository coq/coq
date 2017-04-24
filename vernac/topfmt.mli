(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
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
val std_logger   : ?pre_hdr:Pp.std_ppcmds -> Feedback.level -> Pp.std_ppcmds -> unit
val emacs_logger : ?pre_hdr:Pp.std_ppcmds -> Feedback.level -> Pp.std_ppcmds -> unit

(** Color output *)
val init_color_output : unit -> unit
val clear_styles : unit -> unit
val parse_color_config : string -> unit
val dump_tags : unit -> (string * Terminal.style) list

(** Error printing *)
(* To be deprecated when we can fully move to feedback-based error
   printing. *)
val pr_loc : Loc.t -> Pp.std_ppcmds
val print_err_exn : ?extra:Pp.std_ppcmds -> exn -> unit

(** [with_output_to_file file f x] executes [f x] with logging
    redirected to a file [file] *)
val with_output_to_file : string -> ('a -> 'b) -> 'a -> 'b

