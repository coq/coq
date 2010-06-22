(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Parameters of pretty-printing. *)

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

type 'a pp_formatter_params = {
  fp_output : out_channel;
  fp_output_function : string -> int -> int -> unit;
  fp_flush_function : unit -> unit }

val std_fp : (int*string) pp_formatter_params
val err_fp : (int*string) pp_formatter_params

val with_fp : 'a pp_formatter_params -> Format.formatter
val with_output_to : out_channel -> Format.formatter

val std_ft : Format.formatter ref
val err_ft : Format.formatter ref
val deep_ft : Format.formatter ref

(** {6 For parametrization through vernacular. } *)

val set_depth_boxes : int option -> unit
val get_depth_boxes : unit -> int option

val set_margin : int option -> unit
val get_margin : unit -> int option
