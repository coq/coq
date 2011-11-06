(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2011     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

(* Parameters of pretty-printing *)

type pp_global_params = {
  margin : int;
  max_indent : int;
  max_depth : int;
  ellipsis : string }

(* Default parameters of pretty-printing *)

let dflt_gp = {
  margin     = 78;
  max_indent = 50;
  max_depth  = 50;
  ellipsis   = ".." }

(* A deeper pretty-printer to print proof scripts *)

let deep_gp = {
  margin     = 78;
  max_indent = 50;
  max_depth  = 10000;
  ellipsis   = "..." }

(* set_gp : Format.formatter -> pp_global_params -> unit
 * set the parameters of a formatter *)

let set_gp ft gp =
  Format.pp_set_margin ft gp.margin ;
  Format.pp_set_max_indent ft gp.max_indent ;
  Format.pp_set_max_boxes ft gp.max_depth ;
  Format.pp_set_ellipsis_text ft gp.ellipsis

let set_dflt_gp ft = set_gp ft dflt_gp

let get_gp ft =
  { margin = Format.pp_get_margin ft ();
    max_indent = Format.pp_get_max_indent ft ();
    max_depth = Format.pp_get_max_boxes ft ();
    ellipsis = Format.pp_get_ellipsis_text ft () }


(* Output functions of pretty-printing *)

type 'a pp_formatter_params = {
  fp_output : out_channel ;
  fp_output_function : string -> int -> int -> unit ;
  fp_flush_function : unit -> unit }

(* Output functions for stdout and stderr *)

let std_fp = {
  fp_output = stdout ;
  fp_output_function = output stdout;
  fp_flush_function = (fun () -> flush stdout) }

let err_fp = {
  fp_output = stderr ;
  fp_output_function = output stderr;
  fp_flush_function = (fun () -> flush stderr) }

(* with_fp : 'a pp_formatter_params -> Format.formatter
 * returns of formatter for given formatter functions *)

let with_fp fp =
  let ft = Format.make_formatter fp.fp_output_function fp.fp_flush_function in
  Format.pp_set_formatter_out_channel ft fp.fp_output;
  ft

(* Output on a channel ch *)

let with_output_to ch =
  let ft = with_fp { fp_output = ch ;
      	             fp_output_function = (output ch) ;
	             fp_flush_function = (fun () -> flush ch) } in
  set_gp ft deep_gp;
  ft

let std_ft = ref Format.std_formatter
let _ = set_dflt_gp !std_ft

let err_ft = ref Format.err_formatter
let _ = set_gp !err_ft deep_gp

let deep_ft = ref (with_output_to stdout)
let _ = set_gp !deep_ft deep_gp

(* For parametrization through vernacular *)
let default = Format.pp_get_max_boxes !std_ft ()
let default_margin = Format.pp_get_margin !std_ft ()

let get_depth_boxes () = Some (Format.pp_get_max_boxes !std_ft ())
let set_depth_boxes v =
  Format.pp_set_max_boxes !std_ft (match v with None -> default | Some v -> v)

let get_margin () = Some (Format.pp_get_margin !std_ft ())
let set_margin v =
  let v = match v with None -> default_margin | Some v -> v in
  Format.pp_set_margin !std_ft v;
  Format.pp_set_margin !deep_ft v

