(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Feedback
open Pp

(** Pp control also belongs here as the terminal is private to the toplevel *)

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
  ellipsis   = "..." }

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

(* with_fp : 'a pp_formatter_params -> Format.formatter
 * returns of formatter for given formatter functions *)

let with_fp chan out_function flush_function =
  let ft = Format.make_formatter out_function flush_function in
  Format.pp_set_formatter_out_channel ft chan;
  ft

(* Output on a channel ch *)

let with_output_to ch =
  let ft = with_fp ch (output_substring ch) (fun () -> flush ch) in
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
  Format.pp_set_margin Format.str_formatter v;
  Format.pp_set_margin !std_ft v;
  Format.pp_set_margin !deep_ft v;
  (* Heuristic, based on usage: the column on the right of max_indent
     column is 20% of width, capped to 30 characters *)
  let m = max (64 * v / 100) (v-30) in
  Format.pp_set_max_indent Format.str_formatter m;
  Format.pp_set_max_indent !std_ft m;
  Format.pp_set_max_indent !deep_ft m

(** Console display of feedback *)

(** Default tags *)
module Tag = struct

  let error   = "message.error"
  let warning = "message.warning"
  let debug   = "message.debug"

end

let msgnl_with ?pre_hdr fmt strm =
  pp_with fmt (strm ++ fnl ());
  Format.pp_print_flush fmt ()

module Emacs = struct

  (* Special chars for emacs, to detect warnings inside goal output *)
  let quote_warning_start = "<warning>"
  let quote_warning_end = "</warning>"

  let quote_info_start = "<infomsg>"
  let quote_info_end = "</infomsg>"

  let quote_emacs q_start q_end msg =
    hov 0 (seq [str q_start; brk(0,0); msg; brk(0,0); str q_end])

  let quote_warning = quote_emacs quote_warning_start quote_warning_end
  let quote_info = quote_emacs quote_info_start quote_info_end

end

let  dbg_hdr = tag Tag.debug   (str "Debug:")   ++ spc ()
let info_hdr = mt ()
let warn_hdr = tag Tag.warning (str "Warning:") ++ spc ()
let  err_hdr = tag Tag.error   (str "Error:")   ++ spc ()

let make_body quoter info ?pre_hdr s =
  pr_opt_no_spc (fun x -> x ++ fnl ()) pre_hdr ++ quoter (hov 0 (info ++ s))

(* The empty quoter *)
let noq x = x
(* Generic logger *)
let gen_logger dbg warn ?pre_hdr level msg = match level with
  | Debug   -> msgnl_with !std_ft (make_body dbg  dbg_hdr ?pre_hdr msg)
  | Info    -> msgnl_with !std_ft (make_body dbg info_hdr ?pre_hdr msg)
  | Notice  -> msgnl_with !std_ft (make_body noq info_hdr ?pre_hdr msg)
  | Warning -> Flags.if_warn (fun () ->
               msgnl_with !err_ft (make_body warn warn_hdr ?pre_hdr msg)) ()
  | Error   -> msgnl_with !err_ft (make_body noq   err_hdr ?pre_hdr msg)

(** Standard loggers *)

(* We provide a generic clear_log_backend callback for backends
   wanting to do clenaup after the print.
*)
let std_logger_cleanup = ref (fun () -> ())

let std_logger ?pre_hdr level msg =
  gen_logger (fun x -> x) (fun x -> x) ?pre_hdr level msg;
  !std_logger_cleanup ()

(** Color logging. Moved from Ppstyle, it may need some more refactoring  *)

(* Tag map for terminal style *)
let default_tag_map () = let open Terminal in [
  (* Local to console toplevel *)
    "message.error"    , make ~bold:true ~fg_color:`WHITE ~bg_color:`RED ()
  ; "message.warning"  , make ~bold:true ~fg_color:`WHITE ~bg_color:`YELLOW ()
  ; "message.debug"    , make ~bold:true ~fg_color:`WHITE ~bg_color:`MAGENTA ()
  (* Coming from the printer *)
  ; "constr.evar"      , make            ~fg_color:`LIGHT_BLUE ()
  ; "constr.keyword"   , make ~bold:true ()
  ; "constr.type"      , make ~bold:true ~fg_color:`YELLOW ()
  ; "constr.notation"  , make ~fg_color:`WHITE ()
  (* ["constr"; "variable"] is not assigned *)
  ; "constr.reference" , make ~fg_color:`LIGHT_GREEN ()
  ; "constr.path"      , make ~fg_color:`LIGHT_MAGENTA ()
  ; "module.definition", make ~bold:true ~fg_color:`LIGHT_RED ()
  ; "module.keyword"   , make ~bold:true ()
  ; "tactic.keyword"   , make ~bold:true ()
  ; "tactic.primitive" , make ~fg_color:`LIGHT_GREEN ()
  ; "tactic.string"    , make ~fg_color:`LIGHT_RED ()
  ]

let tag_map = ref CString.Map.empty

let init_tag_map styles =
  let set accu (name, st) = CString.Map.add name st accu in
  tag_map := List.fold_left set !tag_map styles

let clear_styles () =
  tag_map := CString.Map.empty

let parse_color_config file =
  let styles = Terminal.parse file in
  init_tag_map styles

let dump_tags () = CString.Map.bindings !tag_map

(** Not thread-safe. We should put a lock somewhere if we print from
    different threads. Do we? *)
let make_style_stack () =
  (** Default tag is to reset everything *)
  let empty = Terminal.make () in
  let default_tag = Terminal.({
      fg_color = Some `DEFAULT;
      bg_color = Some `DEFAULT;
      bold = Some false;
      italic = Some false;
      underline = Some false;
      negative = Some false;
    })
  in
  let style_stack = ref [] in
  let peek () = match !style_stack with
  | []      -> default_tag  (** Anomalous case, but for robustness *)
  | st :: _ -> st
  in
  let push tag =
    let style =
      try CString.Map.find tag !tag_map
      with | Not_found -> empty
    in
    (** Use the merging of the latest tag and the one being currently pushed.
    This may be useful if for instance the latest tag changes the background and
    the current one the foreground, so that the two effects are additioned. *)
    let style = Terminal.merge (peek ()) style in
    style_stack := style :: !style_stack;
    Terminal.eval style
  in
  let pop _ = match !style_stack with
  | []       -> (** Something went wrong, we fallback *)
                Terminal.eval default_tag
  | _ :: rem -> style_stack := rem;
                Terminal.eval (peek ())
  in
  let clear () = style_stack := [] in
  push, pop, clear

let init_color_output () =
  init_tag_map (default_tag_map ());
  let push_tag, pop_tag, clear_tag = make_style_stack () in
  std_logger_cleanup := clear_tag;
  let tag_handler = {
    Format.mark_open_tag   = push_tag;
    Format.mark_close_tag  = pop_tag;
    Format.print_open_tag  = ignore;
    Format.print_close_tag = ignore;
  } in
  Format.pp_set_mark_tags !std_ft true;
  Format.pp_set_mark_tags !err_ft true;
  Format.pp_set_formatter_tag_functions !std_ft tag_handler;
  Format.pp_set_formatter_tag_functions !err_ft tag_handler

(* Rules for emacs:
   - Debug/info: emacs_quote_info
   - Warning/Error: emacs_quote_err
   - Notice: unquoted
 *)
let emacs_logger = gen_logger Emacs.quote_info Emacs.quote_warning


(* This is specific to the toplevel *)
let pr_loc loc =
    let fname = loc.Loc.fname in
    if CString.equal fname "" then
      Loc.(str"Toplevel input, characters " ++ int loc.bp ++
	   str"-" ++ int loc.ep ++ str":")
    else
      Loc.(str"File " ++ str "\"" ++ str fname ++ str "\"" ++
	   str", line " ++ int loc.line_nb ++ str", characters " ++
	   int (loc.bp-loc.bol_pos) ++ str"-" ++ int (loc.ep-loc.bol_pos) ++
	   str":")

let print_err_exn ?extra any =
  let (e, info) = CErrors.push any in
  let loc = Loc.get_loc info in
  let msg_loc = Option.cata pr_loc (mt ()) loc in
  let pre_hdr = pr_opt_no_spc (fun x -> x) extra ++ msg_loc in
  let msg = CErrors.iprint (e, info) ++ fnl () in
  std_logger ~pre_hdr Feedback.Error msg

let with_output_to_file fname func input =
  (* XXX FIXME: redirect std_ft  *)
  (* let old_logger = !logger in *)
  let channel = open_out (String.concat "." [fname; "out"]) in
  (* logger := ft_logger old_logger (Format.formatter_of_out_channel channel); *)
  try
    let output = func input in
    (* logger := old_logger; *)
    close_out channel;
    output
  with reraise ->
    let reraise = Backtrace.add_backtrace reraise in
    (* logger := old_logger; *)
    close_out channel;
    Exninfo.iraise reraise
