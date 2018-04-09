(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

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
  Format.pp_set_margin !err_ft v;
  (* Heuristic, based on usage: the column on the right of max_indent
     column is 20% of width, capped to 30 characters *)
  let m = max (64 * v / 100) (v-30) in
  Format.pp_set_max_indent Format.str_formatter m;
  Format.pp_set_max_indent !std_ft m;
  Format.pp_set_max_indent !deep_ft m;
  Format.pp_set_max_indent !err_ft m

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
let gen_logger dbg warn ?pre_hdr level msg = let open Feedback in match level with
  | Debug   -> msgnl_with !std_ft (make_body dbg  dbg_hdr ?pre_hdr msg)
  | Info    -> msgnl_with !std_ft (make_body dbg info_hdr ?pre_hdr msg)
  | Notice  -> msgnl_with !std_ft (make_body noq info_hdr ?pre_hdr msg)
  | Warning -> Flags.if_warn (fun () ->
               msgnl_with !err_ft (make_body warn warn_hdr ?pre_hdr msg)) ()
  | Error   -> msgnl_with !err_ft (make_body noq   err_hdr ?pre_hdr msg)

(** Standard loggers *)

(* We provide a generic clear_log_backend callback for backends
   wanting to do cleanup after the print.
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
  ; "diff.added"       , make ~bg_color:(`RGB(0,141,0)) ~underline:true ()
  ; "diff.removed"     , make ~bg_color:(`RGB(170,0,0)) ~underline:true ()
  ; "diff.added.bg"    , make ~bg_color:(`RGB(0,91,0)) ()
  ; "diff.removed.bg"  , make ~bg_color:(`RGB(91,0,0)) ()
  ]

let tag_map = ref CString.Map.empty

let init_tag_map styles =
  let set accu (name, st) = CString.Map.add name st accu in
  tag_map := List.fold_left set !tag_map styles

let default_styles () =
  init_tag_map (default_tag_map ())

let parse_color_config file =
  let styles = Terminal.parse file in
  init_tag_map styles

let dump_tags () = CString.Map.bindings !tag_map

let empty = Terminal.make ()
let default_style = Terminal.reset_style

let get_style tag =
  try CString.Map.find tag !tag_map
  with Not_found -> empty;;

let get_open_seq tags =
  let style = List.fold_left (fun a b -> Terminal.merge a (get_style b)) default_style tags in
  Terminal.eval (Terminal.diff default_style style);;

let get_close_seq tags =
  let style = List.fold_left (fun a b -> Terminal.merge a (get_style b)) default_style tags in
  Terminal.eval (Terminal.diff style default_style);;

let diff_tag_stack = ref []  (* global, just like std_ft *)

(** Not thread-safe. We should put a lock somewhere if we print from
    different threads. Do we? *)
let make_style_stack () =
  (** Default tag is to reset everything *)
  let style_stack = ref [] in
  let peek () = match !style_stack with
  | []      -> default_style  (** Anomalous case, but for robustness *)
  | st :: _ -> st
  in
  let open_tag tag =
    let (tpfx, ttag) = split_tag tag in
    if tpfx = end_pfx then "" else
      let style = get_style ttag in
    (** Merge the current settings and the style being pushed.  This allows
    restoring the previous settings correctly in a pop when both set the same
    attribute.  Example: current settings have red FG, the pushed style has
    green FG.  When popping the style, we should set red FG, not default FG. *)
    let style = Terminal.merge (peek ()) style in
    let diff = Terminal.diff (peek ()) style in
    style_stack := style :: !style_stack;
    if tpfx = start_pfx then diff_tag_stack := ttag :: !diff_tag_stack;
    Terminal.eval diff
  in
  let close_tag tag =
    let (tpfx, _) = split_tag tag in
      if tpfx = start_pfx then "" else begin
        if tpfx = end_pfx then diff_tag_stack := (try List.tl !diff_tag_stack with tl -> []);
        match !style_stack with
        | []       -> (** Something went wrong, we fallback *)
                      Terminal.eval default_style
        | cur :: rem -> style_stack := rem;
                      if cur = (peek ()) then "" else
                        if rem = [] then Terminal.reset else
                          Terminal.eval (Terminal.diff cur (peek ()))
      end
  in
  let clear () = style_stack := [] in
  open_tag, close_tag, clear

let make_printing_functions () =
  let print_prefix ft tag =
    let (tpfx, ttag) = split_tag tag in
    if tpfx <> end_pfx then
      let style = get_style ttag in
      match style.Terminal.prefix with Some s -> Format.pp_print_string ft s | None -> () in

  let print_suffix ft tag =
    let (tpfx, ttag) = split_tag tag in
    if tpfx <> start_pfx then
      let style = get_style ttag in
      match style.Terminal.suffix with Some s -> Format.pp_print_string ft s | None -> () in

  print_prefix, print_suffix

let init_output_fns () =
  let reopen_highlight = ref "" in
  let open Format in
  let fns = Format.pp_get_formatter_out_functions !std_ft () in
  let newline () =
    if !diff_tag_stack <> [] then begin
      let close = get_close_seq !diff_tag_stack in
      fns.out_string close 0 (String.length close);
      reopen_highlight := get_open_seq (List.rev !diff_tag_stack);
    end;
    fns.out_string "\n" 0 1 in
  let string s off n =
    if !reopen_highlight <> ""  && String.trim (String.sub s off n) <> "" then begin
      fns.out_string !reopen_highlight 0 (String.length !reopen_highlight);
      reopen_highlight := ""
    end;
    fns.out_string s off n in
  let new_fns = { fns with out_string = string; out_newline = newline } in
  Format.pp_set_formatter_out_functions !std_ft new_fns;;

let init_terminal_output ~color =
  let open_tag, close_tag, clear_tag = make_style_stack () in
  let print_prefix, print_suffix = make_printing_functions () in
  let tag_handler ft = {
    Format.mark_open_tag   = open_tag;
    Format.mark_close_tag  = close_tag;
    Format.print_open_tag  = print_prefix ft;
    Format.print_close_tag = print_suffix ft;
  } in
  if color then
    (* Use 0-length markers *)
    begin
      std_logger_cleanup := clear_tag;
      init_output_fns ();
      Format.pp_set_mark_tags !std_ft true;
      Format.pp_set_mark_tags !err_ft true
    end
  else
    (* Use textual markers *)
    begin
      Format.pp_set_print_tags !std_ft true;
      Format.pp_set_print_tags !err_ft true
    end;
  Format.pp_set_formatter_tag_functions !std_ft (tag_handler !std_ft);
  Format.pp_set_formatter_tag_functions !err_ft (tag_handler !err_ft)

(* Rules for emacs:
   - Debug/info: emacs_quote_info
   - Warning/Error: emacs_quote_err
   - Notice: unquoted
 *)
let emacs_logger = gen_logger Emacs.quote_info Emacs.quote_warning

(* This is specific to the toplevel *)

type execution_phase =
  | ParsingCommandLine
  | Initialization
  | LoadingPrelude
  | LoadingRcFile
  | InteractiveLoop

let pr_loc loc =
    let fname = loc.Loc.fname in
    match fname with
    | Loc.ToplevelInput ->
      Loc.(str"Toplevel input, characters " ++ int loc.bp ++
	   str"-" ++ int loc.ep ++ str":")
    | Loc.InFile fname ->
      Loc.(str"File " ++ str "\"" ++ str fname ++ str "\"" ++
	   str", line " ++ int loc.line_nb ++ str", characters " ++
	   int (loc.bp-loc.bol_pos) ++ str"-" ++ int (loc.ep-loc.bol_pos) ++
	   str":")

let pr_phase ?loc phase =
  match phase, loc with
  | LoadingRcFile, loc ->
     (* For when all errors go through feedback:
     str "While loading rcfile:" ++
     Option.cata (fun loc -> fnl () ++ pr_loc loc) (mt ()) loc *)
     Option.map pr_loc loc
  | LoadingPrelude, loc ->
     Some (str "While loading initial state:" ++ Option.cata (fun loc -> fnl () ++ pr_loc loc) (mt ()) loc)
  | _, Some loc -> Some (pr_loc loc)
  | ParsingCommandLine, _
  | Initialization, _ -> None
  | InteractiveLoop, _ ->
     (* Note: interactive messages such as "foo is defined" are not located *)
     None

let print_err_exn phase any =
  let (e, info) = CErrors.push any in
  let loc = Loc.get_loc info in
  let pre_hdr = pr_phase ?loc phase in
  let msg = CErrors.iprint (e, info) ++ fnl () in
  std_logger ?pre_hdr Feedback.Error msg

let with_output_to_file fname func input =
  let channel = open_out (String.concat "." [fname; "out"]) in
  let old_fmt = !std_ft, !err_ft, !deep_ft in
  let new_ft = Format.formatter_of_out_channel channel in
  std_ft := new_ft;
  err_ft := new_ft;
  deep_ft := new_ft;
  try
    let output = func input in
    std_ft := Util.pi1 old_fmt;
    err_ft := Util.pi2 old_fmt;
    deep_ft := Util.pi3 old_fmt;
    close_out channel;
    output
  with reraise ->
    let reraise = Backtrace.add_backtrace reraise in
    std_ft := Util.pi1 old_fmt;
    err_ft := Util.pi2 old_fmt;
    deep_ft := Util.pi3 old_fmt;
    close_out channel;
    Exninfo.iraise reraise
