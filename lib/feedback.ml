(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Xml_datatype

type level =
  | Debug
  | Info
  | Notice
  | Warning
  | Error

type edit_id = int
type state_id = Stateid.t
type edit_or_state_id = Edit of edit_id | State of state_id
type route_id = int

type feedback_content =
  | Processed
  | Incomplete
  | Complete
  | ProcessingIn of string
  | InProgress of int
  | WorkerStatus of string * string
  | Goals of Loc.t * string
  | AddedAxiom
  | GlobRef of Loc.t * string * string * string * string
  | GlobDef of Loc.t * string * string * string
  | FileDependency of string option * string
  | FileLoaded of string * string
  (* Extra metadata *)
  | Custom of Loc.t * string * xml
  (* Generic messages *)
  | Message of level * Loc.t option * Richpp.richpp

type feedback = {
  id : edit_or_state_id;
  contents : feedback_content;
  route : route_id;
}

let default_route = 0

(** Feedback and logging *)
open Pp
open Pp_control

type logger = ?loc:Loc.t -> level -> std_ppcmds -> unit

let msgnl_with ?pp_tag fmt strm = msg_with ?pp_tag fmt (strm ++ fnl ())

(* XXX: This is really painful! *)
module Emacs = struct

  (* Special chars for emacs, to detect warnings inside goal output *)
  let emacs_quote_start = String.make 1 (Char.chr 254)
  let emacs_quote_end   = String.make 1 (Char.chr 255)

  let emacs_quote_err g =
    hov 0 (str emacs_quote_start ++ g ++ str emacs_quote_end)

  let emacs_quote_info_start = "<infomsg>"
  let emacs_quote_info_end = "</infomsg>"

  let emacs_quote_info g =
    hov 0 (str emacs_quote_info_start++ brk(0,0) ++ g ++ brk(0,0) ++ str emacs_quote_info_end)

end

open Emacs

let  dbg_str = tag Ppstyle.(Tag.inj debug_tag   tag) (str "Debug:")   ++ spc ()
let info_str = mt ()
let warn_str = tag Ppstyle.(Tag.inj warning_tag tag) (str "Warning:") ++ spc ()
let  err_str = tag Ppstyle.(Tag.inj error_tag   tag) (str "Error:"  ) ++ spc ()

let make_body quoter info ?loc s =
  let loc = Option.cata Pp.pr_loc (Pp.mt ()) loc in
  quoter (hov 0 (loc ++ info ++ s))

(* Generic logger *)
let gen_logger dbg err ?pp_tag ?loc level msg = match level with
  | Debug   -> msgnl_with ?pp_tag !std_ft (make_body dbg  dbg_str ?loc msg)
  | Info    -> msgnl_with ?pp_tag !std_ft (make_body dbg info_str ?loc msg)
  | Notice  -> msgnl_with ?pp_tag !std_ft msg
  | Warning -> Flags.if_warn (fun () ->
               msgnl_with ?pp_tag !err_ft (make_body err warn_str ?loc msg)) ()
  | Error   -> msgnl_with ?pp_tag !err_ft (make_body err  err_str ?loc msg)

(* We provide a generic clear_log_backend callback for backends
   wanting to do clenaup after the print.
*)
let std_logger_tag     = ref None
let std_logger_cleanup = ref (fun () -> ())

let std_logger ?loc level msg =
  gen_logger (fun x -> x) (fun x -> x) ?pp_tag:!std_logger_tag ?loc level msg;
  !std_logger_cleanup ()

(* Rules for emacs:
   - Debug/info: emacs_quote_info
   - Warning/Error: emacs_quote_err
   - Notice: unquoted

  Note the inconsistency.
 *)
let emacs_logger = gen_logger emacs_quote_info emacs_quote_err ?pp_tag:None

(** Color logging. Moved from pp_style, it may need some more refactoring  *)

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
    let style = match Ppstyle.get_style tag with
      | None    -> empty
      | Some st -> st
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
  let open Pp_control in
  let push_tag, pop_tag, clear_tag = make_style_stack () in
  std_logger_cleanup := clear_tag;
  std_logger_tag     := Some Ppstyle.pp_tag;
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

let logger       = ref std_logger
let set_logger l = logger := l

let msg_info    ?loc x = !logger ?loc Info x
let msg_notice  ?loc x = !logger ?loc Notice x
let msg_warning ?loc x = !logger ?loc Warning x
let msg_error   ?loc x = !logger ?loc Error x
let msg_debug   ?loc x = !logger ?loc Debug x

(** Feeders *)
let feeders = ref []
let add_feeder f = feeders := f :: !feeders

let debug_feeder = function
  | { contents = Message (Debug, loc, pp) } ->
       msg_debug ?loc (Pp.str (Richpp.raw_print pp))
  | _ -> ()

let feedback_id    = ref (Edit 0)
let feedback_route = ref default_route

let set_id_for_feedback ?(route=default_route) i =
  feedback_id := i; feedback_route := route

let feedback ?id ?route what =
  let m = {
     contents = what;
     route = Option.default !feedback_route route;
     id    = Option.default !feedback_id id;
  } in
  List.iter (fun f -> f m) !feeders

let feedback_logger ?loc lvl msg =
  feedback ~route:!feedback_route ~id:!feedback_id
    (Message (lvl, loc, Richpp.richpp_of_pp msg))

(* Output to file *)
let ft_logger old_logger ft ?loc level mesg =
  let id x = x in
  match level with
  | Debug   -> msgnl_with ft (make_body id  dbg_str mesg)
  | Info    -> msgnl_with ft (make_body id info_str mesg)
  | Notice  -> msgnl_with ft mesg
  | Warning -> old_logger ?loc level mesg
  | Error   -> old_logger ?loc level mesg

let with_output_to_file fname func input =
  let old_logger = !logger in
  let channel = open_out (String.concat "." [fname; "out"]) in
  logger := ft_logger old_logger (Format.formatter_of_out_channel channel);
  try
    let output = func input in
    logger := old_logger;
    close_out channel;
    output
  with reraise ->
    let reraise = Backtrace.add_backtrace reraise in
    logger := old_logger;
    close_out channel;
    Exninfo.iraise reraise

