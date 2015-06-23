(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util

type t = string
(** We use the concatenated string, with dots separating each string. We
    forbid the use of dots in the strings. *)

let tags : Terminal.style option String.Map.t ref = ref String.Map.empty

let make ?style tag =
  let check s = if String.contains s '.' then invalid_arg "Ppstyle.make" in
  let () = List.iter check tag in
  let name = String.concat "." tag in
  let () = assert (not (String.Map.mem name !tags)) in
  let () = tags := String.Map.add name style !tags in
  name

let repr t = String.split '.' t

let get_style tag =
  try String.Map.find tag !tags with Not_found -> assert false

let set_style tag st =
  try tags := String.Map.update tag st !tags with Not_found -> assert false

let clear_styles () =
  tags := String.Map.map (fun _ -> None) !tags

let dump () = String.Map.bindings !tags

let parse_config s =
  let styles = Terminal.parse s in
  let set accu (name, st) =
    try String.Map.update name (Some st) accu with Not_found -> accu
  in
  tags := List.fold_left set !tags styles

let tag = Pp.Tag.create "ppstyle"

(** Default tag is to reset everything *)
let default = Terminal.({
  fg_color = Some `DEFAULT;
  bg_color = Some `DEFAULT;
  bold = Some false;
  italic = Some false;
  underline = Some false;
  negative = Some false;
})

let empty = Terminal.make ()

let make_style_stack style_tags =
  (** Not thread-safe. We should put a lock somewhere if we print from
      different threads. Do we? *)
  let style_stack = ref [] in
  let peek () = match !style_stack with
  | [] -> default (** Anomalous case, but for robustness *)
  | st :: _ -> st
  in
  let push tag =
    let style =
      try
        begin match String.Map.find tag style_tags with
        | None -> empty
        | Some st -> st
        end
      with Not_found -> empty
    in
    (** Use the merging of the latest tag and the one being currently pushed.
    This may be useful if for instance the latest tag changes the background and
    the current one the foreground, so that the two effects are additioned. *)
    let style = Terminal.merge (peek ()) style in
    let () = style_stack := style :: !style_stack in
    Terminal.eval style
  in
  let pop _ = match !style_stack with
  | [] ->
    (** Something went wrong, we fallback *)
    Terminal.eval default
  | _ :: rem ->
    let () = style_stack := rem in
    Terminal.eval (peek ())
  in
  let clear () = style_stack := [] in
  push, pop, clear

let error_tag =
  let style = Terminal.make ~bold:true ~fg_color:`WHITE ~bg_color:`RED () in
  make ~style ["message"; "error"]

let warning_tag =
  let style = Terminal.make ~bold:true ~fg_color:`WHITE ~bg_color:`YELLOW () in
  make ~style ["message"; "warning"]

let debug_tag =
  let style = Terminal.make ~bold:true ~fg_color:`WHITE ~bg_color:`MAGENTA () in
  make ~style ["message"; "debug"]

let pp_tag t = match Pp.Tag.prj t tag with
| None -> ""
| Some key -> key

let init_color_output () =
  let push_tag, pop_tag, clear_tag = make_style_stack !tags in
  let tag_handler = {
    Format.mark_open_tag = push_tag;
    Format.mark_close_tag = pop_tag;
    Format.print_open_tag = ignore;
    Format.print_close_tag = ignore;
  } in
  let open Pp_control in
  let () = Format.pp_set_mark_tags !std_ft true in
  let () = Format.pp_set_mark_tags !err_ft true in
  let () = Format.pp_set_formatter_tag_functions !std_ft tag_handler in
  let () = Format.pp_set_formatter_tag_functions !err_ft tag_handler in
  let pptag = tag in
  let open Pp in
  let msg ?header ft strm =
    let strm = match header with
    | None -> hov 0 strm
    | Some (h, t) ->
      let tag = Pp.Tag.inj t pptag in
      let h = Pp.tag tag (str h ++ str ":") in
      hov 0 (h ++ spc () ++ strm)
    in
    pp_with ~pp_tag ft strm;
    Format.pp_print_newline ft ();
    Format.pp_print_flush ft ();
    (** In case something went wrong, we reset the stack *)
    clear_tag ();
  in
  let logger level strm = match level with
  | Debug _ -> msg ~header:("Debug", debug_tag) !std_ft strm
  | Info -> msg !std_ft strm
  | Notice -> msg !std_ft strm
  | Warning ->
    let header = ("Warning", warning_tag) in
    Flags.if_warn (fun () -> msg ~header !err_ft strm) ()
  | Error -> msg ~header:("Error", error_tag) !err_ft strm
  in
  let () = set_logger logger in
  ()
