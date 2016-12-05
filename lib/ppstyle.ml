(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

module String = CString

type t = Pp.pp_tag

let tags : Terminal.style option String.Map.t ref = ref String.Map.empty

let to_format tag = String.concat "." tag
let of_format tag = String.split  '.' tag

let make ?style tag =
  let name = to_format tag                          in
  let () = assert (not (String.Map.mem name !tags)) in
  let () = tags := String.Map.add name style !tags  in
  name

let get_style tag =
  try String.Map.find tag !tags
  with Not_found -> assert false

let set_style tag st =
  try tags := String.Map.update tag st !tags
  with Not_found -> assert false

let clear_styles () =
  tags := String.Map.map (fun _ -> None) !tags

let dump () = String.Map.bindings !tags

let parse_config s =
  let styles = Terminal.parse s in
  let set accu (name, st) =
    try String.Map.update name (Some st) accu with Not_found -> accu
  in
  tags := List.fold_left set !tags styles

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

let error_tag =
  let style = Terminal.make ~bold:true ~fg_color:`WHITE ~bg_color:`RED () in
  make ~style ["message"; "error"]

let warning_tag =
  let style = Terminal.make ~bold:true ~fg_color:`WHITE ~bg_color:`YELLOW () in
  make ~style ["message"; "warning"]

let debug_tag =
  let style = Terminal.make ~bold:true ~fg_color:`WHITE ~bg_color:`MAGENTA () in
  make ~style ["message"; "debug"]
