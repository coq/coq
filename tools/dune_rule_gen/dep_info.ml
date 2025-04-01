(************************************************************************)
(* This file is licensed under The MIT License                          *)
(* See LICENSE for more information                                     *)
(************************************************************************)

module CD = Coqdeplib
module Dep_map = Map.Make(Path)

type t = CD.Dep_info.Dep.t list Dep_map.t

(* What a pita OCaml's stdlib missing basic stuff ... *)
let from_list l =
  List.fold_left (fun map { CD.Dep_info.name; deps } ->
      let name = Path.make name in
      let path = Path.add_extension ~ext:".v" name in
      Dep_map.add path deps map) Dep_map.empty l

let debug_coqdep = false
let debug = false

let coqdep_register_file vAccu file =
  (* if debug then Format.eprintf "cd regfile: %s@\n%!" file; *)
  CD.Common.treat_file_command_line vAccu (Path.to_string file)

(* From dir info + context *)
let make ~args ~(dir_info : _ Dir_info.t) =
  let args = "-dyndep" :: "opt" :: List.map Arg.to_string args in
  if debug_coqdep then Format.eprintf "coqdep: %s@\n%!" (String.concat " " args);
  let args = Coqdeplib.Args.parse (Coqdeplib.Args.make ()) args in
  (* We are sane w.r.t. path separators *)
  let make_separator_hack = false in
  let rocqenv, st = CD.Common.init ~make_separator_hack args in
  (* we always use -boot *)
  assert (rocqenv = Boot);
  let st =
    Dir_info.fold dir_info ~init:st ~f:(fun ~prefix:_ vAccu files ->
        let files = List.map Coq_module.source files in
        List.fold_left coqdep_register_file vAccu files) in
  CD.Common.compute_deps st |> from_list

let lookup ~dep_info file =
  if debug then Format.eprintf "lookup: %a@\n%!" Path.pp file;
  let file = Path.coqdep_fixup_dir file in
  Dep_map.find file dep_info

let pp_binding fmt (s, _) = Format.fprintf fmt "%a" Path.pp s

let lookup ~dep_info x =
  try lookup ~dep_info x
  with
  | Not_found ->
    if debug then
      begin
        Format.eprintf "@[<v>%a@]@\n%!"
          (Format.pp_print_list pp_binding) (Dep_map.bindings dep_info);
        Format.eprintf "@[dep: %a@\n%!@]" Path.pp x
      end;
    raise Not_found
