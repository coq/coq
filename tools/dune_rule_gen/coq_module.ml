(************************************************************************)
(* This file is licensed under The MIT License                          *)
(* See LICENSE for more information                                     *)
(* (c) MINES ParisTech 2018-2019                                        *)
(* (c) INRIA 2020-2022                                                  *)
(* Written by: Emilio Jesús Gallego Arias                               *)
(* Written by: Rudi Grinberg                                            *)
(************************************************************************)

let with_timing = true

type t =
  { source : Path.t
  ; prefix : string list
  ; name : string
  }

let pp fmt { source; prefix; name } =
  Format.fprintf fmt "@[{%s : %a}@]" (String.concat "." (prefix@[name]) ) Path.pp source

let make ~source ~prefix ~name = { source; prefix; name }
let source { source; _ } = source
let prefix { prefix; _ } = prefix

let mod_to_obj ~ext { name; _ } = name ^ ext

module Rule_type = struct

  type native = Disabled | Coqc | CoqNative
  type t =
    | Regular of { native : native }

  let native_coqc = function
    | Regular { native = Coqc } -> true
    | Regular { native = CoqNative }
    | Regular { native = Disabled } -> false

end

let native_obj_files ~install ~tname { prefix; name; _ } =
  let base_theory = tname in
  let native_base = "N" ^ String.concat "_" (base_theory @ prefix @ [name]) in
  let prefix file = if install then Filename.concat ".coq-native" file else file in
  [ prefix @@ native_base ^ ".cmi"; prefix @@ native_base ^ ".cmxs" ]

let base_obj_files coq_module =
  [ mod_to_obj coq_module ~ext:".glob"
  ; mod_to_obj coq_module ~ext:".vos"
  ; mod_to_obj coq_module ~ext:".vo"
  ]

let obj_files ~tname ~rule coq_module =
  let native = Rule_type.native_coqc rule in
  let native_objs = if native then native_obj_files ~tname ~install:false coq_module else [] in
  let timing_objs = if with_timing then [ mod_to_obj coq_module ~ext:".timing" ] else [] in
  timing_objs @ native_objs @ base_obj_files coq_module

let prefix_to_dir = String.concat Filename.dir_sep

let native_install_files ~tname ~rule coq_module =
  match rule with
  | Rule_type.Regular { native = CoqNative }
  | Regular { native = Coqc } ->
    native_obj_files ~tname ~install:false coq_module
  , native_obj_files ~tname ~install:true coq_module
  | Regular { native = Disabled } -> [], []

(* quick/vio woes... it does produce a different set of targets than
   regular compilation *)
let base_install_files coq_module =
  mod_to_obj coq_module ~ext:".v" :: base_obj_files coq_module

let install_files ~tname ~rule coq_module =
  let src_base = base_install_files coq_module in
  let src_native, dst_native = native_install_files ~tname ~rule coq_module in
  let src = src_base @ src_native in
  let ppath = prefix_to_dir (prefix coq_module) in
  let dst = List.map (Filename.concat ppath) (src_base @ dst_native) in
  List.combine src dst

let native_obj_files = native_obj_files ~install:false
