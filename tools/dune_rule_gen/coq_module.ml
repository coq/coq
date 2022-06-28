(************************************************************************)
(* This file is licensed under The MIT License                          *)
(* See LICENSE for more information                                     *)
(* (c) MINES ParisTech 2018-2019                                        *)
(* (c) INRIA 2020-2022                                                  *)
(* Written by: Emilio Jesús Gallego Arias                               *)
(* Written by: Rudi Grinberg                                            *)
(************************************************************************)

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
    | Quick
    (** build / depend on .vio instead of .vo  *)

  let native_coqc = function
    | Regular { native = Coqc } -> true
    | Regular { native = CoqNative }
    | Regular { native = Disabled }
    | Quick -> false
  let quick = function Regular _ -> false | Quick -> true
  let vo_ext = function Regular _ -> ".vo" | Quick -> ".vio"

end

let native_obj_files ~install ~tname { prefix; name; _ } =
  let base_theory = tname in
  let native_base = "N" ^ String.concat "_" (base_theory @ prefix @ [name]) in
  let prefix file = if install then Filename.concat ".coq-native" file else file in
  [ prefix @@ native_base ^ ".cmi"; prefix @@ native_base ^ ".cmxs" ]

let base_obj_files ~rule coq_module =
  let quick = Rule_type.quick rule in
  let vo_ext = Rule_type.vo_ext rule in

  let aux_objs = if quick then []
    else
      [ mod_to_obj coq_module ~ext:".glob"
      ; "." ^ mod_to_obj coq_module ~ext:".aux"
      ; mod_to_obj coq_module ~ext:".vos"
      ]
  in
  aux_objs @
  [ mod_to_obj coq_module ~ext:vo_ext
  ]

let obj_files ~tname ~rule coq_module =
  let native = Rule_type.native_coqc rule in
  let native_objs = if native then native_obj_files ~tname ~install:false coq_module else [] in
  native_objs @ base_obj_files ~rule coq_module

let prefix_to_dir = String.concat Filename.dir_sep

let native_install_files ~tname ~rule coq_module =
  match rule with
  | Rule_type.Regular { native = CoqNative }
  | Regular { native = Coqc } ->
    native_obj_files ~tname ~install:false coq_module
  , native_obj_files ~tname ~install:true coq_module
  | Regular { native = Disabled }
  | Quick ->
    [], []

(* quick/vio woes... it does produce a different set of targets than
   regular compilation *)
let base_install_files ~rule coq_module =
  match rule with
  | Rule_type.Quick ->
    [ mod_to_obj coq_module ~ext:".vo"
    ; mod_to_obj coq_module ~ext:".vos"
    ]
  | Rule_type.Regular _ as rule ->
    base_obj_files ~rule coq_module

let install_files ~tname ~rule coq_module =
  let src_base = base_install_files ~rule coq_module in
  let src_native, dst_native = native_install_files ~tname ~rule coq_module in
  let src = src_base @ src_native in
  let ppath = prefix_to_dir (prefix coq_module) in
  let dst = List.map (Filename.concat ppath) (src_base @ dst_native) in
  List.combine src dst

let native_obj_files = native_obj_files ~install:false
