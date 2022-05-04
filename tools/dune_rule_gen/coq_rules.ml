(************************************************************************)
(* This file is licensed under The MIT License                          *)
(* See LICENSE for more information                                     *)
(* (c) MINES ParisTech 2018-2019                                        *)
(* (c) INRIA 2020-2022                                                  *)
(* Written by: Emilio Jesús Gallego Arias                               *)
(* Written by: Rudi Grinberg                                            *)
(************************************************************************)

(* coq_rules: generate dune build rules for Coq's test-suite and stdlib *)

(* Originally written by Emilio Jesús Gallego Arias and Rudi Grinberg
   for Dune's coq_rules.ml , which followed a first coq_dune.exe
   implementation by Emilio Jesús Gallego Arias *)

(* note that this file closely follows Dune's own coq_rules.ml [and
   eventually they could be merged], hence the license. Other modules
   such as Arg or Path are straight copies from Dune's *)

let _debug = false

module FlagUtil = struct

  let read_plugin_dir ~root_lvl =
    let plugins_dir = Path.(make "plugins" |> adjust ~lvl:root_lvl) in
    Sys.readdir (Path.to_string plugins_dir) |> Array.to_list

  (* XXX: This should go away once we fully use findlib in coqdep;
     for that, we must depend on the META file and pass -m to coqdep.
     Left for a future PR.
   *)
  let local_plugin_flags ~root_lvl =
    let plugins_dir = Path.(make "plugins" |> adjust ~lvl:root_lvl) in
    read_plugin_dir ~root_lvl
    |> List.map (Path.relative plugins_dir)
    |> Util.list_concat_map (fun p -> [Arg.A "-I"; Arg.Path p])

  let findlib_plugin_fixup p =
    ["number_string_notation"; "zify"; "tauto"; "ssreflect"]
    @ (List.filter (fun s -> not (String.equal s "syntax" || String.equal s "ssr")) p)

  (* This can also go when the -I flags are gone, by passing the meta
     file for coq-core *)
  (* Use non-local libs for split build *)
  let findlib_plugin_flags ~root_lvl =
    let () = Findlib.init () in
    read_plugin_dir ~root_lvl
    |> findlib_plugin_fixup
    |> List.map (fun p -> Findlib.package_directory ("coq-core.plugins."^p))
    |> Util.list_concat_map (fun p -> [Arg.A "-I"; Arg.Path (Path.make p)])

  let findlib_plugin_flags ~root_lvl =
    try findlib_plugin_flags ~root_lvl
    with
      Fl_package_base.No_such_package (p,_) ->
      raise (Invalid_argument ("failed to locate Coq plugins in split build mode: " ^ p))

  let plugin_flags ~split =
    if split then findlib_plugin_flags else local_plugin_flags

  (* Native flag *)
  let findlib_native_dir ~root_lvl =
    try
      Findlib.package_directory ("coq-core.kernel") |> Path.make |> Path.adjust ~lvl:root_lvl
    with
      Fl_package_base.No_such_package (p,_) ->
      raise (Invalid_argument ("failed to locate Coq kernel package in split build mode: " ^ p))

  let local_native_dir ~root_lvl =
    Path.make "kernel/.kernel.objs/byte" |> Path.adjust ~lvl:root_lvl

  let kernel_cmi_dir ~split =
    if split then findlib_native_dir else local_native_dir

end

(* dep to vo *)
let path_of_dep ~vo_ext dep =
  let open Coqdeplib.Dep_info in
  let file = match dep with
    | Dep.Require dep -> dep ^ vo_ext
    | Dep.Ml (dep, _ext)-> dep ^ ".cmxs"
    | Dep.Other dep -> dep
  in
  Path.make file

(* dep to cmi, this is hacky, cleanup. A better way is to keep a
   reverse map from files to modules *)
let dot_path s = String.equal s "." || String.equal s ".."
let not_dot_path s = not (dot_path s)
let translate_to_native ~tname dep =
  let dir = Filename.dirname dep in
  let components = String.split_on_char '/' dep |> List.filter not_dot_path in
  let name = String.concat "_" (tname @ components) in
  Filename.concat dir ("N" ^ name ^ ".cmi")

(* Case for prelude.vo *)
let not_dot_path_or_coqlib s = not (dot_path s) && not (String.equal "theories" s)
let translate_boot_to_native dep =
  let dep = Path.to_string dep |> Filename.remove_extension in
  let dir = Filename.dirname dep in
  let components = String.split_on_char '/' dep |> List.filter not_dot_path_or_coqlib in
  let name = String.concat "_" ("Coq"::components) in
  Filename.concat dir ("N" ^ name ^ ".cmi") |> Path.make

let cmi_of_dep ~tname dep =
  let open Coqdeplib.Dep_info in
  let file = match dep with
    | Dep.Require dep ->
      Some (translate_to_native ~tname dep)
    | Dep.Ml (_dep, _ext)-> None
    | Dep.Other _ -> None
  in
  Option.map Path.make file

(* Regular (Some directory_of_stdlib) *)
module Boot_type = struct
  type t = Stdlib | NoInit | Regular of Path.t option
end

(* Context for a Coq theory *)
module Context = struct

  module Flags = struct
    type t =
      { user : Arg.t list
      ; loadpath : Arg.t list
      ; common : Arg.t list
      ; native_common : Arg.t list
      ; native_coqc : Arg.t list
      }
  end

  type t =
    { tname : string list       (* wrapper name *)
    ; flags : Flags.t           (* flags *)
    ; rule : Coq_module.Rule_type.t (* rule kind *)
    ; boot : Boot_type.t        (* type of library *)
    ; dep_info : Dep_info.t
    ; async_deps : string list  (* whether coqc needs the workers *)
    ; package : string          (* installation path under lib/coq *)
    }

  let native_common ~root_lvl ~split =
    let path_coq_kernel_cmi = FlagUtil.kernel_cmi_dir ~root_lvl ~split in
    [ Arg.A "-nI"; Path path_coq_kernel_cmi
    ; A "-native-output-dir"; A "."
    ]

  let native_coqc ~native_common ~native =
    let native_string = if native then "on" else "off" in
    (if native then native_common else [])
    @ Arg.[ A "-w"; A "-deprecated-native-compiler-option"
          ; A "-native-compiler"; A native_string
          ]

  (* XXX: we could put the workers here, but they need a complete OCaml runtime so this is better *)
  let build_async_deps = ["(package coq-core)"]

  (* args are for coqdep *)
  let build_dep_info ~coqdep_args dir_info =
    Dep_info.make ~args:coqdep_args ~dir_info

  let make ~root_lvl ~tname ~user_flags ~rule ~boot ~async ~dir_info ~package ~split =

    let flags =


      (* both coqdep and coqc need the -I flags, coqc otherwise
         doesn't use the legacy plugin resolution method *)
      let plugin_flags = FlagUtil.plugin_flags ~root_lvl ~split in

      let loadpath =
        Arg.[ A "-boot"; A "-R"
            ; Path (Path.make "."); A (String.concat "." tname)
            ]
        @ plugin_flags
      in
      let native_common = native_common ~root_lvl ~split in
      let native_coqc = native_coqc ~native_common ~native:(Coq_module.Rule_type.native_coqc rule) in
      let common = Arg.[ A "-w"; A "+default" ] in

      { Flags.user = user_flags; common; loadpath; native_common; native_coqc } in

    (* coqdep and dep info *)
    let coqdep_args = flags.loadpath in
    let dep_info = build_dep_info ~coqdep_args dir_info in

    let async_deps = if async then build_async_deps else [] in
    { tname; flags; rule; boot; dep_info; async_deps;  package }

end

(* Return flags and deps to inject *)
let prelude_path ~ext = "Init/Prelude" ^ ext

(* This can't happen in Context.make due to the dynamic check for "Init" *)
let boot_module_setup ~cctx coq_module =
  let ext = Coq_module.Rule_type.vo_ext cctx.Context.rule in
  let prelude_path = prelude_path ~ext in
  match cctx.Context.boot with
  | Boot_type.NoInit -> [Arg.A "-noinit"], []
  | Stdlib ->
    (match Coq_module.prefix coq_module with
     | ["Init"] -> [ Arg.A "-noinit" ], []
     | _ -> [ ], [ Path.make prelude_path ]
    )
  | Regular (Some stdlib) ->
    [ Arg.A "-R"; Arg.Path stdlib; Arg.A "Coq" ],
    [ Path.relative stdlib prelude_path]
  | Regular None -> [], []

(* rule generation for a module *)
let module_rule ~(cctx : Context.t) coq_module =
  let tname, rule = cctx.tname, cctx.rule in
  (* retrieve deps *)
  let vfile = Coq_module.source coq_module in
  let vo_ext = Coq_module.Rule_type.vo_ext rule in
  let vfile_deps = Dep_info.lookup ~dep_info:cctx.dep_info vfile |> List.map (path_of_dep ~vo_ext) in
  (* handle -noinit, inject prelude.vo if needed *)
  let boot_flags, boot_deps = boot_module_setup ~cctx coq_module in
  let coqc_flags = cctx.flags.loadpath @ cctx.flags.user @ cctx.flags.common @ cctx.flags.native_coqc in
  let vfile_deps, flags = boot_deps @ vfile_deps, boot_flags @ coqc_flags in
  (* Adjust paths *)
  let lvl = Coq_module.prefix coq_module |> List.length in
  let flags = List.map (Arg.adjust ~lvl) flags |> Arg.List.to_string in
  let deps = List.map (Path.adjust ~lvl) vfile_deps |> List.map Path.to_string in
  (* Depend on the workers if async *)
  let deps = cctx.async_deps @ deps in
  (* Build rule *)
  let vfile_base = Path.basename vfile in
  let action = Format.asprintf "(run coqc %s %s)" flags vfile_base in
  let targets = Coq_module.obj_files ~tname ~rule coq_module in
  let alias = if rule = Coq_module.Rule_type.Quick then Some "vio" else None in
  { Dune_file.Rule.targets; deps; action; alias }

let vio2vo_rule ~(cctx : Context.t) coq_module =
  let _ = cctx in
  let vfile = Coq_module.source coq_module in
  let viofile = Path.replace_ext ~ext:".vio" vfile in

  let boot_flags, _boot_deps = boot_module_setup ~cctx coq_module in
  let flags = Arg.A "-vio2vo" :: boot_flags @ cctx.flags.loadpath in

  (* Non deterministic code in loadpath to pick .vio vs .vo means that
     we can't really do a parallel build of .v to .vio and .vio to .vo

     We have a race condition due to transitive dependencies not
     agreeing on the module chosen, it may happen that a module is
     upgraded to .vo and hence the compilation will boom.

     There are four possible remedies: remove vio, make the vio
     require deterministic, use a `@vio` alias before the main
     build, insert a barrier on which all .vio to .vo depend.

     I guess an alias looks fine for CI for the moment.
  *)
  let viofile_deps = [viofile] in
  (* Adjust paths *)
  let lvl = Coq_module.prefix coq_module |> List.length in
  let flags = List.map (Arg.adjust ~lvl) flags |> Arg.List.to_string in
  let deps = List.map (Path.adjust ~lvl) viofile_deps |> List.map Path.to_string in
  (* vio2vo doesn't follow normal convention... so we can't use Coq_module.obj_files *)
  let vofile_base = Path.replace_ext ~ext:".vo" vfile |> Path.basename in
  let vosfile_base = Path.replace_ext ~ext:".vos" vfile |> Path.basename in
  let targets = [vofile_base; vosfile_base] in
  let viofile_base = Path.basename viofile in
  let action = Format.asprintf "(run coqc %s %s)" flags viofile_base in
  let alias = None in
  { Dune_file.Rule.targets; deps; action; alias }

(* Helper for Dir_info to Subdir *)
let gen_rules ~dir_info ~cctx ~f =
  let f ~prefix sub_acc mods =
    let subdir = Coq_module.prefix_to_dir prefix in
    let payload = List.map (f ~cctx) mods in
    Dune_file.Subdir.{ subdir; payload } :: List.concat sub_acc
  in
  Dir_info.fold ~f ~init:[] dir_info

(* Has to be called in the current dir *)
let vo_rules ~dir_info ~cctx = gen_rules ~dir_info ~cctx ~f:module_rule
let vio2vo_rules ~dir_info ~cctx = gen_rules ~dir_info ~cctx ~f:vio2vo_rule

(* rule generation for .vo -> .{cmi,cmxs} *)
let coqnative_module_rule ~(cctx: Context.t) coq_module =
  let tname = cctx.tname in
  (* deps *)
  let vfile = Coq_module.source coq_module in
  let vofile_deps = Dep_info.lookup ~dep_info:cctx.dep_info vfile |> Util.pmap (cmi_of_dep ~tname) in
  (* base [maybe this should go to coq_module] *)
  let vofile_base = Path.(replace_ext ~ext:".vo" vfile |> basename) in
  (* handle -noinit, inject prelude.vo if needed *)
  let boot_flags, boot_deps = boot_module_setup ~cctx coq_module in
  (* Improve this code *)
  let boot_deps = List.map translate_boot_to_native boot_deps in
  (* Should we pass user and common flags here? They are ignored as of today so we don't *)
  let flags = boot_flags @ cctx.flags.loadpath @ cctx.flags.native_common in
  let vofile_deps = boot_deps @ vofile_deps in
  (* Adjust paths *)
  let lvl = Coq_module.prefix coq_module |> List.length in
  let flags = List.map (Arg.adjust ~lvl) flags |> Arg.List.to_string in
  let deps = List.map (Path.adjust ~lvl) vofile_deps |> List.map Path.to_string in
  (* Build rule *)
  let action = Format.asprintf "(run coqnative %s %s)" flags vofile_base in
  let targets = Coq_module.native_obj_files ~tname coq_module in
  let deps = vofile_base :: deps in
  let alias = None in
  { Dune_file.Rule.targets; deps; action; alias }

let coqnative_rules ~dir_info ~cctx = gen_rules ~dir_info ~cctx ~f:coqnative_module_rule

let install_rule ~(cctx : Context.t) coq_module =
  let tname, rule, package = cctx.tname, cctx.rule, cctx.package in
  let dst_base = Filename.concat "coq" package in
  let files =
    Coq_module.install_files ~tname ~rule coq_module
    |> List.map (fun (src,dst) -> src, Filename.concat dst_base dst) in
  (* May need to woraround invalid empty `(install )` stanza if that happens *)
  Dune_file.Install.{ section = "lib_root"; package = "coq-stdlib"; files }

let install_rules ~dir_info ~cctx = gen_rules ~dir_info ~cctx ~f:install_rule
