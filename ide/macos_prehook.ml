let append_to_var var value =
  let new_val =
    try value ^ ":" ^ Unix.getenv var
    with Not_found -> value in
  Unix.putenv var new_val

let resources_dir =
  let working_dir = Sys.getcwd () in
  let () = Sys.chdir (Filename.dirname (Sys.executable_name)) in
  let app_root_dir = Filename.dirname (Sys.getcwd ()) in
  let () = Sys.chdir working_dir in
  Filename.concat app_root_dir "Resources"

let lib_dir = Filename.concat resources_dir "lib"
let etc_dir = Filename.concat resources_dir "etc"
let xdg_home = Filename.concat (Sys.getenv "HOME") "Library/Application Support"

let () = Unix.putenv "DYLD_LIBRARY_PATH" lib_dir
let () = Unix.putenv "XDG_DATA_HOME" xdg_home
let () = Unix.putenv "XDG_CONFIG_HOME" xdg_home
let () = append_to_var "XDG_DATA_DIRS" (Filename.concat resources_dir "share")
let () = append_to_var "XDG_CONFIG_DIRS" (Filename.concat etc_dir "xdg")
let () = Unix.putenv "GTK_DATA_PREFIX" resources_dir
let () = Unix.putenv "GTK_EXE_PREFIX" resources_dir
let () = Unix.putenv "GTK_PATH" resources_dir
let () =
  Unix.putenv "GTK2_RC_FILES" (Filename.concat etc_dir "gtk-2.0/gtkrc")
let () =
  Unix.putenv "GTK_IM_MODULE_FILE"
   (Filename.concat etc_dir "gtk-2.0/gtk-immodules.loaders")
let () =
  Unix.putenv "GDK_PIXBUF_MODULE_FILE"
   (Filename.concat etc_dir "gtk-2.0/gdk-pixbuf.loaders")
let () = Unix.putenv "PANGO_LIBDIR" lib_dir
let () = Unix.putenv "PANGO_SYSCONFIGDIR" etc_dir
let () = Unix.putenv "CHARSETALIASDIR" lib_dir
let () = append_to_var "PATH" (Filename.concat resources_dir "bin")
