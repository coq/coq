(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

let _ = Coqide.ignore_break ()
let _ = GtkMain.Main.init ()

(* We handle Gtk warning messages ourselves :
   - on win32, we don't want them to end on a non-existing console
   - we display critical messages via pop-ups *)

let catch_gtk_messages () =
  let all_levels =
    [`FLAG_RECURSION;`FLAG_FATAL;`ERROR;`CRITICAL;`WARNING;
     `MESSAGE;`INFO;`DEBUG]
  in
  let handler ~level msg =
    let header = "Coqide internal error: " in
    let level_is tag = (level land Glib.Message.log_level tag) <> 0 in
    if level_is `ERROR then
      let () = GToolbox.message_box ~title:"Error" (header ^ msg) in
      Coqide.crash_save 1
    else if level_is `CRITICAL then
      GToolbox.message_box ~title:"Error" (header ^ msg)
    else if level_is `DEBUG || Sys.os_type = "Win32" then
      Ideutils.prerr_endline msg (* no-op unless in debug mode *)
    else
      Printf.eprintf "%s\n" msg
  in
  let catch domain =
    ignore (Glib.Message.set_log_handler ~domain ~levels:all_levels handler)
  in
  List.iter catch ["GLib";"Gtk";"Gdk";"Pango"]

let () = catch_gtk_messages ()

(* We anticipate a bit the argument parsing and look for -debug *)

let early_set_debug () =
  Ideutils.debug := List.mem "-debug" (Array.to_list Sys.argv)

(* On win32, we add the directory of coqide to the PATH at launch-time
   (this used to be done in a .bat script). *)

let set_win32_path () =
  Unix.putenv "PATH"
    (Filename.dirname Sys.executable_name ^ ";" ^
      (try Sys.getenv "PATH" with _ -> ""))

(* On win32, in debug mode we duplicate stdout/stderr in a log file. *)

let log_stdout_stderr () =
  let (name,chan) = Filename.open_temp_file "coqide_" ".log" in
  Coqide.logfile := Some name;
  let out_descr = Unix.descr_of_out_channel chan in
  Unix.set_close_on_exec out_descr;
  Unix.dup2 out_descr Unix.stdout;
  Unix.dup2 out_descr Unix.stderr

(* We also provide specific kill and interrupt functions. *)

IFDEF WIN32 THEN
external win32_kill : int -> unit = "win32_kill"
external win32_interrupt_all : unit -> unit = "win32_interrupt_all"
external win32_hide_console : unit -> unit = "win32_hide_console"

let () =
  set_win32_path ();
  Coq.killer := win32_kill;
  Coq.interrupter := (fun pid -> win32_interrupt_all ());
  early_set_debug ();
  if !Ideutils.debug then
    log_stdout_stderr ()
  else
    win32_hide_console ()
END

IFDEF QUARTZ THEN
  let osx = GosxApplication.osxapplication ()

  let _ =
    osx#connect#ns_application_open_file ~callback:(fun x -> Coqide.do_load x; true) in
  let _ =
    osx#connect#ns_application_block_termination ~callback:Coqide.forbid_quit_to_save in
  ()
END

let () =
  (try
     let gtkrcdir = List.find
       (fun x -> Sys.file_exists (Filename.concat x "coqide-gtk2rc"))
       Minilib.xdg_config_dirs in
     GtkMain.Rc.add_default_file (Filename.concat gtkrcdir "coqide-gtk2rc");
   with Not_found -> ());
  (* Statup preferences *)
  begin
    try Preferences.load_pref ()
    with e ->
      Ideutils.flash_info ("Could not load preferences ("^Printexc.to_string e^").");
  end;
(*    GtkData.AccelGroup.set_default_mod_mask
      (Some [`CONTROL;`SHIFT;`MOD1;`MOD3;`MOD4]);*)
  let argl = Array.to_list Sys.argv in
  let argl = Coqide.read_coqide_args argl in
  let files = Coq.filter_coq_opts (List.tl argl) in
  let args = List.filter (fun x -> not (List.mem x files)) (List.tl argl) in
  Coq.check_connection args;
  Coqide.sup_args := args;
  Coqide.main files;
    if !Coq_config.with_geoproof then ignore (Thread.create Coqide.check_for_geoproof_input ())

IFDEF QUARTZ THEN
  let () =
    GtkosxApplication.Application.set_menu_bar osx#as_osxapplication (GtkMenu.MenuShell.cast (Coqide_ui.ui_m#get_widget "/CoqIde MenuBar")#as_widget) in
  let () =
    GtkosxApplication.Application.insert_app_menu_item osx#as_osxapplication (Coqide_ui.ui_m#get_widget "/CoqIde MenuBar/Edit/Prefs")#as_widget 1 in
  let () =
    GtkosxApplication.Application.set_help_menu osx#as_osxapplication (Some (GtkMenu.MenuItem.cast (Coqide_ui.ui_m#get_widget "/CoqIde MenuBar/Help")#as_widget)) in
  osx#ready ()
END

    while true do
      try
	GtkThread.main ()
      with
	| Sys.Break -> Ideutils.prerr_endline "Interrupted."
	| e ->
	    Minilib.safe_prerr_endline
	      ("CoqIde unexpected error:" ^ (Printexc.to_string e));
	    Coqide.crash_save 127
    done
