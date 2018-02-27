(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

let _ = Coqide.set_signal_handlers ()
let _ = GtkMain.Main.init ()

(* We handle Gtk warning messages ourselves :
   - on win32, we don't want them to end on a non-existing console
   - we display critical messages via pop-ups *)

let catch_gtk_messages () =
  let all_levels =
    [`FLAG_RECURSION;`FLAG_FATAL;`ERROR;`CRITICAL;`WARNING;
     `MESSAGE;`INFO;`DEBUG]
  in
  let log_level lvl =
    let level_is tag = (lvl land Glib.Message.log_level tag) <> 0 in
    if level_is `ERROR then `FATAL
    else if level_is `CRITICAL then `ERROR
    else if level_is `DEBUG then `DEBUG
    else if level_is `WARNING then `WARNING
    else if level_is `MESSAGE then `NOTICE
    else `INFO
  in
  let handler ~level msg =
    let header = "Coqide internal error: " in
    match log_level level with
      |`FATAL ->
        let () = GToolbox.message_box ~title:"Error" (header ^ msg) in
        Coqide.crash_save 1
      |`ERROR ->
        if !Flags.debug then GToolbox.message_box ~title:"Error" (header ^ msg)
        else Printf.eprintf "%s\n" (header ^ msg)
      |`DEBUG -> Minilib.log msg
      |level when Sys.os_type = "Win32" -> Minilib.log ~level msg
      |_ -> Printf.eprintf "%s\n" msg
  in
  let catch domain =
    ignore (Glib.Message.set_log_handler ~domain ~levels:all_levels handler)
  in
  List.iter catch ["GLib";"Gtk";"Gdk";"Pango"]

let () = catch_gtk_messages ()



(** System-dependent settings *)

let os_specific_init () = ()

(** Win32 *)

IFDEF WIN32 THEN

(* On win32, we add the directory of coqide to the PATH at launch-time
   (this used to be done in a .bat script). *)

let set_win32_path () =
  Unix.putenv "PATH"
    (Filename.dirname Sys.executable_name ^ ";" ^
      (try Sys.getenv "PATH" with _ -> ""))

(* On win32, since coqide is now console-free, we re-route stdout/stderr
   to avoid Sys_error if someone writes to them. We write to a pipe which
   is never read (by default) or to a temp log file (when in debug mode).
*)

let reroute_stdout_stderr () =
  (* We anticipate a bit the argument parsing and look for -debug *)
  let debug = List.mem "-debug" (Array.to_list Sys.argv) in
  Minilib.debug := debug;
  let out_descr =
    if debug then
      let (name,chan) = Filename.open_temp_file "coqide_" ".log" in
      Coqide.logfile := Some name;
      Unix.descr_of_out_channel chan
    else
      snd (Unix.pipe ())
  in
  Unix.set_close_on_exec out_descr;
  Unix.dup2 out_descr Unix.stdout;
  Unix.dup2 out_descr Unix.stderr

(* We also provide specific kill and interrupt functions. *)

external win32_kill : int -> unit = "win32_kill"
external win32_interrupt : int -> unit = "win32_interrupt"
let () =
  Coq.gio_channel_of_descr_socket := Glib.Io.channel_of_descr_socket;
  set_win32_path ();
  Coq.interrupter := win32_interrupt;
  reroute_stdout_stderr ()
END

(** MacOSX *)

IFDEF QUARTZ THEN
let osx = GosxApplication.osxapplication ()

let () =
  let _ = osx#connect#ns_application_open_file
    ~callback:(fun x -> Coqide.do_load x; true)
  in
  let _ = osx#connect#ns_application_block_termination
    ~callback:Coqide.forbid_quit
  in
  let _ = osx#connect#ns_application_will_terminate
    ~callback:Coqide.close_and_quit
  in ()

let os_specific_init () =
  let () = GtkosxApplication.Application.set_menu_bar osx#as_osxapplication
    (GtkMenu.MenuShell.cast
       (Coqide_ui.ui_m#get_widget "/CoqIde MenuBar")#as_widget)
  in
  let () = GtkosxApplication.Application.insert_app_menu_item
    osx#as_osxapplication
    (Coqide_ui.ui_m#get_widget "/CoqIde MenuBar/Edit/Prefs")#as_widget 1
  in
  let () = GtkosxApplication.Application.set_help_menu osx#as_osxapplication
    (Some (GtkMenu.MenuItem.cast
             (Coqide_ui.ui_m#get_widget "/CoqIde MenuBar/Help")#as_widget))
  in
  osx#ready ()
END

let load_prefs () =
  try Preferences.load_pref ()
  with e -> Ideutils.flash_info
    ("Could not load preferences ("^Printexc.to_string e^").")

let () =
  load_prefs ();
  let argl = List.tl (Array.to_list Sys.argv) in
  let argl = Coqide.read_coqide_args argl in
  let files = Coq.filter_coq_opts argl in
  let args = List.filter (fun x -> not (List.mem x files)) argl in
  Coq.check_connection args;
  Coqide.sup_args := args;
  Coqide.main files;
  os_specific_init ();
  try
    GMain.main ();
    failwith "Gtk loop ended"
  with e ->
    Minilib.log ("CoqIde unexpected error:" ^ Printexc.to_string e);
    Coqide.crash_save 127
