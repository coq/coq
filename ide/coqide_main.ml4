(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

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
  let out_descr =
    if !Minilib.debug then
      Unix.descr_of_out_channel (snd (Filename.open_temp_file "coqide_" ".log"))
    else
      snd (Unix.pipe ())
  in
  Unix.dup2 out_descr Unix.stdout;
  Unix.dup2 out_descr Unix.stderr

(* We also provide specific kill and interrupt functions. *)

(* Since [win32_interrupt] involves some hack about the process console,
   only one should run at the same time, we simply skip execution of
   [win32_interrupt] if another instance is already running *)

let ctrl_c_mtx = Mutex.create ()

let ctrl_c_protect f i =
  if not (Mutex.try_lock ctrl_c_mtx) then ()
  else try f i; Mutex.unlock ctrl_c_mtx with _ -> Mutex.unlock ctrl_c_mtx

IFDEF WIN32 THEN
external win32_kill : int -> unit = "win32_kill"
external win32_interrupt : int -> unit = "win32_interrupt"
let () =
  Coq.killer := win32_kill;
  Coq.interrupter := ctrl_c_protect win32_interrupt;
  set_win32_path ();
  reroute_stdout_stderr ()
END

let () =
  Coqide.ignore_break ();
  ignore (GtkMain.Main.init ())

IFDEF QUARTZ THEN
  let osx = GosxApplication.osxapplication ()

  let _ =
    osx#connect#ns_application_open_file ~callback:(fun x -> Coqide.do_load x; true) in
  let _ =
    osx#connect#ns_application_block_termination ~callback:Coqide.forbid_quit_to_save in
  ()
END

let () =
  (* Statup preferences *)
  begin
    try Preferences.load_pref ()
    with e ->
      Ideutils.flash_info ("Could not load preferences ("^Printexc.to_string e^").");
  end;
(*    GtkData.AccelGroup.set_default_mod_mask
      (Some [`CONTROL;`SHIFT;`MOD1;`MOD3;`MOD4]);*)
    ignore (
	     Glib.Message.set_log_handler ~domain:"Gtk" ~levels:[`ERROR;`FLAG_FATAL;
								 `WARNING;`CRITICAL]
	       (fun ~level msg ->
		  if level land Glib.Message.log_level `WARNING <> 0
		  then Printf.eprintf "Warning: %s\n" msg
		  else failwith ("Coqide internal error: " ^ msg)));
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
	| Sys.Break -> Minilib.log "Interrupted."
	| e ->
	    Minilib.log
	      ("CoqIde unexpected error:" ^ (Printexc.to_string e));
	    Coqide.crash_save 127
    done
