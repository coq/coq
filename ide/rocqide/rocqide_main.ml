(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

let _ = Rocqide.set_signal_handlers ()

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
    let header = "RocqIDE internal error: " in
    match log_level level with
      |`FATAL ->
        let () = GToolbox.message_box ~title:"Error" (header ^ msg) in
        Rocqide.crash_save 1
      |`ERROR ->
        if CDebug.(get_flag misc) then GToolbox.message_box ~title:"Error" (header ^ msg)
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

let load_prefs () =
  Preferences.load_pref ~warn:(fun ~delay -> Ideutils.flash_info ~delay)

let () =
  Ideutils.push_info ("Ready"^ if Preferences.microPG#get then ", [μPG]" else "");
  load_prefs ();
  let argl = List.tl (Array.to_list Sys.argv) in
  let argl = Rocqide.read_rocqide_args argl in
  let files = RocqDriver.filter_rocq_opts argl in
  let args = List.filter (fun x -> not (List.mem x files)) argl in
  RocqDriver.check_connection args;
  Rocqide.sup_args := args;
  let w = Rocqide.main files in
  Rocqide.set_signal_handlers ~parent:w ();
  Rocqide_os_specific.init ();
  Shared_os_specific.init ();
  try
    GMain.main ();
    failwith "Gtk loop ended"
  with e ->
    Minilib.log ("RocqIDE unexpected error: " ^ Printexc.to_string e);
    Rocqide.crash_save 127
