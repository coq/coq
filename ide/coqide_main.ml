(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

let _ = Coqide.set_signal_handlers ()

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
  let w = Coqide.main files in
  Coqide.set_signal_handlers ~parent:w ();
  Coqide_os_specific.init ();
  try
    GMain.main ();
    failwith "Gtk loop ended"
  with e ->
    Minilib.log ("CoqIde unexpected error:" ^ Printexc.to_string e);
    Coqide.crash_save 127
