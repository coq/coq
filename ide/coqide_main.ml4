(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

IFDEF MacInt THEN
external gtk_mac_init : (string -> unit) -> (unit -> bool) -> unit
  = "caml_gtk_mac_init"

external gtk_mac_ready : unit -> unit
  = "caml_gtk_mac_ready"
END

let initmac () = IFDEF MacInt THEN gtk_mac_init Coqide.do_load Coqide.forbid_quit_to_save ELSE () END

let macready () = IFDEF MacInt THEN gtk_mac_ready () ELSE ()  END

(* On win32, we add the directory of coqide to the PATH at launch-time
   (this used to be done in a .bat script).
   We also provide a specific kill function.
*)

IFDEF Win32 THEN
external win32_kill : int -> unit = "win32_kill"
let () =
  Unix.putenv "PATH"
    (Filename.dirname Sys.executable_name ^ ";" ^
      (try Sys.getenv "PATH" with _ -> ""));
  Coq.killer := win32_kill
END

let () =
  let argl = Array.to_list Sys.argv in
  let argl = Coqide.set_coqtop_path argl in
  let files = Coqide.process_argv argl in
  let args = List.filter (fun x -> not (List.mem x files)) (List.tl argl) in
  Coq.check_connection args;
  Minilib.coqlib := Coq.check_coqlib args;
  Coqide.sup_args := args;
  Coqide.ignore_break ();
    GtkMain.Rc.add_default_file (Ideutils.lib_ide_file ".coqide-gtk2rc");
    (try
	 GtkMain.Rc.add_default_file (Filename.concat Minilib.home ".coqide-gtk2rc");
     with Not_found -> ());
    ignore (GtkMain.Main.init ());
    initmac () ;
(*    GtkData.AccelGroup.set_default_mod_mask
      (Some [`CONTROL;`SHIFT;`MOD1;`MOD3;`MOD4]);*)
    ignore (
	     Glib.Message.set_log_handler ~domain:"Gtk" ~levels:[`ERROR;`FLAG_FATAL;
								 `WARNING;`CRITICAL]
	       (fun ~level msg ->
		  if level land Glib.Message.log_level `WARNING <> 0
		  then Printf.eprintf "Warning: %s\n" msg
		  else failwith ("Coqide internal error: " ^ msg)));
    Coqide.main files;
    if !Coq_config.with_geoproof then ignore (Thread.create Coqide.check_for_geoproof_input ());
    macready () ;
    while true do
      try
	GtkThread.main ()
      with
	| Sys.Break -> Ideutils.prerr_endline "Interrupted."
	| e ->
	    Ideutils.safe_prerr_endline
	      ("CoqIde unexpected error:" ^ (Printexc.to_string e));
	    Coqide.crash_save 127
    done
