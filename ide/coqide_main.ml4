IFDEF MacInt THEN
external gtk_mac_init : (string -> unit) -> unit
  = "caml_gtk_mac_init"

external gtk_mac_ready : unit -> unit
  = "caml_gtk_mac_ready"
END

let initmac () = IFDEF MacInt THEN gtk_mac_init Coqide.do_load ELSE () END

let macready () = IFDEF MacInt THEN gtk_mac_ready () ELSE ()  END

let () =
  let argl = Array.to_list Sys.argv in
  let files = Coqide.process_argv argl in
  let args = List.filter (fun x -> not (List.mem x files)) (List.tl argl) in
  Coqide.sup_args := List.map Filename.quote args;
  Coq.check_connection !Coqide.sup_args;
  Coqide.ignore_break ();
    GtkMain.Rc.add_default_file (Ideutils.lib_ide_file ".coqide-gtk2rc");
    (try
	 GtkMain.Rc.add_default_file (Filename.concat System.home ".coqide-gtk2rc");
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
		  then Pp.warning msg
		  else failwith ("Coqide internal error: " ^ msg)));
    Coqide.main files;
    if !Coq_config.with_geoproof then ignore (Thread.create Coqide.check_for_geoproof_input ());
    macready () ;
    while true do
      try
	GtkThread.main ()
      with
	| Sys.Break -> prerr_endline "Interrupted." ; flush stderr
	| e ->
	    Pervasives.prerr_endline ("CoqIde unexpected error:" ^ (Printexc.to_string e));
	    flush stderr;
	    Coqide.crash_save 127
    done
