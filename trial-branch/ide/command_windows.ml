(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

class command_window () = 
  let window = GWindow.window 
		 ~allow_grow:true ~allow_shrink:true 
		 ~width:320 ~height:200
		 ~position:`CENTER
		 ~title:"CoqIde queries" ~show:false ()
  in
  let _ = GtkData.AccelGroup.create () in
  let vbox = GPack.vbox ~homogeneous:false ~packing:window#add () in
  let toolbar = GButton.toolbar 
		  ~orientation:`HORIZONTAL 
		  ~style:`ICONS
		  ~tooltips:true 
		  ~packing:(vbox#pack 
			       ~expand:false
			       ~fill:false)
		  ()
  in
  let notebook = GPack.notebook ~scrollable:true 
		   ~packing:(vbox#pack 
			       ~expand:true
			       ~fill:true
			    ) 
		   ()
  in
  let _ = 
    toolbar#insert_button
      ~tooltip:"Hide Window"
      ~text:"Hide Window"
      ~icon:(Ideutils.stock_to_widget ~size:`LARGE_TOOLBAR `CLOSE)
      ~callback:window#misc#hide
      ()
  in
  let new_page_menu = 
    toolbar#insert_button
      ~tooltip:"New Page"
      ~text:"New Page"
      ~icon:(Ideutils.stock_to_widget ~size:`LARGE_TOOLBAR `NEW)
(*
      ~callback:window#misc#hide
*)
      ()
  in

  let _ = 
    toolbar#insert_button
      ~tooltip:"Kill Page"
      ~text:"Kill Page"
      ~icon:(Ideutils.stock_to_widget ~size:`LARGE_TOOLBAR `DELETE)
      ~callback:(fun () -> notebook#remove_page notebook#current_page)
      ()
  in
object(self)
  val window = window
(*
  val menubar = menubar
*)
  val new_page_menu = new_page_menu
  val notebook = notebook
  method window = window
  method new_command ?command ?term () =
    let appendp x = ignore (notebook#append_page x) in
    let frame = GBin.frame 
		  ~shadow_type:`ETCHED_OUT
		  ~packing:appendp
		  ()
    in
    notebook#goto_page (notebook#page_num frame#coerce);
    let vbox = GPack.vbox ~homogeneous:false ~packing:frame#add () in
    let hbox = GPack.hbox ~homogeneous:false ~packing:vbox#pack () in
    let combo = GEdit.combo ~popdown_strings:Coq_commands.state_preserving
		  ~enable_arrow_keys:true
		  ~allow_empty:false
		  ~value_in_list:false (* true is not ok with disable_activate...*)
		  ~packing:hbox#pack
		  ()
    in
    combo#disable_activate ();
    let on_activate c () = 
      if List.mem combo#entry#text Coq_commands.state_preserving then c () 
      else prerr_endline "Not a state preserving command" 
    in
    let entry = GEdit.entry ~packing:(hbox#pack ~expand:true) () in
    entry#misc#set_can_default true;
    let r_bin =
      GBin.scrolled_window 
	~vpolicy:`AUTOMATIC 
	~hpolicy:`AUTOMATIC
	~packing:(vbox#pack ~fill:true ~expand:true) () in
    let ok_b = GButton.button ~label:"Ok" ~packing:(hbox#pack ~expand:false) () in
    let result = GText.view ~packing:r_bin#add () in
    result#misc#set_can_focus true; (* false causes problems for selection *)
    result#set_editable false;
    let callback () =
      let com = combo#entry#text in
      let phrase = 
	if String.get com (String.length com - 1) = '.'
	then com ^ " " else com ^ " " ^ entry#text ^" . " 
      in
      try
	ignore(Coq.interp false phrase);
	result#buffer#set_text 
	  ("Result for command " ^ phrase ^ ":\n" ^ Ideutils.read_stdout ())
      with e ->
	let (s,loc) = Coq.process_exn e in
	assert (Glib.Utf8.validate s);
	result#buffer#set_text s
    in
    ignore (combo#entry#connect#activate ~callback:(on_activate callback));
    ignore (ok_b#connect#clicked ~callback:(on_activate callback));

    begin match command,term with 
      | None,None -> ()
      | Some c, None -> 
	  combo#entry#set_text c;
	  
      | Some c, Some t -> 
	  combo#entry#set_text c;
	  entry#set_text t
	 
      | None , Some t -> 
	  entry#set_text t
    end;
    on_activate callback ();
    entry#misc#grab_focus ();
    entry#misc#grab_default ();
    ignore (entry#connect#activate ~callback);
    ignore (combo#entry#connect#activate ~callback);
    self#window#present ()

  initializer 
    ignore (new_page_menu#connect#clicked self#new_command);
    ignore (window#event#connect#delete (fun _ -> window#misc#hide(); true));
end

let command_window = ref None

let main () = command_window := Some (new command_window ())

let command_window () = match !command_window with 
  | None -> failwith "No command window."
  | Some c -> c
