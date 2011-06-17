(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

class command_window coqtop current =
(*  let window = GWindow.window
		 ~allow_grow:true ~allow_shrink:true
		 ~width:500 ~height:250
		 ~position:`CENTER
		 ~title:"CoqIde queries" ~show:false ()
  in *)
  let frame = GBin.frame ~label:"Command Pane" ~shadow_type:`IN () in
  let _ = frame#misc#hide () in
  let _ = GtkData.AccelGroup.create () in
  let hbox = GPack.hbox ~homogeneous:false ~packing:frame#add () in
  let toolbar = GButton.toolbar
		  ~orientation:`VERTICAL
		  ~style:`ICONS
		  ~tooltips:true
		  ~packing:(hbox#pack
			       ~expand:false
			       ~fill:false)
		  ()
  in
  let notebook = GPack.notebook ~scrollable:true
		   ~packing:(hbox#pack
			       ~expand:true
			       ~fill:true
			    )
		   ()
  in
  let _ =
    toolbar#insert_button
      ~tooltip:"Hide Commands Pane"
      ~text:"Hide Pane"
      ~icon:(Ideutils.stock_to_widget `CLOSE)
      ~callback:frame#misc#hide
      ()
  in
  let new_page_menu =
    toolbar#insert_button
      ~tooltip:"New Page"
      ~text:"New Page"
      ~icon:(Ideutils.stock_to_widget `NEW)
      ()
  in

  let _ =
    toolbar#insert_button
      ~tooltip:"Delete Page"
      ~text:"Delete Page"
      ~icon:(Ideutils.stock_to_widget `DELETE)
      ~callback:(fun () -> notebook#remove_page notebook#current_page)
      ()
  in
object(self)
  val frame = frame


  val new_page_menu = new_page_menu
  val notebook = notebook
  method frame = frame
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
    result#misc#modify_font !current.Preferences.text_font;
    result#misc#set_can_focus true; (* false causes problems for selection *)
    result#set_editable false;
    let callback () =
      let com = combo#entry#text in
      let phrase =
	if String.get com (String.length com - 1) = '.'
	then com ^ " " else com ^ " " ^ entry#text ^" . "
      in
      try
        result#buffer#set_text
          (match Coq.raw_interp coqtop phrase with
             | Ide_intf.Fail (l,str) ->
                 ("Error while interpreting "^phrase^":\n"^str)
             | Ide_intf.Good () ->
                 match Coq.read_stdout coqtop with
                   | Ide_intf.Fail (l,str) ->
                       ("Error while fetching "^phrase^"results:\n"^str)
                   | Ide_intf.Good results ->
                       ("Result for command " ^ phrase ^ ":\n" ^ results))
      with e ->
	let s = Printexc.to_string e in
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
    self#frame#misc#show ()

  initializer
    ignore (new_page_menu#connect#clicked ~callback:self#new_command);
   (* ignore (window#event#connect#delete (fun _ -> window#misc#hide(); true));*)
end
