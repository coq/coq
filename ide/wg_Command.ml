(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Preferences

class command_window coqtop
  ~mark_as_broken ~mark_as_processed ~cur_state
=
(*  let window = GWindow.window
		 ~allow_grow:true ~allow_shrink:true
		 ~width:500 ~height:250
		 ~position:`CENTER
		 ~title:"CoqIde queries" ~show:false ()
  in *)
  let views = ref [] in
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

  let remove_cb () =
    let index = notebook#current_page in
    let () = notebook#remove_page index in
    views := Util.List.filteri (fun i x -> i <> index) !views
  in
  let _ =
    toolbar#insert_button
      ~tooltip:"Delete Page"
      ~text:"Delete Page"
      ~icon:(Ideutils.stock_to_widget `DELETE)
      ~callback:remove_cb
      ()
  in
object(self)
  val frame = frame


  val new_page_menu = new_page_menu
  val notebook = notebook

  method frame = frame
  method new_command ?command ?term () =
    let frame = GBin.frame
		  ~shadow_type:`ETCHED_OUT
		  ()
    in
    let _ = notebook#append_page frame#coerce in
    notebook#goto_page (notebook#page_num frame#coerce);
    let vbox = GPack.vbox ~homogeneous:false ~packing:frame#add () in
    let hbox = GPack.hbox ~homogeneous:false ~packing:vbox#pack () in
    let (combo,_) = GEdit.combo_box_entry_text ~strings:Coq_commands.state_preserving
		  ~packing:hbox#pack
		  ()
    in
    let on_activate c () =
      if List.mem combo#entry#text Coq_commands.state_preserving then c ()
      else Minilib.log "Not a state preserving command"
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
    let () = views := !views @ [result] in
    result#misc#modify_font current.text_font;
    let clr = Tags.color_of_string current.background_color in
    result#misc#modify_base [`NORMAL, `COLOR clr];
    result#misc#set_can_focus true; (* false causes problems for selection *)
    result#set_editable false;
    let callback () =
      let com = combo#entry#text in
      let phrase =
	if String.get com (String.length com - 1) = '.'
	then com ^ " " else com ^ " " ^ entry#text ^" . "
      in
      let log level message = result#buffer#insert (message^"\n") in
      let process =
	Coq.bind (Coq.query ~logger:log (phrase,Stateid.dummy)) (function
          | Interface.Fail (_,l,str) ->
            result#buffer#insert str;
	    Coq.return ()
          | Interface.Good res ->
            result#buffer#insert res; 
	    Coq.return ())
      in
      result#buffer#set_text ("Result for command " ^ phrase ^ ":\n");
      Coq.try_grab coqtop process ignore
    in
    ignore (combo#entry#connect#activate ~callback:(on_activate callback));
    ignore (ok_b#connect#clicked ~callback:(on_activate callback));

    begin match command with
      | None -> ()
      | Some c -> combo#entry#set_text c
    end;
    begin match term with
      | None -> ()
      | Some t -> entry#set_text t
    end;
    on_activate callback ();
    entry#misc#grab_focus ();
    entry#misc#grab_default ();
    ignore (entry#connect#activate ~callback);
    ignore (combo#entry#connect#activate ~callback);
    self#frame#misc#show ()

  method refresh_font () =
    let iter view = view#misc#modify_font current.text_font in
    List.iter iter !views

  method refresh_color () =
    let clr = Tags.color_of_string current.background_color in
    let iter view = view#misc#modify_base [`NORMAL, `COLOR clr] in
    List.iter iter !views

  initializer
    ignore (new_page_menu#connect#clicked ~callback:self#new_command);
   (* ignore (window#event#connect#delete (fun _ -> window#misc#hide(); true));*)
end
