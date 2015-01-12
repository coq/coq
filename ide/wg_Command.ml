(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Preferences

class command_window name coqtop =
  let frame = Wg_Detachable.detachable
    ~title:(Printf.sprintf "Query pane (%s)" name) () in
  let _ = frame#hide in
  let _ = GtkData.AccelGroup.create () in
  let notebook =
    GPack.notebook ~height:200 ~scrollable:true ~packing:frame#add () in
  let _ = frame#connect#attached ~callback:(fun _ ->
    notebook#misc#set_size_request ~height:200 ()) in
  let _ = frame#connect#detached ~callback:(fun _ ->
    notebook#misc#set_size_request ~width:600 ~height:500 ();
    notebook#misc#grab_focus ()) in

object(self)
  val frame = frame

  val notebook = notebook

  method pack_in (f : GObj.widget -> unit) = f frame#coerce

  val mutable new_page : GObj.widget = (GMisc.label ())#coerce

  val mutable views = []

  method private new_page_maker =
    let page = notebook#append_page
      (GMisc.label ~text:"No query" ())#coerce in
    let page = notebook#get_nth_page page in
    let b = GButton.button () in
    b#add (Ideutils.stock_to_widget ~size:(`CUSTOM(12,12)) `NEW);
    ignore(b#connect#clicked ~callback:self#new_query);
    notebook#set_page ~tab_label:b#coerce page;
    new_page <- page

  method new_query ?command ?term () = self#new_query_aux ?command ?term ()

  method private new_query_aux ?command ?term ?(grab_now=true) () =
    let frame = GBin.frame ~shadow_type:`NONE () in
    ignore(notebook#insert_page ~pos:(notebook#page_num new_page) frame#coerce);
    let new_tab_lbl text =
      let hbox = GPack.hbox ~homogeneous:false () in
      ignore(GMisc.label ~width:100 ~ellipsize:`END ~text ~packing:hbox#pack());
      let b = GButton.button ~packing:hbox#pack () in
      ignore(b#connect#clicked ~callback:(fun () ->
        views <-
          List.filter (fun (f,_,_) -> f#get_oid <> frame#coerce#get_oid) views;
        notebook#remove_page (notebook#page_num frame#coerce)));
      b#add (Ideutils.stock_to_widget ~size:(`CUSTOM(12,10)) `CLOSE);
      hbox#coerce in
    notebook#set_page ~tab_label:(new_tab_lbl "New query") frame#coerce;
    notebook#goto_page (notebook#page_num frame#coerce);
    let vbox = GPack.vbox ~homogeneous:false ~packing:frame#add () in
    let combo, entry, ok_b =
      let bar =
        GButton.toolbar ~style:`ICONS ~packing:(vbox#pack ~expand:false) () in
      let bar_add ~expand w =
        let item = GButton.tool_item ~expand () in
        item#add w#coerce;
        bar#insert item in
      let combo, _ =
        GEdit.combo_box_entry_text ~strings:Coq_commands.state_preserving () in
      combo#entry#set_text "Search";
      let entry = GEdit.entry () in
      entry#misc#set_can_default true;
      let ok_b = GButton.button () in
      ok_b#add (Ideutils.stock_to_widget `OK);
      bar_add ~expand:false combo;
      bar_add ~expand:true entry;
      bar_add ~expand:false ok_b;
      combo, entry, ok_b in
    let r_bin =
      GBin.scrolled_window
	~vpolicy:`AUTOMATIC
	~hpolicy:`AUTOMATIC
	~packing:(vbox#pack ~fill:true ~expand:true) () in
    let result = GText.view ~packing:r_bin#add () in
    views <- (frame#coerce, result, combo#entry) :: views;
    result#misc#modify_font current.text_font;
    let clr = Tags.color_of_string current.background_color in
    result#misc#modify_base [`NORMAL, `COLOR clr];
    result#misc#set_can_focus true; (* false causes problems for selection *)
    result#set_editable false;
    let callback () =
      let com = combo#entry#text in
      let arg = entry#text in
      if Str.string_match (Str.regexp "^ *$") (com^arg) 0 then () else
      let phrase =
        if Str.string_match (Str.regexp "\\. *$") com 0 then com
        else com ^ " " ^ arg ^" . "
      in
      let log level message = result#buffer#insert (message^"\n") in
      let process =
	Coq.bind (Coq.query ~logger:log (phrase,Stateid.dummy)) (function
          | Interface.Fail (_,l,str) ->
            result#buffer#insert str;
            notebook#set_page ~tab_label:(new_tab_lbl "Error") frame#coerce;
	    Coq.return ()
          | Interface.Good res ->
            result#buffer#insert res; 
            notebook#set_page ~tab_label:(new_tab_lbl arg) frame#coerce;
	    Coq.return ())
      in
      result#buffer#set_text ("Result for command " ^ phrase ^ ":\n");
      Coq.try_grab coqtop process ignore
    in
    ignore (combo#entry#connect#activate ~callback);
    ignore (ok_b#connect#clicked ~callback);
    begin match command with
      | None -> ()
      | Some c -> combo#entry#set_text c
    end;
    begin match term with
      | None -> ()
      | Some t -> entry#set_text t
    end;
    combo#entry#misc#grab_focus ();
    if grab_now then entry#misc#grab_default ();
    ignore (entry#connect#activate ~callback);
    ignore (combo#entry#connect#activate ~callback);
    ignore (combo#entry#event#connect#key_press ~callback:(fun ev ->
      if GdkEvent.Key.keyval ev = GdkKeysyms._Tab then
        (entry#misc#grab_focus ();true)
      else false))

  method show =
    frame#show;
    let cur_page = notebook#get_nth_page notebook#current_page in
    let _, _, e =
      List.find (fun (p,_,_) -> p#get_oid == cur_page#get_oid) views in
    e#misc#grab_focus ()

  method hide =
    frame#hide

  method visible =
    frame#visible
  
  method refresh_font () =
    let iter (_,view,_) = view#misc#modify_font current.text_font in
    List.iter iter views

  method refresh_color () =
    let clr = Tags.color_of_string current.background_color in
    let iter (_,view,_) = view#misc#modify_base [`NORMAL, `COLOR clr] in
    List.iter iter views

  initializer
    self#new_page_maker;
    self#new_query_aux ~grab_now:false ();
    frame#misc#hide ();
    ignore(notebook#event#connect#key_press ~callback:(fun ev ->
      if GdkEvent.Key.keyval ev = GdkKeysyms._Escape then (self#hide; true)
      else false
    ));

end
