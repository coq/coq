(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Preferences

class command_window name coqtop coqops router =
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

  let route_id =
    let r = ref 0 in
    fun () -> incr r; !r in

object(self)
  val frame = frame

  val notebook = notebook

  (* We need access to coqops in order to place queries in the proper
     document stint. This should remove access from this module to the
     low-level Coq one. *)
  val coqops = coqops

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
    let route_id = route_id () in
    let new_tab_lbl text =
      let hbox = GPack.hbox ~homogeneous:false () in
      ignore(GMisc.label ~width:100 ~ellipsize:`END ~text ~packing:hbox#pack());
      let b = GButton.button ~packing:hbox#pack () in
      ignore(b#connect#clicked ~callback:(fun () ->
        router#delete_route route_id;
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
    let result = Wg_MessageView.message_view () in
    router#register_route route_id result;
    r_bin#add_with_viewport (result :> GObj.widget);
    views <- (frame#coerce, result, combo#entry) :: views;
    let cb clr = result#misc#modify_base [`NORMAL, `NAME clr] in
    let _ = background_color#connect#changed ~callback:cb in
    let _ = result#misc#connect#realize ~callback:(fun () -> cb background_color#get) in
    let cb ft = result#misc#modify_font (Pango.Font.from_string ft) in
    stick text_font result cb;
    result#misc#set_can_focus true; (* false causes problems for selection *)
    let callback () =
      let com = combo#entry#text in
      let arg = entry#text in
      if Str.string_match (Str.regexp "^ *$") (com^arg) 0 then () else
      let phrase =
        if Str.string_match (Str.regexp "\\. *$") com 0 then com
        else com ^ " " ^ arg ^" . "
      in
      let process =
        let next = function
        | Interface.Fail (_, _, err) ->
            let err = Ideutils.validate err in
            result#set err;
            notebook#set_page ~tab_label:(new_tab_lbl "Error") frame#coerce;
            Coq.return ()
        | Interface.Good () ->
            notebook#set_page ~tab_label:(new_tab_lbl arg) frame#coerce;
            Coq.return ()
        in
        coqops#raw_coq_query ~route_id ~next phrase
      in
      result#set (Pp.str ("Result for command " ^ phrase ^ ":\n"));
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
    match List.find (fun (p,_,_) -> p#get_oid == cur_page#get_oid) views with
    | (_, _, e) -> e#misc#grab_focus ()
    | exception Not_found -> ()

  method hide =
    frame#hide

  method visible =
    frame#visible

  method private refresh_color clr =
    let clr = Tags.color_of_string clr in
    let iter (_,view,_) = view#misc#modify_base [`NORMAL, `COLOR clr] in
    List.iter iter views

  initializer
    self#new_page_maker;
    self#new_query_aux ~grab_now:false ();
    frame#misc#hide ();
    let _ = background_color#connect#changed ~callback:self#refresh_color in
    self#refresh_color background_color#get;
    ignore(notebook#event#connect#key_press ~callback:(fun ev ->
      if GdkEvent.Key.keyval ev = GdkKeysyms._Escape then (self#hide; true)
      else false
    ));

end
