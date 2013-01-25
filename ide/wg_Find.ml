(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

type mode = [ `FIND | `REPLACE ]

class finder (view : GText.view) =

  let widget = GPack.vbox () in
  (* Find part *)
  let find_box = GPack.hbox ~packing:widget#add () in
  let _ =
    GMisc.label ~text:"Find:"
      ~xalign:1.0
      ~packing:find_box#pack ()
  in
  let find_entry = GEdit.entry
    ~editable:true
    ~packing:(find_box#pack ~expand:true)
    ()
  in
  let next_button =
    GButton.button
      ~label:"_Next"
      ~use_mnemonic:true
(*       ~stock:`GO_DOWN *)
      ~packing:find_box#pack
      ()
  in
  let previous_button =
    GButton.button
      ~label:"_Previous"
      ~use_mnemonic:true
(*       ~stock:`GO_UP *)
      ~packing:find_box#pack
      ()
  in
  (* Find and replace part *)
  let replace_box = GPack.table
    ~columns:4 ~rows:2
    ~homogeneous:false ~packing:widget#add () in
  let _ =
    GMisc.label ~text:"Find:"
      ~xalign:1.0
      ~packing:(replace_box#attach ~left:0 ~top:0 ~fill:`X) ()
  in
  let _ =
    GMisc.label ~text:"Replace:"
      ~xalign:1.0
      ~packing:(replace_box#attach ~left:0 ~top:1 ~fill:`X) ()
  in
  let r_find_entry = GEdit.entry
    ~editable:true
    ~packing:(replace_box#attach ~left:1 ~top:0 ~expand:`X ~fill:`X)
    ()
  in
  let r_replace_entry = GEdit.entry
    ~editable:true
    ~packing:(replace_box#attach ~left:1 ~top:1 ~expand:`X ~fill:`X)
    ()
  in
  let r_next_button =
    GButton.button
      ~label:"_Next" ~use_mnemonic:true
      ~packing:(replace_box#attach ~left:2 ~top:0)
      ()
  in
  let r_previous_button =
    GButton.button
      ~label:"_Previous" ~use_mnemonic:true
      ~packing:(replace_box#attach ~left:3 ~top:0)
      ()
  in
  let r_replace_button =
    GButton.button
      ~label:"_Replace" ~use_mnemonic:true
      ~packing:(replace_box#attach ~left:2 ~top:1)
      ()
  in
  let r_replace_all_button =
    GButton.button
      ~label:"Replace _All" ~use_mnemonic:true
      ~packing:(replace_box#attach ~left:3 ~top:1)
      ()
  in

  object (self)
    val mutable last_found = None
    val mutable mode : mode = `FIND

    method coerce = widget#coerce

    method private get_selected_word () =
      let start = view#buffer#get_iter `INSERT in
      let stop = view#buffer#get_iter `SEL_BOUND in
      view#buffer#get_text ~start ~stop ()

    method private may_replace () =
      let search = self#search_text in
      (search <> "") && (search = self#get_selected_word ())

    method replace () =
      if self#may_replace () then
        let _ = view#buffer#delete_selection () in
        let _ = view#buffer#insert_interactive r_replace_entry#text in
        self#find_forward ()
      else self#find_forward ()

    method replace_all () =
      let rec replace_at (iter : GText.iter) =
        let found = iter#forward_search self#search_text in
        match found with
        | None -> ()
        | Some (start, stop) ->
          let start_mark = view#buffer#create_mark start in
          let stop_mark = view#buffer#create_mark ~left_gravity:false stop in
          let _ = view#buffer#delete_interactive ~start ~stop () in
          let iter = view#buffer#get_iter_at_mark (`MARK start_mark) in
          let _ = view#buffer#insert_interactive ~iter r_replace_entry#text in
          let next = view#buffer#get_iter_at_mark (`MARK stop_mark) in
          let () = view#buffer#delete_mark (`MARK start_mark) in
          let () = view#buffer#delete_mark (`MARK stop_mark) in
          replace_at next
      in
      replace_at view#buffer#start_iter

    method private set_not_found () =
      find_entry#misc#modify_base [`NORMAL, `NAME "#F7E6E6"];
      r_find_entry#misc#modify_base [`NORMAL, `NAME "#F7E6E6"];

    method private set_found () =
      find_entry#misc#modify_base [`NORMAL, `NAME "#BAF9CE"];
      r_find_entry#misc#modify_base [`NORMAL, `NAME "#BAF9CE"]

    method private set_normal () =
      find_entry#misc#modify_base [`NORMAL, `NAME "white"];
      r_find_entry#misc#modify_base [`NORMAL, `NAME "white"]

    method private find_from backward (starti : GText.iter) text =
      let found =
        if backward then
          starti#backward_search text
        else
          starti#forward_search text
      in
      match found with
      | None ->
        if not backward && not (starti#equal view#buffer#start_iter) then
          self#find_from backward view#buffer#start_iter text
        else if backward && not (starti#equal view#buffer#end_iter) then
          self#find_from backward view#buffer#end_iter text
        else
          self#set_not_found ()
      | Some (start, stop) ->
        let _ = view#buffer#select_range start stop in
        let scroll = `MARK (view#buffer#create_mark stop) in
        let _ = view#scroll_to_mark ~use_align:false scroll in
        self#set_found ()

    method find_forward () =
      let starti = view#buffer#get_iter `SEL_BOUND in
      self#find_from false starti self#search_text

    method find_backward () =
      let starti = view#buffer#get_iter `INSERT in
      self#find_from true starti self#search_text

    method private search_text = match mode with
    | `FIND -> find_entry#text
    | `REPLACE -> r_find_entry#text

    method hide () =
      widget#misc#hide ();
      view#coerce#misc#grab_focus ()

    method show (mode : mode) = match mode with
    | `FIND -> self#show_find ()
    | `REPLACE -> self#show_replace ()

    method private show_find () =
      mode <- `FIND;
      let search =
        if self#coerce#misc#visible then
          r_find_entry#text
        else
          self#get_selected_word ()
      in
      self#set_normal ();
      find_entry#set_text search;
      widget#misc#show ();
      find_box#misc#show ();
      replace_box#misc#hide ();
      find_entry#misc#grab_focus ()

    method private show_replace () =
      mode <- `REPLACE;
      let search =
        if self#coerce#misc#visible then
          find_entry#text
        else
          self#get_selected_word ()
      in
      self#set_normal ();
      r_find_entry#set_text search;
      widget#misc#show ();
      find_box#misc#hide ();
      replace_box#misc#show ();
      r_find_entry#misc#grab_focus ()

    initializer
      let _ = self#hide () in
      let _ = next_button#connect#clicked ~callback:self#find_forward in
      let _ = previous_button#connect#clicked ~callback:self#find_backward in
      let _ = r_next_button#connect#clicked ~callback:self#find_forward in
      let _ = r_previous_button#connect#clicked ~callback:self#find_backward in
      let _ = r_replace_button#connect#clicked ~callback:self#replace in
      let _ = r_replace_all_button#connect#clicked ~callback:self#replace_all in
      let find_cb ev =
        let ev_key = GdkEvent.Key.keyval ev in
        let (key, _) = GtkData.AccelGroup.parse "Return" in
        let () = Printf.printf "%i %i\n%!" ev_key key in
        if ev_key = key then (self#find_forward (); true)
        else false
      in
      let _ = find_entry#event#connect#key_press find_cb in
      ()

  end

class info (coqtop : Coq.coqtop) (view : GText.view) (msg_view : Wg_MessageView.message_view) =

  let widget = GPack.vbox () in
  (* SearchAbout part *)
  let query_box = GPack.hbox ~packing:widget#add () in
  let _ =
    GMisc.label ~text:"SearchAbout:"
      ~xalign:1.0
      ~packing:query_box#pack ()
  in
  let find_entry = GEdit.entry
    ~editable:true
    ~packing:(query_box#pack ~expand:true)
    ()
  in
  let next_button =
    GButton.button
      ~label:"_Go"
      ~use_mnemonic:true
(*       ~stock:`GO_DOWN *)
      ~packing:query_box#pack
      ()
  in


  object (self)
    method coerce = widget#coerce

    method private get_selected_word () =
      let start = view#buffer#get_iter `INSERT in
      let stop = view#buffer#get_iter `SEL_BOUND in
      view#buffer#get_text ~start ~stop ()

    method hide () =
      widget#misc#hide ();
      view#coerce#misc#grab_focus ()

    method show () =
      let search =
        if self#coerce#misc#visible then find_entry#text
        else
          self#get_selected_word ()
      in
      find_entry#set_text search;
      widget#misc#show ()

    method private search () =
      let search = find_entry#text in
      let len = String.length search in
      ignore len

    initializer
      let _ = self#hide () in
      let _ = next_button#connect#clicked ~callback:self#search in
      ()

  end
