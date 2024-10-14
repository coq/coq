(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

let b2c = Ideutils.byte_offset_to_char_offset

class finder name (view : GText.view) =

  let widget = Wg_Detachable.detachable
    ~title:(Printf.sprintf "Find & Replace (%s)" name) () in
  let replace_box = GPack.grid ~col_homogeneous:false ~row_homogeneous:false
    ~row_spacings:2 ~col_spacings:2 ~packing:widget#add () in
  let () = replace_box#set_margin 2 in
  let hb = GPack.hbox ~packing:(replace_box#attach ~left:1 ~top:0) () in
  let use_regex =
    GButton.check_button ~label:"Regular expression"
      ~packing:(hb#pack ~expand:false ~fill:true ~padding:3) () in
  let use_nocase =
    GButton.check_button ~label:"Case insensitive"
      ~packing:(hb#pack ~expand:false ~fill:true ~padding:3) () in
  let find_label = GMisc.label ~text:"Find:"
    ~packing:(replace_box#attach ~left:0 ~top:1) () in
  let replace_label = GMisc.label ~text:"Replace with:"
    ~packing:(replace_box#attach ~left:0 ~top:2) () in
  let () = List.iter (fun label ->
      label#set_halign `START;
      label#set_margin_left 2;
      label#set_margin_right 2;
    ) [find_label; replace_label] in
  let find_entry = GEdit.entry ~editable:true
    ~packing:(replace_box#attach ~left:1 ~top:1) () in
  let replace_entry = GEdit.entry ~editable:true
    ~packing:(replace_box#attach ~left:1 ~top:2) () in
  let next_button = GButton.button ~label:"_Next" ~use_mnemonic:true
    ~packing:(replace_box#attach ~left:2 ~top:1) () in
  let previous_button = GButton.button ~label:"_Previous" ~use_mnemonic:true
    ~packing:(replace_box#attach ~left:3 ~top:1) () in
  let replace_button = GButton.button ~label:"_Replace" ~use_mnemonic:true
    ~packing:(replace_box#attach ~left:2 ~top:2) () in
  let replace_all_button =
    GButton.button ~label:"Replace _All" ~use_mnemonic:true
      ~packing:(replace_box#attach ~left:3 ~top:2) () in

  object (self)
    val mutable last_found = None

    method coerce = widget#coerce

    method private get_selected_word () =
      let start = view#buffer#get_iter `INSERT in
      let stop = view#buffer#get_iter `SEL_BOUND in
      view#buffer#get_text ~start ~stop ()

    method private may_replace () =
      (self#search_text <> "") &&
      (Str.string_match self#regex (self#get_selected_word ()) 0)

    method replace () =
      if self#may_replace () then begin
        let txt = self#get_selected_word () in
        let () = view#buffer#begin_user_action () in
        let _ = view#buffer#delete_selection () in
        let _ = view#buffer#insert_interactive (self#replacement txt) in
        let () = view#buffer#end_user_action () in
        self#find_forward ()
      end

    method private regex =
      let rex = self#search_text in
      if use_regex#active then
        if use_nocase#active then Str.regexp_case_fold rex
        else Str.regexp rex
      else
        if use_nocase#active then Str.regexp_string_case_fold rex
        else Str.regexp_string rex

    method private replacement txt =
      if use_regex#active then Str.replace_matched replace_entry#text txt
      else replace_entry#text

    method private backward_search starti =
      let text = view#buffer#start_iter#get_text ~stop:starti in
      let regexp = self#regex in
      let offs = (String.length text - 1) in
      if offs < 0 then None
      else try
        let i = Str.search_backward regexp text offs in
        let j = Str.match_end () in
        Some(view#buffer#start_iter#forward_chars (b2c text i),
             view#buffer#start_iter#forward_chars (b2c text j))
      with Not_found -> None

    method private forward_search starti =
      let text = starti#get_text ~stop:view#buffer#end_iter in
      let regexp = self#regex in
      try
        let i = Str.search_forward regexp text 0 in
        let j = Str.match_end () in
        Some(starti#forward_chars (b2c text i), starti#forward_chars (b2c text j))
      with Not_found -> None

    method replace_all () =
      let rec replace_at (iter : GText.iter) ct tot =
        let found = self#forward_search iter in
        match found with
        | None ->
           let tot_str = if Int.equal ct tot then "" else " of " ^ string_of_int tot in
           let occ_str = CString.plural tot "occurrence" in
           let _ = Ideutils.flash_info ("Replaced " ^ string_of_int ct ^ tot_str ^ " " ^ occ_str) in
           ()
        | Some (start, stop) ->
          let text = iter#get_text ~stop:view#buffer#end_iter in
          let start_mark = view#buffer#create_mark start in
          let stop_mark = view#buffer#create_mark ~left_gravity:false stop in
          let mod_save = view#buffer#modified in
          let _ = view#buffer#set_modified false in
          let _ = view#buffer#delete_interactive ~start ~stop () in
          let iter = view#buffer#get_iter_at_mark (`MARK start_mark) in
          let _ = view#buffer#insert_interactive ~iter (self#replacement text) in
          let edited = view#buffer#modified in
          let _ = view#buffer#set_modified (edited || mod_save) in
          let next = view#buffer#get_iter_at_mark (`MARK stop_mark) in
          let () = view#buffer#delete_mark (`MARK start_mark) in
          let () = view#buffer#delete_mark (`MARK stop_mark) in
          let next_ct = if edited then ct + 1 else ct in
          replace_at next next_ct (tot + 1)
      in
      if self#search_text <> "" then begin
        let () = view#buffer#begin_user_action () in
        let () = replace_at view#buffer#start_iter 0 0 in
        view#buffer#end_user_action ()
      end

    method private set_not_found () =
      find_entry#set_secondary_icon_stock `DELETE;
      find_entry#set_secondary_icon_tooltip_text "String not found";

    method private set_found () =
      find_entry#set_secondary_icon_stock `FIND;
      find_entry#set_secondary_icon_tooltip_text "String found";

    method private set_normal () =
      find_entry#set_secondary_icon_stock (`STOCK "");
      find_entry#set_secondary_icon_tooltip_text "";

    method private find_from backward ?(wrapped=false) (starti : GText.iter) =
      let found =
        if backward then self#backward_search starti
        else self#forward_search starti in
      match found with
      | None ->
        if not backward && not (starti#equal view#buffer#start_iter) then
          self#find_from backward ~wrapped:true view#buffer#start_iter
        else if backward && not (starti#equal view#buffer#end_iter) then
          self#find_from backward ~wrapped:true view#buffer#end_iter
        else
          let _ = Ideutils.flash_info "String not found" in
          self#set_not_found ()
      | Some (start, stop) ->
        let _ = view#buffer#select_range start stop in
        let scroll = `MARK (view#buffer#create_mark stop) in
        let _ = view#scroll_to_mark ~use_align:false scroll in
        self#set_found ()

    method find_forward () =
      let starti = view#buffer#get_iter `SEL_BOUND in
      self#find_from false starti

    method find_backward () =
      let starti = view#buffer#get_iter `INSERT in
      self#find_from true starti

    method private search_text = find_entry#text

    method hide () =
      widget#hide;
      self#set_normal ();
      view#coerce#misc#grab_focus ()

    method show () =
      widget#show;
      find_entry#misc#grab_focus ()

    initializer
      let _ = self#hide () in

      (* Widget button interaction *)
      let _ = next_button#connect#clicked ~callback:self#find_forward in
      let _ = previous_button#connect#clicked ~callback:self#find_backward in
      let _ = replace_button#connect#clicked ~callback:self#replace in
      let _ = replace_all_button#connect#clicked ~callback:self#replace_all in

      (* Keypress interaction *)
      let dispatch_key_cb esc_cb ret_cb shift_ret_cb ev =
        let ev_key = GdkEvent.Key.keyval ev in
        let ev_modifiers = GdkEvent.Key.state ev in
        if ev_key = GdkKeysyms._Return then
          (if List.mem `SHIFT ev_modifiers then
            shift_ret_cb ()
          else ret_cb (); true)
        else if ev_key = GdkKeysyms._Escape then (esc_cb (); true)
        else false
      in
      let find_cb = dispatch_key_cb self#hide self#find_forward self#find_backward in
      let replace_cb = dispatch_key_cb self#hide self#replace self#replace in
      let _ = find_entry#event#connect#key_press ~callback:find_cb in
      let _ = replace_entry#event#connect#key_press ~callback:replace_cb in

      (* TextView interaction *)
      let view_cb ev =
        if widget#visible then
          let ev_key = GdkEvent.Key.keyval ev in
          if ev_key = GdkKeysyms._Escape then (widget#hide; true)
          else false
        else false
      in
      let _ = view#event#connect#key_press ~callback:view_cb in
      ()

  end
