(***********************************************************************)
(*                          Configwin                                  *)
(*                                                                     *)
(*            Maxence Guesdon, projet Cristal, INRIA Rocquencourt      *)
(*                                                                     *)
(*  Copyright 2001 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

(** This module contains the gui functions of Confgiwin.*)

open Configwin_types

module O = Uoptions


(** The file where the html config is. *)
let file_html_config = Filename.concat Configwin_messages.home ".configwin_html"
  
(** Return the ini file for the html config, and the option for bindings. *)
let html_config_file_and_option () =
  let ini = O.create_options_file file_html_config in
  let bindings = O.define_option ini ["bindings"]
      ""
      (O.list_option Configwin_types.Html_binding.t)
      [ { html_key = KeyOption.string_to_key "A-b" ;
	  html_begin = "<b>";
	  html_end = "</b>" ;
	} ;
	{ html_key = KeyOption.string_to_key "A-i" ;
	  html_begin = "<i>";
	  html_end = "</i>" ;
	} 
      ]	
  in
  O.load ini ;
  (ini, bindings)


(** This variable contains the last directory where the user selected a file.*)
let last_dir = ref "";;

(** This function allows the user to select a file and returns the
   selected file name. An optional function allows to change the 
   behaviour of the ok button.
   A VOIR : mutli-selection ? *)
let select_files ?dir
    ?(fok : (string -> unit) option)
    the_title =
  let files = ref ([] : string list) in 
  let fs = GWindow.file_selection ~modal:true
      ~title: the_title () in
  (* we set the previous directory, if no directory is given *)
  (
   match dir with
     None ->
       if !last_dir <> "" then
         let _ = fs#set_filename !last_dir in
         ()
       else
         ()
  | Some dir ->
      let _ = fs#set_filename !last_dir in
      ()
  );
 
  let _ = fs # connect#destroy ~callback: GMain.Main.quit in
  let _ = fs # ok_button # connect#clicked ~callback:
      (match fok with
        None ->
          (fun () -> files := [fs#get_filename] ; fs#destroy ())
      | Some f ->
          (fun () -> f fs#get_filename)
      )
  in
  let _ = fs # cancel_button # connect#clicked ~callback:fs#destroy in
  fs # show ();
  GMain.Main.main ();
  match !files with
  | [] ->
      []
  | [""] ->
      []
  | l ->
      (* we keep the directory in last_dir *)
      last_dir := Filename.dirname (List.hd l);
      l
;;

(** Make the user select a date. *)
let select_date title (day,mon,year) =
  let v_opt = ref None in
  let window = GWindow.dialog ~modal:true ~title () in
  let hbox = GPack.hbox ~border_width:10 ~packing:window#vbox#add () in
  let cal = GMisc.calendar ~packing: (hbox#pack ~expand: true) () in
  cal#select_month ~month: mon ~year: year ;
  cal#select_day day;
  let bbox = window#action_area in

  let bok = GButton.button ~label: Configwin_messages.mOk
      ~packing:(bbox#pack ~expand:true ~padding:4) ()
  in
  let bcancel = GButton.button ~label: Configwin_messages.mCancel
      ~packing:(bbox#pack ~expand:true ~padding:4) ()
  in
  ignore (bok#connect#clicked ~callback:
	    (fun () -> v_opt := Some (cal#date); window#destroy ()));
  ignore(bcancel#connect#clicked ~callback: window#destroy);

  bok#grab_default ();
  ignore(window#connect#destroy ~callback: GMain.Main.quit);
  window#set_position `CENTER;
  window#show ();
  GMain.Main.main ();
  !v_opt


(** This class builds a frame with a clist and two buttons :
   one to add items and one to remove the selected items.
   The class takes in parameter a function used to add items and
   a string list ref which is used to store the content of the clist.
   At last, a title for the frame  is also in parameter, so that     
   each instance of the class creates a frame. *)
class ['a] list_selection_box (listref : 'a list ref) 
    titles_opt
    help_opt
    f_edit_opt
    f_strings
    f_color
    (eq : 'a -> 'a -> bool)
    add_function title editable =
  let wev = GBin.event_box () in
  let wf = GBin.frame ~label: title ~packing: wev#add () in
  let hbox = GPack.hbox ~packing: wf#add () in
  (* the scroll window and the clist *)
  let wscroll = GBin.scrolled_window
      	~vpolicy: `AUTOMATIC
	~hpolicy: `AUTOMATIC
      ~packing: (hbox#pack ~expand: true) () 
  in
  let wlist = match titles_opt with
    None -> 
      GList.clist ~selection_mode: `MULTIPLE
	~titles_show: false
	~packing: wscroll#add ()
  | Some l -> 
      GList.clist ~selection_mode: `MULTIPLE 
	~titles: l
	~titles_show: true
	~packing: wscroll#add ()
  in
  let _ = 
    match help_opt with
      None -> ()
    | Some help ->
	let tooltips = GData.tooltips () in
	ignore (wf#connect#destroy ~callback: tooltips#destroy);
	tooltips#set_tip wev#coerce ~text: help ~privat: help 
  in  (* the vbox for the buttons *)
  let vbox_buttons = GPack.vbox () in
  let _ = 
    if editable then
      let _ = hbox#pack ~expand: false vbox_buttons#coerce in
      ()
    else
      () 
  in
  let wb_add = GButton.button
      ~label: Configwin_messages.mAdd
      ~packing: (vbox_buttons#pack ~expand:false ~padding:2)
      ()
  in
  let wb_edit = GButton.button
      ~label: Configwin_messages.mEdit
      ()
  in
  let _ = match f_edit_opt with
    None -> ()
  | Some _ -> vbox_buttons#pack ~expand:false ~padding:2 wb_edit#coerce
  in
  let wb_up = GButton.button
      ~label: Configwin_messages.mUp
      ~packing: (vbox_buttons#pack ~expand:false ~padding:2)
      ()
  in
  let wb_remove = GButton.button
      ~label: Configwin_messages.mRemove
      ~packing: (vbox_buttons#pack ~expand:false ~padding:2)
      ()
  in
  object (self)
    (** the list of selected rows *)
    val mutable list_select = []

    (** This method returns the frame created. *)
    method box = wev

    method update l =
      (* set the new list in the provided listref *)
      listref := l;
      (* insert the elements in the clist *)
      wlist#freeze ();
      wlist#clear ();
      List.iter 
	(fun ele -> 
	  ignore (wlist#append (f_strings ele));
	  match f_color ele with
	    None -> ()
	  | Some c ->
	      try wlist#set_row ~foreground: (`NAME c) (wlist#rows - 1)
	      with _ -> ()
	) 
	!listref;
      
      (match titles_opt with
	None -> wlist#columns_autosize ()
      |	Some _ -> GToolbox.autosize_clist wlist);
      wlist#thaw ();
      (* the list of selectd elements is now empty *)
      list_select <- []

    (** Move up the selected rows. *)
    method up_selected =
      let rec iter n selrows l =
	match selrows with
	  [] -> (l, [])
	| m :: qrows ->
	    match l with
	      [] -> ([],[])
	    | [_] -> (l,[])
	    | e1 :: e2 :: q when m = n + 1 ->
		let newl, newrows = iter (n+1) qrows (e1 :: q) in
		(e2 :: newl, n :: newrows)
	    | e1 :: q ->
		let newl, newrows = iter (n+1) selrows q in
		(e1 ::  newl, newrows)
      in
      let sorted_select = List.sort compare list_select in
      let new_list, new_rows = iter 0 sorted_select !listref in
      self#update new_list;
      List.iter (fun n -> wlist#select n 0) new_rows

    (** Make the user edit the first selected row. *)
    method edit_selected f_edit =
      let sorted_select = List.sort compare list_select in
      match sorted_select with
	[] -> ()
      |	n :: _ ->
	  try
	    let ele = List.nth !listref n in
	    let ele2 = f_edit ele in
	    let rec iter m = function
		[] -> []
	      |	e :: q ->
		  if n = m then
		    ele2 :: q
		  else
		    e :: (iter (m+1) q)
	    in
	    self#update (iter 0 !listref);
	    wlist#select n 0
	  with
	    Not_found ->
	      ()

    initializer
      (** create the functions called when the buttons are clicked *)
      let f_add () = 
        (* get the files to add with the function provided *)
        let l = add_function () in
        (* remove from the list the ones which are already in 
           the listref, using the eq predicate *)
        let l2 = List.fold_left
            (fun acc -> fun ele ->
              if List.exists (eq ele) acc then
                acc
              else
                acc @ [ele])
            !listref
            l
        in    
        self#update l2
      in
      let f_remove () =
        (* remove the selected items from the listref and the clist *)
	let rec iter n = function
	    [] -> []
	  | h :: q ->
	      if List.mem n list_select then
		iter (n+1) q
	      else
		h :: (iter (n+1) q)
	in
        let new_list = iter 0 !listref in
        self#update new_list
      in
      (* connect the functions to the buttons *)
      ignore (wb_add#connect#clicked f_add);
      ignore (wb_remove#connect#clicked f_remove);
      ignore (wb_up#connect#clicked (fun () -> self#up_selected));
      (
       match f_edit_opt with
	 None -> ()
       | Some f -> ignore (wb_edit#connect#clicked (fun () -> self#edit_selected f))
      );
      (* connect the selection and deselection of items in the clist *)
      let f_select ~row ~column ~event =
        try
          list_select <- row :: list_select
        with
          Failure _ ->
            ()
      in
      let f_unselect ~row ~column ~event =
        try
          let new_list_select = List.filter (fun n -> n <> row) list_select in
          list_select <- new_list_select
        with
          Failure _ ->
            ()
      in
      (* connect the select and deselect events *)
      ignore(wlist#connect#select_row f_select);
      ignore(wlist#connect#unselect_row f_unselect);

      (* initialize the clist with the listref *)
      self#update !listref
  end;;


(** This class is used to build a box for a string parameter.*)
class string_param_box param =
  let hbox = GPack.hbox () in
  let wev = GBin.event_box ~packing: (hbox#pack ~expand: false ~padding: 2) () in
  let wl = GMisc.label ~text: param.string_label ~packing: wev#add () in
  let we = GEdit.entry
      ~editable: param.string_editable
      ~packing: (hbox#pack ~expand: param.string_expand ~padding: 2)
      ()
  in
  let _ = 
    match param.string_help with
      None -> ()
    | Some help ->
	let tooltips = GData.tooltips () in
	ignore (hbox#connect#destroy ~callback: tooltips#destroy);
	tooltips#set_tip wev#coerce ~text: help ~privat: help 
  in
  let _ = we#set_text param.string_value in

  object (self)
    (** This method returns the main box ready to be packed. *)
    method box = hbox#coerce
    (** This method applies the new value of the parameter. *)
    method apply =
      let new_value = we#text in
      if new_value <> param.string_value then
	let _ = param.string_f_apply new_value in
	param.string_value <- new_value
      else
	()
  end ;;

(** This class is used to build a box for a combo parameter.*)
class combo_param_box param =
  let hbox = GPack.hbox () in
  let wev = GBin.event_box ~packing: (hbox#pack ~expand: false ~padding: 2) () in
  let wl = GMisc.label ~text: param.combo_label ~packing: wev#add () in
  let wc = GEdit.combo
      ~popdown_strings: param.combo_choices
      ~value_in_list: (not param.combo_new_allowed)
      ~ok_if_empty: param.combo_blank_allowed
      ~packing: (hbox#pack ~expand: param.combo_expand ~padding: 2)
      ()
  in
  let _ = 
    match param.combo_help with
      None -> ()
    | Some help ->
	let tooltips = GData.tooltips () in
	ignore (hbox#connect#destroy ~callback: tooltips#destroy);
	tooltips#set_tip wev#coerce ~text: help ~privat: help 
  in
  let _ = wc#entry#set_editable param.combo_editable in
  let _ = wc#entry#set_text param.combo_value in

  object (self)
    (** This method returns the main box ready to be packed. *)
    method box = hbox#coerce
    (** This method applies the new value of the parameter. *)
    method apply =
      let new_value = wc#entry#text in
      if new_value <> param.combo_value then
	let _ = param.combo_f_apply new_value in
	param.combo_value <- new_value
      else
	()
  end ;;

(** Class used to pack a custom box. *)
class custom_param_box param =
  let top = 
    match param.custom_framed with
      None -> param.custom_box#coerce
    | Some l ->
	let wf = GBin.frame ~label: l () in
	wf#add param.custom_box#coerce;
	wf#coerce
  in
  object (self)
    method box = top
    method apply = param.custom_f_apply ()
  end

(** This class is used to build a box for a color parameter.*)
class color_param_box param =
  let v = ref param.color_value in
  let hbox = GPack.hbox () in
  let wb = GButton.button ~label: param.color_label 
      ~packing: (hbox#pack ~expand: false ~padding: 2) () 
  in
  let w_test = GMisc.arrow 
      ~kind: `RIGHT
      ~shadow: `OUT
      ~width: 20
      ~height: 20
      ~packing: (hbox#pack ~expand: false ~padding: 2 )
      () 
  in
  let we = GEdit.entry
      ~editable: param.color_editable
      ~packing: (hbox#pack ~expand: param.color_expand ~padding: 2)
      ()
  in
  let _ = 
    match param.color_help with
      None -> ()
    | Some help ->
	let tooltips = GData.tooltips () in
	ignore (hbox#connect#destroy ~callback: tooltips#destroy);
	tooltips#set_tip wb#coerce ~text: help ~privat: help 
  in
  let set_color s =
    let style = w_test#misc#style#copy in
    (
     try style#set_bg [ (`NORMAL, `NAME s) ; ]
     with _ -> ()
    );
    w_test#misc#set_style style 
  in
  let _ = set_color !v in
  let _ = we#set_text !v in
  let f_sel () =
    let dialog = GWindow.color_selection_dialog
	~title: param.color_label
	~modal: true
	~show: true
	()
    in
    let wb_ok = dialog#ok_button in
    let wb_cancel = dialog#cancel_button in
    let _ = dialog#connect#destroy GMain.Main.quit in
    let _ = wb_ok#connect#clicked
	(fun () -> 
	  let color = dialog#colorsel#get_color in
	  let r = int_of_float (ceil (color.Gtk.red *. 255.)) in
	  let g = int_of_float (ceil (color.Gtk.green *. 255.)) in
	  let b = int_of_float (ceil (color.Gtk.blue *. 255.)) in
	  let s = Printf.sprintf "#%2X%2X%2X" r g b in
	  let _ = 
	    for i = 1 to (String.length s) - 1 do
	      if s.[i] = ' ' then s.[i] <- '0'
	    done
	  in
	  we#set_text s ;
	  set_color s;
	  dialog#destroy ()
	)
    in
    let _ = wb_cancel#connect#clicked dialog#destroy in
    GMain.Main.main ()
  in
  let _ = 
    if param.color_editable then ignore (wb#connect#clicked f_sel)
  in

  object (self)
    (** This method returns the main box ready to be packed. *)
    method box = hbox#coerce
    (** This method applies the new value of the parameter. *)
    method apply =
      let new_value = we#text in
      if new_value <> param.color_value then
	let _ = param.color_f_apply new_value in
	param.color_value <- new_value
      else
	()
  end ;;

(** This class is used to build a box for a font parameter.*)
class font_param_box param =
  let v = ref param.font_value in
  let hbox = GPack.hbox () in
  let wb = GButton.button ~label: param.font_label 
      ~packing: (hbox#pack ~expand: false ~padding: 2) () 
  in
  let we = GEdit.entry
      ~editable: false
      ~packing: (hbox#pack ~expand: param.font_expand ~padding: 2)
      ()
  in
  let _ = 
    match param.font_help with
      None -> ()
    | Some help ->
	let tooltips = GData.tooltips () in
	ignore (hbox#connect#destroy ~callback: tooltips#destroy);
	tooltips#set_tip wb#coerce ~text: help ~privat: help 
  in
  let set_entry_font font_opt =
    match font_opt with
      None -> ()
    | Some s ->
	let style = we#misc#style#copy in
	(
	 try 
	   let font = Gdk.Font.load_fontset s in
	   style#set_font font
	 with _ -> ()
	);
	we#misc#set_style style
  in
  let _ = set_entry_font (Some !v) in
  let _ = we#set_text !v in
  let f_sel () =
    let dialog = GWindow.font_selection_dialog
	~title: param.font_label
	~modal: true
	~show: true
	()
    in
    dialog#selection#set_font_name !v;
    let wb_ok = dialog#ok_button in
    let wb_cancel = dialog#cancel_button in
    let _ = dialog#connect#destroy GMain.Main.quit in
    let _ = wb_ok#connect#clicked
	(fun () -> 
	  let font_opt = dialog#selection#font_name in
	  we#set_text (match font_opt with None -> "" | Some s -> s) ;
	  set_entry_font font_opt;
	  dialog#destroy ()
	)
    in
    let _ = wb_cancel#connect#clicked dialog#destroy in
    GMain.Main.main ()
  in
  let _ = if param.font_editable then ignore (wb#connect#clicked f_sel) in

  object (self)
    (** This method returns the main box ready to be packed. *)
    method box = hbox#coerce
    (** This method applies the new value of the parameter. *)
    method apply =
      let new_value = we#text in
      if new_value <> param.font_value then
	let _ = param.font_f_apply new_value in
	param.font_value <- new_value
      else
	()
  end ;;

(** This class is used to build a box for a text parameter.*)
class text_param_box param =
  let hbox = GPack.hbox ~height: 100 () in
  let wev = GBin.event_box ~packing: (hbox#pack ~expand: false ~padding: 2) () in
  let wl = GMisc.label ~text: param.string_label ~packing: wev#add () in
  let wscroll = GBin.scrolled_window
      ~vpolicy: `AUTOMATIC
      ~hpolicy: `AUTOMATIC
      ~packing: (hbox#pack ~expand: true ~padding: 2) () 
  in
  let wt = GText.view ~packing:wscroll#add () in
  let _ = wt#coerce#misc#set_size_request ~height:100 in
  let _ = wt#set_editable param.string_editable in
  let _ = 
    match param.string_help with
      None -> ()
    | Some help ->
	let tooltips = GData.tooltips () in
	ignore (hbox#connect#destroy ~callback: tooltips#destroy);
	tooltips#set_tip wev#coerce ~text: help ~privat: help 
  in
  let _ = wt#buffer#insert param.string_value in

  object (self)
    val wt = wt
    (** This method returns the main box ready to be packed. *)
    method box = hbox#coerce
    (** This method applies the new value of the parameter. *)
    method apply =
      let new_value = wt#buffer#get_text () in
      if new_value <> param.string_value then
	let _ = param.string_f_apply new_value in
	param.string_value <- new_value
      else
	()
  end ;;

(** This class is used to build a box a html parameter. *)
class html_param_box param =
  object (self)
    inherit text_param_box param

    method private exec html_start html_end () =
      let s,e = wt#buffer#selection_bounds in
      if s#compare e = 0 then 
	wt#buffer#insert (html_start^html_end)
      else begin
	ignore (wt#buffer#insert ~iter:e html_end);
	ignore (wt#buffer#insert ~iter:s html_start);
	wt#buffer#place_cursor 
	  (e#forward_chars (String.length (html_start^html_end)))
      end
    initializer
      let (_,html_bindings) = html_config_file_and_option () in
      let add_shortcut hb =
	let (mods, k) = hb.html_key in
	Okey.add wt ~mods k (self#exec hb.html_begin hb.html_end)
      in
      List.iter add_shortcut (O.(!!) html_bindings)      
  end

(** This class is used to build a box for a boolean parameter.*)
class bool_param_box param =
  let wchk = GButton.check_button
      ~label: param.bool_label
      ()
  in
  let _ = 
    match param.bool_help with
      None -> ()
    | Some help ->
	let tooltips = GData.tooltips () in
	ignore (wchk#connect#destroy ~callback: tooltips#destroy);
	tooltips#set_tip wchk#coerce ~text: help ~privat: help 
  in
  let _ = wchk#set_active param.bool_value in
  let _ = wchk#misc#set_sensitive param.bool_editable in

  object (self)
    (** This method returns the check button ready to be packed. *)
    method box = wchk#coerce
    (** This method applies the new value of the parameter. *)
    method apply =
      let new_value = wchk#active in
      if new_value <> param.bool_value then
	let _ = param.bool_f_apply new_value in
	param.bool_value <- new_value
      else
	()
  end ;;

(** This class is used to build a box for a file name parameter.*)
class filename_param_box param =
  let hbox = GPack.hbox () in
  let wb = GButton.button ~label: param.string_label 
      ~packing: (hbox#pack ~expand: false ~padding: 2) () 
  in
  let we = GEdit.entry
      ~editable: param.string_editable
      ~packing: (hbox#pack ~expand: param.string_expand ~padding: 2)
      ()
  in
  let _ = 
    match param.string_help with
      None -> ()
    | Some help ->
	let tooltips = GData.tooltips () in
	ignore (hbox#connect#destroy ~callback: tooltips#destroy);
	tooltips#set_tip wb#coerce ~text: help ~privat: help 
  in
  let _ = we#set_text param.string_value in

  let f_click () =
    match select_files param.string_label with
      [] ->
        ()
    | f :: _ ->
        we#set_text f
  in
  let _ = 
    if param.string_editable then
      let _ = wb#connect#clicked f_click in
      ()
    else
      ()
  in

  object (self)
    (** This method returns the main box ready to be packed. *)
    method box = hbox#coerce
    (** This method applies the new value of the parameter. *)
    method apply =
      let new_value = we#text in
      if new_value <> param.string_value then
	let _ = param.string_f_apply new_value in
	param.string_value <- new_value
      else
	()
  end ;;

(** This class is used to build a box for a hot key parameter.*)
class hotkey_param_box param =
  let hbox = GPack.hbox () in
  let wev = GBin.event_box ~packing: (hbox#pack ~expand: false ~padding: 2) () in
  let wl = GMisc.label ~text: param.hk_label 
      ~packing: wev#add () 
  in
  let we = GEdit.entry
      ~editable: false
      ~packing: (hbox#pack ~expand: param.hk_expand ~padding: 2)
      ()
  in
  let value = ref param.hk_value in
  let _ = 
    match param.hk_help with
      None -> ()
    | Some help ->
	let tooltips = GData.tooltips () in
	ignore (hbox#connect#destroy ~callback: tooltips#destroy);
	tooltips#set_tip wev#coerce ~text: help ~privat: help 
  in
  let _ = we#set_text (KeyOption.key_to_string param.hk_value) in
  let mods_we_dont_care = [`MOD2 ; `MOD3 ; `MOD4 ; `MOD5 ; `LOCK] in
  let capture ev =
    let key = GdkEvent.Key.keyval ev in
    let modifiers = GdkEvent.Key.state ev in
    let mods = List.filter
	(fun m -> not (List.mem m mods_we_dont_care))
	modifiers
    in
    value := (mods, key);
    we#set_text (KeyOption.key_to_string !value);
    false
  in
  let _ = 
    if param.hk_editable then
      ignore (we#event#connect#key_press capture)
    else
      ()
  in

  object (self)
    (** This method returns the main box ready to be packed. *)
    method box = hbox#coerce
    (** This method applies the new value of the parameter. *)
    method apply =
      let new_value = !value in
      if new_value <> param.hk_value then
	let _ = param.hk_f_apply new_value in
	param.hk_value <- new_value
      else
	()
  end ;;

(** This class is used to build a box for a date parameter.*)
class date_param_box param =
  let v = ref param.date_value in
  let hbox = GPack.hbox () in
  let wb = GButton.button ~label: param.date_label 
      ~packing: (hbox#pack ~expand: false ~padding: 2) () 
  in
  let we = GEdit.entry
      ~editable: false
      ~packing: (hbox#pack ~expand: param.date_expand ~padding: 2)
      ()
  in
  let _ = 
    match param.date_help with
      None -> ()
    | Some help ->
	let tooltips = GData.tooltips () in
	ignore (hbox#connect#destroy ~callback: tooltips#destroy);
	tooltips#set_tip wb#coerce ~text: help ~privat: help 
  in
  let _ = we#set_text (param.date_f_string param.date_value) in

  let f_click () =
    match select_date param.date_label !v with
      None -> ()
    | Some (y,m,d) -> 
	v := (d,m,y) ;
	we#set_text (param.date_f_string (d,m,y))
  in
  let _ = 
    if param.date_editable then
      let _ = wb#connect#clicked f_click in
      ()
    else
      ()
  in

  object (self)
    (** This method returns the main box ready to be packed. *)
    method box = hbox#coerce
    (** This method applies the new value of the parameter. *)
    method apply =
      if !v <> param.date_value then
	let _ = param.date_f_apply !v in
	param.date_value <- !v
      else
	()
  end ;;

(** This class is used to build a box for a parameter whose values are a list.*)
class ['a] list_param_box (param : 'a list_param) =
  let listref = ref param.list_value in
  let frame_selection = new list_selection_box
      listref
      param.list_titles
      param.list_help
      param.list_f_edit
      param.list_strings
      param.list_color
      param.list_eq
      param.list_f_add param.list_label param.list_editable
  in
      
  object (self)
    (** This method returns the main box ready to be packed. *)
    method box = frame_selection#box#coerce
    (** This method applies the new value of the parameter. *)
    method apply =
      param.list_f_apply !listref ;
      param.list_value <- !listref
  end ;;

(** This class is used to build a box from a configuration structure 
   and adds the page to the given notebook. *)
class configuration_box conf_struct (notebook : GPack.notebook) =
  (* we build different widgets, according to the conf_struct parameter *)
  let main_box = GPack.vbox () in
  let (label, child_boxes) = 
    match conf_struct with
      Section (label, param_list) ->
	let f parameter =
	      match parameter with
		String_param p ->
		  let box = new string_param_box p in
		  let _ = main_box#pack ~expand: false ~padding: 2 box#box in
		  box
	      |	Combo_param p ->
		  let box = new combo_param_box p in
		  let _ = main_box#pack ~expand: false ~padding: 2 box#box in
		  box
	      |	Text_param p ->
		  let box = new text_param_box p in
		  let _ = main_box#pack ~expand: p.string_expand ~padding: 2 box#box in
		  box
	      | Bool_param p ->
		  let box = new bool_param_box p in
		  let _ = main_box#pack ~expand: false ~padding: 2 box#box in
		  box
	      |	Filename_param p ->
		  let box = new filename_param_box p in
		  let _ = main_box#pack ~expand: false ~padding: 2 box#box in
		  box
	      |	List_param f ->
		  let box = f () in
		  let _ = main_box#pack ~expand: true ~padding: 2 box#box in
		  box
	      |	Custom_param p ->
		  let box = new custom_param_box p in
		  let _ = main_box#pack ~expand: p.custom_expand ~padding: 2 box#box in
		  box
	      |	Color_param p ->
		  let box = new color_param_box p in
		  let _ = main_box#pack ~expand: false ~padding: 2 box#box in
		  box
	      |	Font_param p ->
		  let box = new font_param_box p in
		  let _ = main_box#pack ~expand: false ~padding: 2 box#box in
		  box
	      |	Date_param p ->
		  let box = new date_param_box p in
		  let _ = main_box#pack ~expand: false ~padding: 2 box#box in
		  box
	      |	Hotkey_param p ->
		  let box = new hotkey_param_box p in
		  let _ = main_box#pack ~expand: false ~padding: 2 box#box in
		  box
	      |	Html_param p ->
		  let box = new html_param_box p in
		  let _ = main_box#pack ~expand: p.string_expand ~padding: 2 box#box in
		  box
	in
	let list_children_boxes = List.map f param_list in
	
	(label, list_children_boxes)

    | Section_list (label, struct_list) ->
	let wnote = GPack.notebook 
            (*homogeneous_tabs: true*)
	    ~scrollable: true
	    ~show_tabs: true
	    ~tab_border: 3
	    ~packing: (main_box#pack ~expand: true)
	    ()
	in
	(* we create all the children boxes *)
	let f structure =
	  let new_box = new configuration_box structure wnote in
	  new_box
	in
	let list_child_boxes = List.map f struct_list in
	(label, list_child_boxes)
	
  in
  let page_label = GMisc.label ~text: label () in
  let _ = notebook#append_page 
      ~tab_label: page_label#coerce
      main_box#coerce
  in

  object (self)
    (** This method returns the main box ready to be packed. *)
    method box = main_box#coerce
    (** This method make the new values of the paramters applied, recursively in
       all boxes.*)
    method apply =
      List.iter (fun box -> box#apply) child_boxes
  end
;;

(** Create a vbox with the list of given configuration structure list,
   and the given list of buttons (defined by their label and callback).
   Before calling the callback of a button, the [apply] function
   of each parameter is called.
*)
let tabbed_box conf_struct_list buttons =
  let vbox = GPack.vbox () in
  let wnote = GPack.notebook 
      (*homogeneous_tabs: true*)
      ~scrollable: true
      ~show_tabs: true
      ~tab_border: 3
      ~packing: (vbox#pack ~expand: true)
      ()
  in
  let list_param_box = 
    List.map (fun conf_struct -> new configuration_box conf_struct wnote)
      conf_struct_list
  in
  let f_apply () = 
    List.iter (fun param_box -> param_box#apply) list_param_box  ;
  in
  let hbox_buttons = GPack.hbox ~packing: (vbox#pack ~expand: false ~padding: 4) () in
  let rec iter_buttons ?(grab=false) = function
      [] ->
        ()
    | (label, callb) :: q ->    
        let b = GButton.button ~label: label
            ~packing:(hbox_buttons#pack ~expand:true ~fill: true ~padding:4) ()
        in
        ignore (b#connect#clicked ~callback:
		  (fun () -> f_apply (); callb ()));
        (* If it's the first button then give it the focus *)
        if grab then b#grab_default ();

        iter_buttons q
  in
  iter_buttons ~grab: true buttons;

  vbox

(** This function takes a configuration structure list and creates a window
   to configure the various parameters. *)
let edit ?(with_apply=true)  
    ?(apply=(fun () -> ()))
    title ?(width=400) ?(height=400) 
    conf_struct_list =
  let return = ref Return_cancel in
  let window = GWindow.window
      ~modal: true ~title: title
      ~width: width ~height: height ()
  in
  let _ = window#connect#destroy ~callback: GMain.Main.quit in
  let vbox = GPack.vbox ~packing: window#add () in
  let wnote = GPack.notebook 
      (*homogeneous_tabs: true*)
      ~scrollable: true
      ~show_tabs: true
      ~tab_border: 3
      ~packing: (vbox#pack ~expand: true)
      ()
  in
  let list_param_box = 
    List.map (fun conf_struct -> new configuration_box conf_struct wnote)
      conf_struct_list
  in

  let hbox_buttons = GPack.hbox ~packing: (vbox#pack ~expand: false ~padding: 4) () in
  let bApply = GButton.button
      ~label: Configwin_messages.mApply
      ()
  in
  if with_apply then hbox_buttons#pack ~expand: true ~padding: 3 bApply#coerce;
  let bOk = GButton.button
      ~label: Configwin_messages.mOk
      ~packing: (hbox_buttons#pack ~expand: true ~padding: 3)
      ()
  in
  let bCancel = GButton.button
      ~label: Configwin_messages.mCancel
      ~packing: (hbox_buttons#pack ~expand: true ~padding: 3)
      ()
  in
  (* we connect the click on the apply button *)
  let f_apply () = 
    List.iter (fun param_box -> param_box#apply) list_param_box  ;
    apply ();
    return := Return_apply
  in
  let _ = bApply#connect#clicked f_apply in
  (* we connect the click on the ok button : the same than apply but we then close the window *)
  let f_ok () = 
    List.iter (fun param_box -> param_box#apply) list_param_box  ;
    return := Return_ok ;
    window#destroy () 
  in
  let _ = bOk#connect#clicked f_ok in
  (* we connect the click on the cancel button : close the window *)
  let f_cancel () = window#destroy () in
  let _ = bCancel#connect#clicked f_cancel in

  let _ = window#show () in
  GMain.Main.main () ;
  !return


(** Create a vbox with the list of given parameters,
   and the given list of buttons (defined by their label and callback).
   Before calling the callback of a button, the [apply] function
   of each parameter is called.
*)
let box param_list buttons =
  let main_box = GPack.vbox  () in
  let f parameter =
    match parameter with
      String_param p ->
	let box = new string_param_box p in
	let _ = main_box#pack ~expand: false ~padding: 2 box#box in
	box
    | Combo_param p ->
	let box = new combo_param_box p in
	let _ = main_box#pack ~expand: false ~padding: 2 box#box in
	box
    | Text_param p ->
	let box = new text_param_box p in
	let _ = main_box#pack ~expand: p.string_expand ~padding: 2 box#box in
	box
    | Bool_param p ->
	let box = new bool_param_box p in
	let _ = main_box#pack ~expand: false ~padding: 2 box#box in
	box
    | Filename_param p ->
	let box = new filename_param_box p in
	let _ = main_box#pack ~expand: false ~padding: 2 box#box in
	box
    | List_param f ->
	let box = f () in
	let _ = main_box#pack ~expand: true ~padding: 2 box#box in
	box
    | Custom_param p ->
	let box = new custom_param_box p in
	let _ = main_box#pack ~expand: p.custom_expand ~padding: 2 box#box in
	box
    | Color_param p ->
	let box = new color_param_box p in
	let _ = main_box#pack ~expand: false ~padding: 2 box#box in
	box
    | Font_param p ->
	let box = new font_param_box p in
	let _ = main_box#pack ~expand: false ~padding: 2 box#box in
	box
    | Date_param p ->
	let box = new date_param_box p in
	let _ = main_box#pack ~expand: false ~padding: 2 box#box in
	box
    | Hotkey_param p ->
	let box = new hotkey_param_box p in
	let _ = main_box#pack ~expand: false ~padding: 2 box#box in
	box
    | Html_param p ->
	let box = new html_param_box p in
	let _ = main_box#pack ~expand: p.string_expand ~padding: 2 box#box in
	box
  in
  let list_param_box = List.map f param_list in
  let f_apply () = 
    List.iter (fun param_box -> param_box#apply) list_param_box 
  in
  let hbox_buttons = GPack.hbox ~packing: (main_box#pack ~expand: false ~padding: 4) () in
  let rec iter_buttons ?(grab=false) = function
      [] ->
        ()
    | (label, callb) :: q ->    
        let b = GButton.button ~label: label
            ~packing:(hbox_buttons#pack ~expand:true ~fill: true ~padding:4) ()
        in
        ignore (b#connect#clicked ~callback:
		  (fun () -> f_apply (); callb ()));
        (* If it's the first button then give it the focus *)
        if grab then b#grab_default ();

        iter_buttons q
  in
  iter_buttons ~grab: true buttons;

  main_box


(** This function takes a list of parameter specifications and 
   creates a window to configure the various parameters.*)
let simple_edit ?(with_apply=true)  
    ?(apply=(fun () -> ()))
    title ?width ?height 
    param_list =
  let return = ref Return_cancel in
  let window = GWindow.window ~modal: true ~title: title () in
  let _ = match width, height with
    None, None -> ()
  | Some w, None -> window#misc#set_geometry ~width: w ()
  | None, Some h -> window#misc#set_geometry ~height: h ()
  | Some w, Some h -> window#misc#set_geometry ~width: w ~height: h ()
  in
  let _ = window#connect#destroy ~callback: GMain.Main.quit in
  let buttons = 
    (if with_apply then
      [Configwin_messages.mApply, fun () -> apply (); return := Return_apply]
    else
      []
    ) @ [
	(Configwin_messages.mOk, fun () -> return := Return_ok ; window#destroy ()) ;
	(Configwin_messages.mCancel, window#destroy) ;
      ]	
  in
  let box = box param_list buttons in
  window#add box#coerce;
  let _ = window#show () in
  GMain.Main.main () ;
  !return

let edit_string l s =
  match GToolbox.input_string ~title: l ~text: s Configwin_messages.mValue with
    None -> s
  | Some s2 -> s2
  
(** Create a string param. *)
let string ?(editable=true) ?(expand=true) ?help ?(f=(fun _ -> ())) label v =
  String_param
    {
      string_label = label ;
      string_help = help ;
      string_value = v ;
      string_editable = editable ;
      string_f_apply = f ;
      string_expand = expand ;
    } 

(** Create a bool param. *)
let bool ?(editable=true) ?help ?(f=(fun _ -> ())) label v =
  Bool_param
    {
      bool_label = label ;
      bool_help = help ;
      bool_value = v ;
      bool_editable = editable ;
      bool_f_apply = f ;
    }

(** Create a list param. *)
let list ?(editable=true) ?help
    ?(f=(fun (_:'a list) -> ())) 
    ?(eq=Pervasives.(=))
    ?(edit:('a -> 'a) option)
    ?(add=(fun () -> ([] : 'a list)))
    ?titles ?(color=(fun (_:'a) -> (None : string option)))
    label (f_strings : 'a -> string list) v =
  List_param
    (fun () ->
      Obj.magic
	(new list_param_box
	   {
	     list_label = label ;
	     list_help = help ;
	     list_value = v ;
	     list_editable = editable ;
	     list_titles = titles;
	     list_eq = eq ;
	     list_strings = f_strings ;
	     list_color = color ;
	     list_f_edit = edit ;
	     list_f_add = add ;
	     list_f_apply = f ;
	   } 
	)
    )

(** Create a strings param. *)
let strings ?(editable=true) ?help
    ?(f=(fun _ -> ())) 
    ?(eq=Pervasives.(=))
    ?(add=(fun () -> [])) label v =
  list ~editable ?help ~f ~eq ~edit: (edit_string label) ~add label (fun s -> [s]) v

(** Create a color param. *)
let color ?(editable=true) ?(expand=true) ?help ?(f=(fun _ -> ())) label v =
  Color_param
    {
      color_label = label ;
      color_help = help ;
      color_value = v ;
      color_editable = editable ;
      color_f_apply = f ;
      color_expand = expand ;
    }

(** Create a font param. *)
let font ?(editable=true) ?(expand=true) ?help ?(f=(fun _ -> ())) label v =
  Font_param
    {
      font_label = label ;
      font_help = help ;
      font_value = v ;
      font_editable = editable ;
      font_f_apply = f ;
      font_expand = expand ;
    }

(** Create a combo param. *)
let combo ?(editable=true) ?(expand=true) ?help ?(f=(fun _ -> ())) 
    ?(new_allowed=false) 
    ?(blank_allowed=false) label choices v =
  Combo_param
    {
      combo_label = label ;
      combo_help = help ;
      combo_value = v ;
      combo_editable = editable ;
      combo_choices = choices ;
      combo_new_allowed = new_allowed ;
      combo_blank_allowed = blank_allowed ;
      combo_f_apply = f ;
      combo_expand = expand ;
    }

(** Create a text param. *)
let text ?(editable=true) ?(expand=true) ?help ?(f=(fun _ -> ())) label v = 
  Text_param
    {
      string_label = label ;
      string_help = help ;
      string_value = v ;
      string_editable = editable ;
      string_f_apply = f ;
      string_expand = expand ;
    } 

(** Create a html param. *)
let html ?(editable=true) ?(expand=true) ?help ?(f=(fun _ -> ())) label v = 
  Html_param
    {
      string_label = label ;
      string_help = help ;
      string_value = v ;
      string_editable = editable ;
      string_f_apply = f ;
      string_expand = expand ;
    } 

(** Create a filename param. *)
let filename ?(editable=true) ?(expand=true)?help ?(f=(fun _ -> ())) label v = 
  Filename_param
    {
      string_label = label ;
      string_help = help ;
      string_value = v ;
      string_editable = editable ;
      string_f_apply = f ;
      string_expand = expand ;
    } 

(** Create a filenames param.*)
let filenames ?(editable=true) ?help ?(f=(fun _ -> ())) 
    ?(eq=Pervasives.(=))
    label v =
  let add () = select_files label in
  list ~editable ?help ~f ~eq ~add label (fun s -> [s]) v

(** Create a date param. *)
let date ?(editable=true) ?(expand=true) ?help ?(f=(fun _ -> ())) 
    ?(f_string=(fun(d,m,y)-> Printf.sprintf "%d/%d/%d" y (m+1) d))
    label v =
  Date_param
    {
      date_label = label ;
      date_help = help ;
      date_value = v ;
      date_editable = editable ;
      date_f_string = f_string ;
      date_f_apply = f ;
      date_expand = expand ;
    } 

(** Create a hot key param. *)
let hotkey ?(editable=true) ?(expand=true) ?help ?(f=(fun _ -> ())) label v =
  Hotkey_param
    {
      hk_label = label ;
      hk_help = help ;
      hk_value = v ;
      hk_editable = editable ;
      hk_f_apply = f ;
      hk_expand = expand ;
    } 

(** Create a custom param.*)
let custom ?label box f expand =
  Custom_param
    {
      custom_box = box ;
      custom_f_apply = f ;
      custom_expand = expand ;
      custom_framed = label ;
    } 
