(*********************************************************************************)
(*                Cameleon                                                       *)
(*                                                                               *)
(*    Copyright (C) 2005 Institut National de Recherche en Informatique et       *)
(*    en Automatique. All rights reserved.                                       *)
(*                                                                               *)
(*    This program is free software; you can redistribute it and/or modify       *)
(*    it under the terms of the GNU Library General Public License as            *)
(*    published by the Free Software Foundation; either version 2 of the         *)
(*    License, or  any later version.                                            *)
(*                                                                               *)
(*    This program is distributed in the hope that it will be useful,            *)
(*    but WITHOUT ANY WARRANTY; without even the implied warranty of             *)
(*    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the              *)
(*    GNU Library General Public License for more details.                       *)
(*                                                                               *)
(*    You should have received a copy of the GNU Library General Public          *)
(*    License along with this program; if not, write to the Free Software        *)
(*    Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA                   *)
(*    02111-1307  USA                                                            *)
(*                                                                               *)
(*    Contact: Maxence.Guesdon@inria.fr                                          *)
(*                                                                               *)
(*********************************************************************************)

(** This module contains the gui functions of Configwin.*)

open Configwin_types

let modifiers_to_string m =
  let rec iter m s =
    match m with
        [] -> s
      | c :: m ->
          iter m ((
                    match c with
			`CONTROL -> "<ctrl>"
		      | `SHIFT -> "<shft>"
		      | `LOCK -> "<lock>"
		      | `MOD1 -> "<alt>"
		      | `MOD2 -> "<mod2>"
		      | `MOD3 -> "<mod3>"
		      | `MOD4 -> "<mod4>"
		      | `MOD5 -> "<mod5>"
		      | _  -> raise Not_found
                  ) ^ s)
  in
    iter m ""

class type widget =
  object
    method box : GObj.widget
    method apply : unit -> unit
  end

let debug = false
let dbg s = if debug then Minilib.log s else ()

(** This class builds a frame with a clist and two buttons :
   one to add items and one to remove the selected items.
   The class takes in parameter a function used to add items and
   a string list ref which is used to store the content of the clist.
   At last, a title for the frame  is also in parameter, so that
   each instance of the class creates a frame. *)
class ['a] list_selection_box
    (listref : 'a list ref)
    titles_opt
    help_opt
    f_edit_opt
    f_strings
    f_color
    (eq : 'a -> 'a -> bool)
    add_function title editable
    (tt:GData.tooltips)
    =
  let _ = dbg "list_selection_box" in
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
	tt#set_tip ~text: help ~privat: help wev#coerce
  in  (* the vbox for the buttons *)
  let vbox_buttons = GPack.vbox () in
  let _ =
    if editable then
      let _ = hbox#pack ~expand: false vbox_buttons#coerce in
      ()
    else
      ()
  in
  let _ = dbg "list_selection_box: wb_add" in
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
  let _ = dbg "list_selection_box: object(self)" in
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
      let _ = dbg "list_selection_box: connecting wb_add" in
      (* connect the functions to the buttons *)
      ignore (wb_add#connect#clicked ~callback:f_add);
      let _ = dbg "list_selection_box: connecting wb_remove" in
      ignore (wb_remove#connect#clicked ~callback:f_remove);
      let _ = dbg "list_selection_box: connecting wb_up" in
      ignore (wb_up#connect#clicked ~callback:(fun () -> self#up_selected));
      (
       match f_edit_opt with
	 None -> ()
       | Some f ->
	   let _ = dbg "list_selection_box: connecting wb_edit" in
	   ignore (wb_edit#connect#clicked ~callback:(fun () -> self#edit_selected f))
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
      let _ = dbg "list_selection_box: connecting select_row" in
      ignore(wlist#connect#select_row ~callback:f_select);
      let _ = dbg "list_selection_box: connecting unselect_row" in
      ignore(wlist#connect#unselect_row ~callback:f_unselect);

      (* initialize the clist with the listref *)
      self#update !listref
  end;;


(** This class is used to build a box for a string parameter.*)
class string_param_box param (tt:GData.tooltips) =
  let _ = dbg "string_param_box" in
  let hbox = GPack.hbox () in
  let wev = GBin.event_box ~packing: (hbox#pack ~expand: false ~padding: 2) () in
  let _wl = GMisc.label ~text: param.string_label ~packing: wev#add () in
  let we = GEdit.entry
      ~editable: param.string_editable
      ~packing: (hbox#pack ~expand: param.string_expand ~padding: 2)
      ()
  in
  let _ =
    match param.string_help with
      None -> ()
    | Some help ->
	tt#set_tip ~text: help ~privat: help wev#coerce
  in
  let _ = we#set_text (param.string_to_string param.string_value) in

  object (self)
    (** This method returns the main box ready to be packed. *)
    method box = hbox#coerce
    (** This method applies the new value of the parameter. *)
    method apply =
      let new_value = param.string_of_string we#text in
      if new_value <> param.string_value then
	let _ = param.string_f_apply new_value in
	param.string_value <- new_value
      else
	()
  end ;;

(** This class is used to build a box for a combo parameter.*)
class combo_param_box param (tt:GData.tooltips) =
    let _ = dbg "combo_param_box" in
    let hbox = GPack.hbox () in
    let wev = GBin.event_box ~packing: (hbox#pack ~expand: false ~padding: 2) () in
    let _wl = GMisc.label ~text: param.combo_label ~packing: wev#add () in
    let _ =
      match param.combo_help with
	  None -> ()
	| Some help ->
	    tt#set_tip ~text: help ~privat: help wev#coerce
    in
    let get_value = if not param.combo_new_allowed then
      let wc = GEdit.combo_box_text
	~strings: param.combo_choices
	?active:(let rec aux i = function
		   |[] -> None
		   |h::_ when h = param.combo_value -> Some i
		   |_::t -> aux (succ i) t
		 in aux 0 param.combo_choices)
	~packing: (hbox#pack ~expand: param.combo_expand ~padding: 2)
	()
      in
	fun () -> match GEdit.text_combo_get_active wc with |None -> "" |Some s -> s
    else
      let (wc,_) = GEdit.combo_box_entry_text
	~strings: param.combo_choices
	~packing: (hbox#pack ~expand: param.combo_expand ~padding: 2)
	()
      in
      let _ = wc#entry#set_editable param.combo_editable in
      let _ = wc#entry#set_text param.combo_value in
	fun () -> wc#entry#text
    in
object (self)
  (** This method returns the main box ready to be packed. *)
  method box = hbox#coerce
    (** This method applies the new value of the parameter. *)
  method apply =
    let new_value = get_value () in
      if new_value <> param.combo_value then
	let _ = param.combo_f_apply new_value in
	  param.combo_value <- new_value
      else
	()
end ;;

(** Class used to pack a custom box. *)
class custom_param_box param (tt:GData.tooltips) =
  let _ = dbg "custom_param_box" in
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

(** This class is used to build a box for a text parameter.*)
class text_param_box param (tt:GData.tooltips) =
  let _ = dbg "text_param_box" in
  let wf = GBin.frame ~label: param.string_label ~height: 100 () in
  let wev = GBin.event_box ~packing: wf#add () in
  let wscroll = GBin.scrolled_window
      ~vpolicy: `AUTOMATIC
      ~hpolicy: `AUTOMATIC
      ~packing: wev#add ()
  in
  let wview = GText.view
      ~editable: param.string_editable
      ~packing: wscroll#add
      ()
  in
  let _ =
    match param.string_help with
      None -> ()
    | Some help ->
	tt#set_tip ~text: help ~privat: help wev#coerce
  in
  let _ = dbg "text_param_box: buffer creation" in
  let buffer = GText.buffer () in

  let _ = wview#set_buffer buffer in
  let _ = buffer#insert (param.string_to_string param.string_value) in
  let _ = dbg "text_param_box: object(self)" in
  object (self)
    val wview = wview
    (** This method returns the main box ready to be packed. *)
    method box = wf#coerce
    (** This method applies the new value of the parameter. *)
    method apply =
      let v = param.string_of_string (buffer#get_text ()) in
      if v <> param.string_value then
	(
	 dbg "apply new value!";
	 let _ = param.string_f_apply v in
	 param.string_value <- v
	)
      else
	()
  end ;;

(** This class is used to build a box for a boolean parameter.*)
class bool_param_box param (tt:GData.tooltips) =
  let _ = dbg "bool_param_box" in
  let wchk = GButton.check_button
      ~label: param.bool_label
      ()
  in
  let _ =
    match param.bool_help with
      None -> ()
    | Some help -> tt#set_tip ~text: help ~privat: help wchk#coerce
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

class modifiers_param_box param =
  let hbox = GPack.hbox () in
  let wev = GBin.event_box ~packing: (hbox#pack ~expand:true ~fill:true ~padding: 2) () in
  let _wl = GMisc.label ~text: param.md_label ~packing: wev#add () in
  let value = ref param.md_value in
  let _ = List.map (fun modifier ->
                      let but = GButton.toggle_button
                                  ~label:(modifiers_to_string [modifier])
                                  ~active:(List.mem modifier param.md_value)
                                  ~packing:(hbox#pack ~expand:false) () in
                      ignore (but#connect#toggled
                                ~callback:(fun _ -> if but#active then value := modifier::!value
                                 else value := List.filter ((<>) modifier) !value)))
            param.md_allow
  in
  let _ =
    match param.md_help with
      None -> ()
    | Some help ->
       let tooltips = GData.tooltips () in
       ignore (hbox#connect#destroy ~callback: tooltips#destroy);
       tooltips#set_tip wev#coerce ~text: help ~privat: help
  in
  object (self)
    (** This method returns the main box ready to be packed. *)
    method box = hbox#coerce
    (** This method applies the new value of the parameter. *)
    method apply =
      let new_value = !value in
      if new_value <> param.md_value then
	let _ = param.md_f_apply new_value in
	param.md_value <- new_value
      else
	()
  end ;;

(** This class is used to build a box for a parameter whose values are a list.*)
class ['a] list_param_box (param : 'a list_param) (tt:GData.tooltips) =
  let _ = dbg "list_param_box" in
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
      tt
  in

  object (self)
    (** This method returns the main box ready to be packed. *)
    method box = frame_selection#box#coerce
    (** This method applies the new value of the parameter. *)
    method apply =
      param.list_f_apply !listref ;
      param.list_value <- !listref
  end ;;

(** This class creates a configuration box from a configuration structure *)
class configuration_box (tt : GData.tooltips) conf_struct =

  let main_box = GPack.hbox () in

  let columns = new GTree.column_list in
  let icon_col = columns#add GtkStock.conv in
  let label_col = columns#add Gobject.Data.string in
  let box_col = columns#add Gobject.Data.caml in
  let () = columns#lock () in

  let pane = GPack.paned `HORIZONTAL ~packing:main_box#add () in

  (* Tree view part *)
  let scroll = GBin.scrolled_window ~hpolicy:`NEVER ~packing:pane#pack1 () in
  let tree = GTree.tree_store columns in
  let view = GTree.view ~model:tree ~headers_visible:false ~packing:scroll#add_with_viewport () in
  let selection = view#selection in
  let _ = selection#set_mode `SINGLE in

  let menu_box = GPack.vbox ~packing:pane#pack2 () in

  let renderer = (GTree.cell_renderer_pixbuf [], ["stock-id", icon_col]) in
  let col = GTree.view_column ~renderer () in
  let _ = view#append_column col in

  let renderer = (GTree.cell_renderer_text [], ["text", label_col]) in
  let col = GTree.view_column ~renderer () in
  let _ = view#append_column col in

  let make_param (main_box : #GPack.box) = function
  | String_param p ->
    let box = new string_param_box p tt in
    let _ = main_box#pack ~expand: false ~padding: 2 box#box in
    box
  | Combo_param p ->
    let box = new combo_param_box p tt in
    let _ = main_box#pack ~expand: false ~padding: 2 box#box in
    box
  | Text_param p ->
    let box = new text_param_box p tt in
    let _ = main_box#pack ~expand: p.string_expand ~padding: 2 box#box in
    box
  | Bool_param p ->
    let box = new bool_param_box p tt in
    let _ = main_box#pack ~expand: false ~padding: 2 box#box in
    box
  | List_param f ->
    let box = f tt in
    let _ = main_box#pack ~expand: true ~padding: 2 box#box in
    box
  | Custom_param p ->
    let box = new custom_param_box p tt in
    let _ = main_box#pack ~expand: p.custom_expand ~padding: 2 box#box in
    box
  | Modifiers_param p ->
    let box = new modifiers_param_box p in
    let _ = main_box#pack ~expand: false ~padding: 2 box#box in
    box
  in

  let set_icon iter = function
  | None -> ()
  | Some icon -> tree#set ~row:iter ~column:icon_col icon
  in

  (* Populate the tree *)

  let rec make_tree iter conf_struct =
    (* box is not shown at first *)
    let box = GPack.vbox ~packing:(menu_box#pack ~expand:true) ~show:false () in
    let new_iter = match iter with
    | None -> tree#append ()
    | Some parent -> tree#append ~parent ()
    in
    match conf_struct with
    | Section (label, icon, param_list) ->
      let params = List.map (make_param box) param_list in
      let widget =
        object
          method box = box#coerce
          method apply () = List.iter (fun param -> param#apply) params
        end
      in
      let () = tree#set ~row:new_iter ~column:label_col label in
      let () = set_icon new_iter icon in
      let () = tree#set ~row:new_iter ~column:box_col widget in
      ()
    | Section_list (label, icon, struct_list) ->
      let widget =
        object
      (* Section_list does not contain any effect widget, so we do not have to
         apply anything. *)
          method apply () = ()
          method box = box#coerce
        end
      in
      let () = tree#set ~row:new_iter ~column:label_col label in
      let () = set_icon new_iter icon in
      let () = tree#set ~row:new_iter ~column:box_col widget in
      List.iter (make_tree (Some new_iter)) struct_list
  in

  let () = List.iter (make_tree None) conf_struct in

  (* Dealing with signals *)

  let current_prop : widget option ref = ref None in

  let select_iter iter =
    let () = match !current_prop with
    | None -> ()
    | Some box -> box#box#misc#hide ()
    in
    let box = tree#get ~row:iter ~column:box_col in
    let () = box#box#misc#show () in
    current_prop := Some box
  in

  let when_selected () =
    let rows = selection#get_selected_rows in
    match rows with
    | [] -> ()
    | row :: _ ->
      let iter = tree#get_iter row in
      select_iter iter
  in

  (* Focus on a box when selected *)

  let _ = selection#connect#changed ~callback:when_selected in

  let _ = match tree#get_iter_first with
  | None -> ()
  | Some iter -> select_iter iter
  in

  object

    method box = main_box

    method apply =
      let foreach _ iter =
        let widget = tree#get ~row:iter ~column:box_col in
        widget#apply(); false
      in
      tree#foreach foreach

  end

(** This function takes a configuration structure list and creates a window
   to configure the various parameters. *)
let edit ?(with_apply=true)
    ?(apply=(fun () -> ()))
    title ?width ?height
    conf_struct =
  let dialog = GWindow.dialog
    ~position:`CENTER
    ~modal: true ~title: title
    ?height ?width
    ()
  in
  let tooltips = GData.tooltips () in

  let config_box = new configuration_box tooltips conf_struct in

  let _ = dialog#vbox#add config_box#box#coerce in

  if with_apply then
    dialog#add_button Configwin_messages.mApply `APPLY;

  dialog#add_button Configwin_messages.mOk `OK;
  dialog#add_button Configwin_messages.mCancel `CANCEL;

  let destroy () =
    tooltips#destroy () ;
    dialog#destroy ();
  in
  let rec iter rep =
    try
      match dialog#run () with
        | `APPLY  -> config_box#apply; iter Return_apply
        | `OK -> config_box#apply; destroy (); Return_ok
        | _ -> destroy (); rep
    with
        Failure s ->
          GToolbox.message_box ~title:"Error" s; iter rep
      | e ->
          GToolbox.message_box ~title:"Error" (Printexc.to_string e); iter rep
  in
    iter Return_cancel

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
      string_to_string = (fun x -> x) ;
      string_of_string = (fun x -> x) ;
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
    (fun tt ->
	new list_param_box
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
	  tt
    )

(** Create a strings param. *)
let strings ?(editable=true) ?help
    ?(f=(fun _ -> ()))
    ?(eq=Pervasives.(=))
    ?(add=(fun () -> [])) label v =
  list ~editable ?help ~f ~eq ~edit: (edit_string label) ~add label (fun s -> [s]) v

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

let modifiers
  ?(editable=true)
  ?(expand=true)
  ?help
  ?(allow=[`CONTROL;`SHIFT;`LOCK;`MOD1;`MOD2;`MOD3;`MOD4;`MOD5])
  ?(f=(fun _ -> ())) label v =
  Modifiers_param
    {
      md_label = label ;
      md_help = help ;
      md_value = v ;
      md_editable = editable ;
      md_f_apply = f ;
      md_expand = expand ;
      md_allow = allow ;
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
