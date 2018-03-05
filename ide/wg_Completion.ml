(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module StringOrd =
struct
  type t = string
  let compare s1 s2 =
    (* we use first size, then usual comparison *)
    let d = String.length s1 - String.length s2 in
    if d <> 0 then d
    else Pervasives.compare s1 s2
end

module Proposals = Set.Make(StringOrd)

(** Retrieve completion proposals in the buffer *)
let get_syntactic_completion (buffer : GText.buffer) pattern accu =
  let rec get_aux accu (iter : GText.iter) =
    match iter#forward_search pattern with
    | None -> accu
    | Some (start, stop) ->
      if Gtk_parsing.starts_word start then
        let ne = Gtk_parsing.find_word_end stop in
        if ne#compare stop = 0 then get_aux accu stop
        else
          let proposal = buffer#get_text ~start ~stop:ne () in
          let accu = Proposals.add proposal accu in
          get_aux accu stop
      else get_aux accu stop
  in
  get_aux accu buffer#start_iter

(** Retrieve completion proposals in Coq libraries *)
let get_semantic_completion pattern accu =
  let flags = [Interface.Name_Pattern ("^" ^ pattern), true] in
  (** Only get the last part of the qualified name *)
  let rec last accu = function
  | [] -> accu
  | [basename] -> Proposals.add basename accu
  | _ :: l -> last accu l
  in
  let next = function
  | Interface.Good l ->
    let fold accu elt = last accu elt.Interface.coq_object_qualid in
    let ans = List.fold_left fold accu l in
    Coq.return ans
  | _ -> Coq.return accu
  in
  Coq.bind (Coq.search flags) next

let is_substring s1 s2 =
  let s1 = Glib.Utf8.to_unistring s1 in
  let s2 = Glib.Utf8.to_unistring s2 in
  let break = ref true in
  let i = ref 0 in
  let len1 = Array.length s1 in
  let len2 = Array.length s2 in
  while !break && !i < len1 && !i < len2 do
    break := s1.(!i) = s2.(!i);
    incr i;
  done;
  if !break then len2 - len1
  else -1

class type complete_model_signals =
  object ('a)
    method after : 'a
    method disconnect : GtkSignal.id -> unit
    method start_completion : callback:(int -> unit) -> GtkSignal.id
    method update_completion : callback:(int * string * Proposals.t -> unit) -> GtkSignal.id
    method end_completion : callback:(unit -> unit) -> GtkSignal.id
  end

let complete_model_signals
  (start_s : int GUtil.signal)
  (update_s : (int * string * Proposals.t) GUtil.signal)
  (end_s : unit GUtil.signal) : complete_model_signals =
let signals = [
  start_s#disconnect;
  update_s#disconnect;
  end_s#disconnect;
] in
object (self : 'a)
  inherit GUtil.ml_signals signals
  method start_completion = start_s#connect ~after
  method update_completion = update_s#connect ~after
  method end_completion = end_s#connect ~after
end

class complete_model coqtop (buffer : GText.buffer) =
  let cols = new GTree.column_list in
  let column = cols#add Gobject.Data.string in
  let store = GTree.list_store cols in
  let filtered_store = GTree.model_filter store in
  let start_completion_signal = new GUtil.signal () in
  let update_completion_signal = new GUtil.signal () in
  let end_completion_signal = new GUtil.signal () in
object (self)

  val signals = complete_model_signals
    start_completion_signal update_completion_signal end_completion_signal
  val mutable active = false
  val mutable auto_complete_length = 3
  (* this variable prevents CoqIDE from autocompleting when we have deleted something *)
  val mutable is_auto_completing = false
  (* this mutex ensure that CoqIDE will not try to autocomplete twice *)
  val mutable cache = (-1, "", Proposals.empty)
  val mutable insert_offset = -1
  val mutable current_completion = ("", Proposals.empty)
  val mutable lock_auto_completing = true

  method connect = signals

  method active = active

  method set_active b = active <- b

  method private handle_insert iter s =
    (* we're inserting, so we may autocomplete *)
    is_auto_completing <- true

  method private handle_delete ~start ~stop =
    (* disable autocomplete *)
    is_auto_completing <- false

  method store = filtered_store

  method column = column

  method handle_proposal path =
    let row = filtered_store#get_iter path in
    let proposal = filtered_store#get ~row ~column in
    let (start_offset, _, _) = cache in
    (* [iter] might be invalid now, get a new one to please gtk *)
    let iter = buffer#get_iter `INSERT in
    (* We cancel completion when the buffer has changed recently *)
    if iter#offset = insert_offset then begin
      let suffix =
        let len1 = String.length proposal in
        let len2 = insert_offset - start_offset in
        String.sub proposal len2 (len1 - len2)
      in
      buffer#begin_user_action ();
      ignore (buffer#insert_interactive ~iter suffix);
      buffer#end_user_action ();
    end

  method private init_proposals pref props =
    let () = store#clear () in
    let iter prop =
      let iter = store#append () in
      store#set ~row:iter ~column prop
    in
    let () = current_completion <- (pref, props) in
    Proposals.iter iter props

  method private update_proposals pref =
    let (_, _, props) = cache in
    let filter prop = 0 <= is_substring pref prop in
    let props = Proposals.filter filter props in
    let () = current_completion <- (pref, props) in
    let () = filtered_store#refilter () in
    props

  method private do_auto_complete k =
    let iter = buffer#get_iter `INSERT in
    let () = insert_offset <- iter#offset in
    let log = Printf.sprintf "Completion at offset: %i" insert_offset in
    let () = Minilib.log log in
    let prefix =
      if Gtk_parsing.ends_word iter#backward_char then
        let start = Gtk_parsing.find_word_start iter in
        let w = buffer#get_text ~start ~stop:iter () in
        if String.length w >= auto_complete_length then Some (w, start)
        else None
      else None
    in
    match prefix with
    | Some (w, start) ->
      let () = Minilib.log ("Completion of prefix: '" ^ w ^ "'") in
      let (off, prefix, props) = cache in
      let start_offset = start#offset in
      (* check whether we have the last request in cache *)
      if (start_offset = off) && (0 <= is_substring prefix w) then
        let props = self#update_proposals w in
        let () = update_completion_signal#call (start_offset, w, props) in
        k ()
      else
        let () = start_completion_signal#call start_offset in
        let update props =
          let () = cache <- (start_offset, w, props) in
          let () = self#init_proposals w props in
          update_completion_signal#call (start_offset, w, props)
        in
        (** If not in the cache, we recompute it: first syntactic *)
        let synt = get_syntactic_completion buffer w Proposals.empty in
        (** Then semantic *)
        let next prop =
          let () = update prop in
          Coq.lift k
        in
        let query = Coq.bind (get_semantic_completion w synt) next in
        (** If coqtop is computing, do the syntactic completion altogether *)
        let occupied () =
          let () = update synt in
          k ()
        in
        Coq.try_grab coqtop query occupied
    | None -> end_completion_signal#call (); k ()

  method private may_auto_complete () =
    if active && is_auto_completing && lock_auto_completing then begin
      let () = lock_auto_completing <- false in
      let unlock () = lock_auto_completing <- true in
      self#do_auto_complete unlock
    end

  initializer
    let filter_prop model row =
      let (_, props) = current_completion in
      let prop = store#get ~row ~column in
      Proposals.mem prop props
    in
    let () = filtered_store#set_visible_func filter_prop in
    (* Install auto-completion *)
    ignore (buffer#connect#insert_text ~callback:self#handle_insert);
    ignore (buffer#connect#delete_range ~callback:self#handle_delete);
    ignore (buffer#connect#after#end_user_action ~callback:self#may_auto_complete);

end

class complete_popup (model : complete_model) (view : GText.view) =
  let obj = GWindow.window ~kind:`POPUP ~show:false () in
  let frame = GBin.scrolled_window
    ~hpolicy:`NEVER ~vpolicy:`NEVER
    ~shadow_type:`OUT ~packing:obj#add ()
  in
(*   let frame = GBin.frame ~shadow_type:`OUT ~packing:obj#add () in *)
  let data = GTree.view
    ~vadjustment:frame#vadjustment ~hadjustment:frame#hadjustment
    ~rules_hint:true ~headers_visible:false
    ~model:model#store ~packing:frame#add ()
  in
  let renderer = GTree.cell_renderer_text [], ["text", model#column] in
  let col = GTree.view_column ~renderer () in
  let _ = data#append_column col in
  let () = col#set_sizing `AUTOSIZE in
  let page_size = 16 in

object (self)

  method coerce = view#coerce

  method private refresh_style () =
    let (renderer, _) = renderer in
    let font = Pango.Font.from_string Preferences.text_font#get in
    renderer#set_properties [`FONT_DESC font; `XPAD 10]

  method private coordinates pos =
    (** Toplevel position w.r.t. screen *)
    let (x, y) = Gdk.Window.get_position view#misc#toplevel#misc#window in
    (** Position of view w.r.t. window *)
    let (ux, uy) = Gdk.Window.get_position view#misc#window in
    (** Relative buffer position to view *)
    let (dx, dy) = view#window_to_buffer_coords ~tag:`WIDGET ~x:0 ~y:0 in
    (** Iter position *)
    let iter = view#buffer#get_iter pos in
    let coords = view#get_iter_location iter in
    let lx = Gdk.Rectangle.x coords in
    let ly = Gdk.Rectangle.y coords in
    let w = Gdk.Rectangle.width coords in
    let h = Gdk.Rectangle.height coords in
    (** Absolute position *)
    (x + lx + ux - dx, y + ly + uy - dy, w, h)

  method private select_any f =
    let sel = data#selection#get_selected_rows in
    let path = match sel with
    | [] ->
      begin match model#store#get_iter_first with
      | None -> None
      | Some iter -> Some (model#store#get_path iter)
      end
    | path :: _ -> Some path
    in
    match path with
    | None -> ()
    | Some path ->
      let path = f path in
      let _ = data#selection#select_path path in
      data#scroll_to_cell ~align:(0.,0.) path col

  method private select_previous () =
    let prev path =
      let copy = GTree.Path.copy path in
      if GTree.Path.prev path then path
      else copy
    in
    self#select_any prev

  method private select_next () =
    let next path =
      let () = GTree.Path.next path in
      path
    in
    self#select_any next

  method private select_previous_page () =
    let rec up i path =
      if i = 0 then path
      else
        let copy = GTree.Path.copy path in
        let has_prev = GTree.Path.prev path in
        if has_prev then up (pred i) path
        else copy
    in
    self#select_any (up page_size)

  method private select_next_page () =
    let rec down i path =
      if i = 0 then path
      else
        let copy = GTree.Path.copy path in
        let iter = model#store#get_iter path in
        let has_next = model#store#iter_next iter in
        if has_next then down (pred i) (model#store#get_path iter)
        else copy
    in
    self#select_any (down page_size)

  method private select_first () =
    let rec up path =
      let copy = GTree.Path.copy path in
      let has_prev = GTree.Path.prev path in
      if has_prev then up path
      else copy
    in
    self#select_any up

  method private select_last () =
    let rec down path =
      let copy = GTree.Path.copy path in
      let iter = model#store#get_iter path in
      let has_next = model#store#iter_next iter in
      if has_next then down (model#store#get_path iter)
      else copy
    in
    self#select_any down

  method private select_enter () =
    let sel = data#selection#get_selected_rows in
    match sel with
    | [] -> ()
    | path :: _ ->
      let () = model#handle_proposal path in
      self#hide ()

  method proposal =
    let sel = data#selection#get_selected_rows in
    if obj#misc#visible then match sel with
    | [] -> None
    | path :: _ ->
      let row = model#store#get_iter path in
      let column = model#column in
      let proposal = model#store#get ~row ~column in
      Some proposal
    else None

  method private manage_scrollbar () =
    (** HACK: we don't have access to the treeview size because of the lack of
        LablGTK binding for certain functions, so we bypass it by approximating
        it through the size of the proposals *)
    let height = match model#store#get_iter_first with
    | None -> -1
    | Some iter ->
      let path = model#store#get_path iter in
      let area = data#get_cell_area ~path ~col () in
      let height = Gdk.Rectangle.height area in
      let height = page_size * height in
      height
    in
    let len = ref 0 in
    let () = model#store#foreach (fun _ _ -> incr len; false) in
    if !len > page_size then
      let () = frame#set_vpolicy `ALWAYS in
      data#misc#set_size_request ~height ()
    else
      data#misc#set_size_request ~height:(-1) ()

  method private refresh () =
    let () = frame#set_vpolicy `NEVER in
    let () = self#select_first () in
    let () = obj#misc#show () in
    let () = self#manage_scrollbar () in
    obj#resize ~width:1 ~height:1

  method private start_callback off =
    let (x, y, w, h) = self#coordinates (`OFFSET off) in
    let () = obj#move ~x ~y:(y + 3 * h / 2) in
    ()

  method private update_callback (off, word, props) =
    if Proposals.is_empty props then self#hide ()
    else if Proposals.mem word props then self#hide ()
    else self#refresh ()

  method private end_callback () =
    obj#misc#hide ()

  method private hide () = self#end_callback ()

  initializer
    let move_cb _ _ ~extend = self#hide () in
    let key_cb ev =
      let eval cb = cb (); true in
      let ev_key = GdkEvent.Key.keyval ev in
      if obj#misc#visible then
        if ev_key = GdkKeysyms._Up then eval self#select_previous
        else if ev_key = GdkKeysyms._Down then eval self#select_next
        else if ev_key = GdkKeysyms._Tab then eval self#select_enter
        else if ev_key = GdkKeysyms._Return then eval self#select_enter
        else if ev_key = GdkKeysyms._Escape then eval self#hide
        else if ev_key = GdkKeysyms._Page_Down then eval self#select_next_page
        else if ev_key = GdkKeysyms._Page_Up then eval self#select_previous_page
        else if ev_key = GdkKeysyms._Home then eval self#select_first
        else if ev_key = GdkKeysyms._End then eval self#select_last
        else false
      else false
    in
    (** Style handling *)
    let _ = view#misc#connect#style_set ~callback:self#refresh_style in
    let _ = self#refresh_style () in
    let _ = data#set_resize_mode `PARENT in
    let _ = frame#set_resize_mode `PARENT in
    (** Callback to model *)
    let _ = model#connect#start_completion ~callback:self#start_callback in
    let _ = model#connect#update_completion ~callback:self#update_callback in
    let _ = model#connect#end_completion ~callback:self#end_callback in
    (** Popup interaction *)
    let _ = view#event#connect#key_press ~callback:key_cb in
    (** Hiding the popup when necessary*)
    let _ = view#misc#connect#hide ~callback:obj#misc#hide in
    let _ = view#event#connect#button_press ~callback:(fun _ -> self#hide (); false) in
    let _ = view#connect#move_cursor ~callback:move_cb in
    let _ = view#event#connect#focus_out ~callback:(fun _ -> self#hide (); false) in
    ()

end
