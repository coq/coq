(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Preferences

class type message_view_signals =
object
  inherit GObj.misc_signals
  inherit GUtil.add_ml_signals
  method pushed : callback:Ideutils.logger -> GtkSignal.id
end

class message_view_signals_impl obj (pushed : 'a GUtil.signal) : message_view_signals =
object
  val after = false
  inherit GObj.misc_signals obj
  inherit GUtil.add_ml_signals obj [pushed#disconnect]
  method pushed ~callback = pushed#connect ~after ~callback:(fun (lvl, s) -> callback lvl s)
end

class type message_view =
  object
    inherit GObj.widget
    method source_buffer : GSourceView3.source_buffer
    method connect : message_view_signals
    method clear : unit
    method add : Pp.t -> unit
    method add_string : string -> unit
    method set : Pp.t -> unit
    method push : Ideutils.logger
      (** same as [add], but with an explicit level instead of [Notice] *)

    (** Callback for the Ltac debugger *)
    method debug_prompt : Pp.t -> unit

    method select_all : unit -> unit
    method has_selection : bool
    method get_selected_text : string
    method editable2 : bool
    method set_editable2 : bool -> unit
    method set_forward_send_db_cmd : (string -> unit) -> unit
    method set_forward_send_db_stack : (unit -> unit) -> unit
    method set_forward_show_debugger : (unit -> unit) -> unit
  end

let forward_keystroke = ref ((fun x -> failwith "forward_keystroke (mv)")
    : Gdk.keysym * Gdk.Tags.modifier list -> int -> bool)

(* The buffer can contain prompt or feedback messages *)
type message_entry_kind =
  | Fb of Feedback.level * Pp.t
  | Prompt of Pp.t

let message_view sid : message_view =
  let buffer = GSourceView3.source_buffer
    ~highlight_matching_brackets:true
    ~tag_table:Tags.Message.table
    ?style_scheme:(style_manager#style_scheme source_style#get) ()
  in
  buffer#set_max_undo_levels 0;
  let mark = buffer#create_mark ~left_gravity:false buffer#start_iter in
  let _ = buffer#create_mark ~name:"end_of_output" buffer#end_iter in
  let box = GPack.vbox () in
  let scroll = GBin.scrolled_window
    ~vpolicy:`AUTOMATIC ~hpolicy:`AUTOMATIC ~packing:(box#pack ~expand:true) () in
  let view = GSourceView3.source_view
    ~source_buffer:buffer ~packing:scroll#add
    ~editable:false ~cursor_visible:false ~wrap_mode:`CHAR ()
  in
  let () = Gtk_parsing.fix_double_click view in
  let default_clipboard = GData.clipboard Gdk.Atom.primary in
  let _ = buffer#add_selection_clipboard default_clipboard in
  let () = view#set_left_margin 2 in
  view#misc#show ();
(* FIXME: handle this using CSS *)
(*   let cb clr = view#misc#modify_bg [`NORMAL, `NAME clr] in *)
(*   let _ = background_color#connect#changed ~callback:cb in *)
(*   let _ = view#misc#connect#realize ~callback:(fun () -> cb background_color#get) in *)
  let cb ft = view#misc#modify_font (GPango.font_description_from_string ft) in
  stick text_font view cb;

  let insert_xml ~mark buffer ~tags msg =
    let width = Ideutils.textview_width view in
    let before = buffer#line_count in
    Ideutils.insert_xml ~mark buffer ~tags (Richpp.richpp_of_pp ~width msg);
    buffer#line_count - before
  in

  (* Inserts at point, advances the mark *)
  let insert_fb_msg (level, msg) =
    let tags = match level with
      | Feedback.Error   -> [Tags.Message.error]
      | Feedback.Warning -> [Tags.Message.warning]
      | _ -> []
    in
    let mark = `MARK mark in
    let lines = insert_xml ~mark buffer ~tags msg in
    buffer#insert ~iter:(buffer#end_iter) "\n";
    buffer#move_mark (`NAME "end_of_output") ~where:buffer#end_iter;
    view#scroll_to_mark `INSERT; (* scroll to end *)
    lines
  in

  let forward_send_db_stack = ref ((fun x -> failwith "forward_send_db_stack")
    : unit -> unit) in
  let forward_show_debugger = ref ((fun x -> failwith "forward_show_debugger")
    : unit -> unit) in

  (* Insert a prompt and make the buffer editable. *)
  let insert_ltac_debug_prompt ?(refresh=false) msg =
    if not refresh then begin
      !forward_send_db_stack ();
      !forward_show_debugger ();
    end;
    let tags = [] in
    let mark = `MARK mark in
    let lines = insert_xml ~mark buffer ~tags msg in
    buffer#move_mark (`NAME "end_of_output") ~where:buffer#end_iter;
    view#set_editable true;
    view#set_cursor_visible true;
    view#scroll_to_mark (`NAME "end_of_output"); (* scroll to end *)
    buffer#move_mark `INSERT ~where:buffer#end_iter;
    let ins = buffer#get_iter_at_mark `INSERT in
    buffer#select_range ins ins;  (* avoid highlighting *)
    lines
  in

  let insert_msg  ?(refresh=false) = function
    | Fb (lvl,msg) -> insert_fb_msg (lvl,msg)
    | Prompt msg -> insert_ltac_debug_prompt ~refresh msg
  in

  (* List of displayed messages *)
  let msgs : (message_entry_kind * int) list ref = ref [] in
  let last_width = ref (-1) in

  let refresh force =
    (* We need to block updates here due to the following race:
       insertion of messages may create a vertical scrollbar, this
       will trigger a width change, calling refresh again and
       going into an infinite loop. *)
    let width = Ideutils.textview_width view  in
    (* Could still this method race if the scrollbar changes the
       textview_width ?? *)
    let needed = force || !last_width <> width in
    if needed then begin
      last_width := width;
      buffer#set_text "";
      buffer#move_mark (`MARK mark) ~where:buffer#start_iter;
      List.(iter (fun (m,_) -> ignore @@ insert_msg ~refresh:true m) (rev !msgs))
    end
  in

  (* todo: verify whether msgs is still needed *)
  let add_msg msg =
    let mlines = insert_msg msg in
    msgs := (msg, mlines) :: !msgs;
    let max_lines = 1000 in
    if buffer#line_count > max_lines then begin
      let rec trim lcnt res msgs =
        match msgs with
        | (m,len) :: tl when lcnt < max_lines ->
            trim (lcnt+len) ((m,len) :: res) tl
        | _ -> lcnt, res
      in
      let lcnt, res = trim 0 [] !msgs in
      msgs := res;
      let stop = buffer#start_iter#forward_lines (buffer#line_count - lcnt) in
      buffer#delete ~start:buffer#start_iter ~stop;
    end
  in

  let return    = GtkData.AccelGroup.parse "Return" in
  let backspace = GtkData.AccelGroup.parse "BackSpace" in
  let delete    = GtkData.AccelGroup.parse "Delete" in

  let forward_send_db_cmd = ref ((fun x -> failwith "forward_send_db_cmd")
    : string -> unit) in

  (* Keypress handler *)
  let keypress_cb ev =
    let key_ev = Ideutils.filter_key ev in
    let state = GdkEvent.Key.state ev in
    let ins = buffer#get_iter_at_mark `INSERT in
    let eoo = buffer#get_iter_at_mark (`NAME "end_of_output") in
    let delta = ins#offset - eoo#offset in
    if !forward_keystroke key_ev sid then
      true (* support some function keys when Messages is detached *)
    else if not view#editable || List.mem `CONTROL state || List.mem `MOD1 state then
      false
    else if key_ev = delete && delta < 0 then
      true (* ignore DELETE before end of output *)
    else if key_ev = backspace && delta <= 0 then
      true (* ignore BACKSPACE before eoo *)
    else begin
      if delta < 0 then
        buffer#move_mark `INSERT ~where:buffer#end_iter;
      let key_code = GdkEvent.Key.keyval ev in
      if (key_code >= Char.code ' ' && key_code <= Char.code '~') then begin
        buffer#insert (String.make 1 (Char.chr key_code));
        view#scroll_to_mark `INSERT; (* scroll to insertion point *)
        let ins = buffer#get_iter_at_mark `INSERT in
        buffer#select_range ins ins;  (* avoid highlighting *)
        true (* consume the event *)
      end else if key_ev = return then begin
        let ins = buffer#get_iter_at_mark `INSERT in
        let cmd = buffer#get_text ~start:eoo ~stop:ins () in
        (* save cmd but don't print a second time *)
        msgs := (Fb (Feedback.Notice, Pp.str cmd), 0) :: !msgs;
        buffer#insert "\n";
        buffer#move_mark `INSERT ~where:buffer#end_iter;
        view#scroll_to_mark `INSERT; (* scroll to insertion point *)
        let ins = buffer#get_iter_at_mark `INSERT in
        buffer#select_range ins ins;  (* avoid highlighting *)
        buffer#move_mark (`NAME "end_of_output") ~where:buffer#end_iter;
        view#set_editable false;
        view#set_cursor_visible false;

        !forward_send_db_cmd cmd;
        true
      end else
        false
      end
  in
  let _ = view#event#connect#key_press ~callback:keypress_cb in

  let mv = object (self)
    inherit GObj.widget box#as_widget

    val push = new GUtil.signal ()

    method source_buffer = buffer

    method connect =
      new message_view_signals_impl box#as_widget push

    method clear =
      msgs := []; refresh true

    method push level msg =
      add_msg (Fb (level, msg));
      push#call (level, msg)

    method debug_prompt msg =
      add_msg (Prompt msg);

    method add msg = self#push Feedback.Notice msg

    method add_string s = self#add (Pp.str s)

    method set msg = self#clear; self#add msg

    method select_all () =
      if view#is_focus then
        self#source_buffer#select_range self#source_buffer#start_iter self#source_buffer#end_iter;
    method has_selection = buffer#has_selection
    method get_selected_text =
      if buffer#has_selection then
        let start, stop = buffer#selection_bounds in
        buffer#get_text ~slice:true ~start ~stop ()
      else ""
    method editable2 = view#editable
    method set_editable2 v = view#set_editable v; view#set_cursor_visible v
    method set_forward_send_db_cmd f = forward_send_db_cmd := f
    method set_forward_send_db_stack f = forward_send_db_stack := f
    method set_forward_show_debugger f = forward_show_debugger := f
  end
  in
  (* Is there a better way to connect the signal ? *)
  let w_cb (_ : Gtk.rectangle) = refresh false in
  ignore (view#misc#connect#size_allocate ~callback:w_cb);
  mv
