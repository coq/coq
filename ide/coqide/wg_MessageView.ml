(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
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
    method refresh : bool -> unit
    method push : Ideutils.logger
      (** same as [add], but with an explicit level instead of [Notice] *)

    (** Callback for the Ltac debugger *)
    method debug_prompt : Pp.t -> unit

    method has_selection : bool
    method get_selected_text : string
  end

let forward_send_db_cmd = ref ((fun x -> failwith "forward_send_db_cmd")
    : string -> unit)

(* The buffer can contain prompt or feedback messages *)
type message_entry_kind =
  | Fb of Feedback.level * Pp.t
  | Prompt of Pp.t

let message_view () : message_view =
  let buffer = GSourceView3.source_buffer
    ~highlight_matching_brackets:true
    ~tag_table:Tags.Message.table
    ?style_scheme:(style_manager#style_scheme source_style#get) ()
  in
  let mark = buffer#create_mark ~left_gravity:false buffer#start_iter in
  let _ = buffer#create_mark ~name:"end_of_output" buffer#end_iter in
  let box = GPack.vbox () in
  let scroll = GBin.scrolled_window
    ~vpolicy:`AUTOMATIC ~hpolicy:`AUTOMATIC ~packing:(box#pack ~expand:true) () in
  let view = GSourceView3.source_view
    ~source_buffer:buffer ~packing:scroll#add
    ~editable:false ~cursor_visible:false ~wrap_mode:`WORD ()
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

  (* Inserts at point, advances the mark *)
  let insert_fb_msg (level, msg) =
    let tags = match level with
      | Feedback.Error   -> [Tags.Message.error]
      | Feedback.Warning -> [Tags.Message.warning]
      | _ -> []
    in
    let mark = `MARK mark in
    let width = Ideutils.textview_width view in
    Ideutils.insert_xml ~mark buffer ~tags (Richpp.richpp_of_pp width msg);
    buffer#insert ~iter:(buffer#get_iter_at_mark mark) "\n";
    buffer#move_mark (`NAME "end_of_output") ~where:buffer#end_iter;
  in

  (* Insert a prompt and make the buffer editable. *)
  let insert_ltac_debug_prompt msg =
    let tags = [] in
    let mark = `MARK mark in
    let width = Ideutils.textview_width view in
    Ideutils.insert_xml ~mark buffer ~tags (Richpp.richpp_of_pp width msg);
    buffer#move_mark (`NAME "end_of_output") ~where:buffer#end_iter;
    view#set_editable true;
    view#set_cursor_visible true;
    view#scroll_to_mark (`NAME "end_of_output"); (* scroll to end *)
    buffer#move_mark `INSERT ~where:buffer#end_iter;
    let ins = buffer#get_iter_at_mark `INSERT in
    buffer#select_range ins ins;  (* avoid highlighting *)
  in

  let insert_msg = function
    | Fb (lvl,msg) -> insert_fb_msg (lvl,msg)
    | Prompt msg -> insert_ltac_debug_prompt msg

  in
  let msgs : message_entry_kind list ref = ref [] in
  let (return, _) = GtkData.AccelGroup.parse "Return" in
  let (backspace, _) = GtkData.AccelGroup.parse "BackSpace" in
  let (delete, _) = GtkData.AccelGroup.parse "Delete" in

  (* Keypress handler *)
  let keypress_cb ev =
    let ev_key = GdkEvent.Key.keyval ev in
    let ins = buffer#get_iter_at_mark `INSERT in
    let eoo = buffer#get_iter_at_mark (`NAME "end_of_output") in
    let delta = ins#offset - eoo#offset in
    if not view#editable then
      false
    else if ev_key = delete && delta < 0 then
      true (* ignore DELETE before end of output *)
    else if ev_key = backspace && delta <= 0 then
      true (* ignore BACKSPACE before eoo *)
    else begin
      if delta < 0 then
        buffer#move_mark `INSERT ~where:buffer#end_iter;
      if (ev_key >= Char.code ' ' && ev_key <= Char.code '~') then begin
        buffer#insert (String.make 1 (Char.chr ev_key));
        view#scroll_to_mark `INSERT; (* scroll to insertion point *)
        let ins = buffer#get_iter_at_mark `INSERT in
        buffer#select_range ins ins;  (* avoid highlighting *)
        true (* consume the event *)
      end else if ev_key = return then begin
        let ins = buffer#get_iter_at_mark `INSERT in
        let cmd = buffer#get_text ~start:eoo ~stop:ins () in
        msgs := Fb (Feedback.Notice, Pp.str cmd) :: !msgs;
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

    (* List of displayed messages *)
    val mutable last_width = -1

    val push = new GUtil.signal ()

    method source_buffer = buffer

    method connect =
      new message_view_signals_impl box#as_widget push

    method refresh force =
      (* We need to block updates here due to the following race:
         insertion of messages may create a vertical scrollbar, this
         will trigger a width change, calling refresh again and
         going into an infinite loop. *)
      let width = Ideutils.textview_width view  in
      (* Could still this method race if the scrollbar changes the
         textview_width ?? *)
      let needed = force || last_width <> width in
      if needed then begin
        last_width <- width;
        buffer#set_text "";
        buffer#move_mark (`MARK mark) ~where:buffer#start_iter;
        List.(iter insert_msg (rev !msgs))
      end

    method clear =
      msgs := []; self#refresh true

    method push level msg =
      msgs := Fb (level, msg) :: !msgs;
      insert_fb_msg (level, msg);
      push#call (level, msg)

    method debug_prompt msg =
      msgs := Prompt msg :: !msgs;
      insert_ltac_debug_prompt msg

    method add msg = self#push Feedback.Notice msg

    method add_string s = self#add (Pp.str s)

    method set msg = self#clear; self#add msg

    method has_selection = buffer#has_selection
    method get_selected_text =
      if buffer#has_selection then
        let start, stop = buffer#selection_bounds in
        buffer#get_text ~slice:true ~start ~stop ()
      else ""

  end
  in
  (* Is there a better way to connect the signal ? *)
  let w_cb (_ : Gtk.rectangle) = mv#refresh false in
  ignore (view#misc#connect#size_allocate ~callback:w_cb);
  mv
