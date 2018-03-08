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
    method connect : message_view_signals
    method clear : unit
    method add : Pp.t -> unit
    method add_string : string -> unit
    method set : Pp.t -> unit
    method refresh : bool -> unit
    method push : Ideutils.logger
      (** same as [add], but with an explicit level instead of [Notice] *)
    method has_selection : bool
    method get_selected_text : string
  end

let message_view () : message_view =
  let buffer = GSourceView2.source_buffer
    ~highlight_matching_brackets:true
    ~tag_table:Tags.Message.table ()
  in
  let mark = buffer#create_mark ~left_gravity:false buffer#start_iter in
  let box = GPack.vbox () in
  let scroll = GBin.scrolled_window
    ~vpolicy:`AUTOMATIC ~hpolicy:`AUTOMATIC ~packing:(box#pack ~expand:true) () in
  let view = GSourceView2.source_view
    ~source_buffer:buffer ~packing:scroll#add
    ~editable:false ~cursor_visible:false ~wrap_mode:`WORD ()
  in
  let () = Gtk_parsing.fix_double_click view in
  let default_clipboard = GData.clipboard Gdk.Atom.primary in
  let _ = buffer#add_selection_clipboard default_clipboard in
  let () = view#set_left_margin 2 in
  view#misc#show ();
  let cb clr = view#misc#modify_base [`NORMAL, `NAME clr] in
  let _ = background_color#connect#changed ~callback:cb in
  let _ = view#misc#connect#realize ~callback:(fun () -> cb background_color#get) in
  let cb ft = view#misc#modify_font (Pango.Font.from_string ft) in
  stick text_font view cb;

  (* Inserts at point, advances the mark *)
  let insert_msg (level, msg) =
    let tags = match level with
      | Feedback.Error   -> [Tags.Message.error]
      | Feedback.Warning -> [Tags.Message.warning]
      | _ -> []
    in
    let mark = `MARK mark in
    let width = Ideutils.textview_width view in
    Ideutils.insert_xml ~mark buffer ~tags (Richpp.richpp_of_pp width msg);
    buffer#insert ~iter:(buffer#get_iter_at_mark mark) "\n"
  in

  let mv = object (self)
    inherit GObj.widget box#as_widget

    (* List of displayed messages *)
    val mutable last_width = -1
    val mutable msgs = []

    val push = new GUtil.signal ()

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
        List.(iter insert_msg (rev msgs))
      end

    method clear =
      msgs <- []; self#refresh true

    method push level msg =
      msgs <- (level, msg) :: msgs;
      insert_msg (level, msg);
      push#call (level, msg)

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
