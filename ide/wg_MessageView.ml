(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Preferences

class type message_view_signals =
object
  inherit GObj.misc_signals
  inherit GUtil.add_ml_signals
  method pushed : callback:(Pp.message_level -> string -> unit) -> GtkSignal.id
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
    method add : string -> unit
    method set : string -> unit
    method push : Pp.message_level -> string -> unit
      (** same as [add], but with an explicit level instead of [Notice] *)
    method buffer : GText.buffer
      (** for more advanced text edition *)
    method modify_font : Pango.font_description -> unit
  end

let message_view () : message_view =
  let buffer = GSourceView2.source_buffer
    ~highlight_matching_brackets:true
    ~tag_table:Tags.Message.table ()
  in
  let text_buffer = new GText.buffer buffer#as_buffer in
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
  let _ = background_color#connect#changed cb in
  let _ = view#misc#connect#realize (fun () -> cb background_color#get) in
  object (self)
    inherit GObj.widget box#as_widget

    val push = new GUtil.signal ()

    method connect =
      new message_view_signals_impl box#as_widget push

    method clear =
      buffer#set_text ""

    method push level msg =
      let tags = match level with
      | Pp.Error -> [Tags.Message.error]
      | Pp.Warning -> [Tags.Message.warning]
      | _ -> []
      in
      if msg <> "" then begin
        buffer#insert ~tags msg;
        buffer#insert ~tags "\n";
        push#call (level, msg)
      end

    method add msg = self#push Pp.Notice msg

    method set msg = self#clear; self#add msg

    method buffer = text_buffer

    method modify_font fd = view#misc#modify_font fd

  end
