(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Ideutils
open GText
type action =
  | Insert of string * int * int (* content*pos*length *)
  | Delete of string * int * int (* content*pos*length *)

let neg act = match act with
  | Insert (s,i,l) -> Delete (s,i,l)
  | Delete (s,i,l) -> Insert (s,i,l)

type source_view = [ Gtk.text_view | `sourceview ] Gtk.obj

class script_view (tv : source_view) =
object (self)
  inherit GSourceView2.source_view (Gobject.unsafe_cast tv) as super

  val mutable history = []
  val mutable redo = []

  val undo_lock = Mutex.create ()

  method private dump_debug () =
    let iter = function
    | Insert (s, p, l) ->
      Printf.eprintf "Insert of '%s' at %d (length %d)\n" s p l
    | Delete (s, p, l) ->
      Printf.eprintf "Delete '%s' from %d (length %d)\n" s p l
    in
    if false (* !debug *) then begin
      prerr_endline "==========Undo Stack top=============";
      List.iter iter history;
      Printf.eprintf "Stack size %d\n" (List.length history);
      prerr_endline "==========Undo Stack Bottom==========";
      prerr_endline "==========Redo Stack start=============";
      List.iter iter redo;
      Printf.eprintf "Stack size %d\n" (List.length redo);
      prerr_endline "==========Redo Stack End=========="
    end

  method clear_undo () =
    history <- [];
    redo <- []

  method private forward () =
    match redo with
    | [] -> ()
    | action :: h ->
      redo <- h;
      history <- neg action :: history

  method private backward () =
    match history with
    | [] -> ()
    | action :: h ->
      history <- h;
      redo <- neg action :: redo

  method private process_action = function
  | [] -> false
  | Insert (s, p, l) :: history ->
    let start = self#buffer#get_iter_at_char p in
    let stop = start#forward_chars l in
    self#buffer#delete_interactive ~start ~stop ()
  | Delete (s, p, l) :: history ->
    let iter = self#buffer#get_iter_at_char p in
    self#buffer#insert_interactive ~iter s

  method undo () =
    if Mutex.try_lock undo_lock then begin
      prerr_endline "UNDO";
      let effective = self#process_action history in
      if effective then self#backward ();
      Mutex.unlock undo_lock;
      effective
    end else
      (prerr_endline "UNDO DISCARDED"; true)

  method redo () =
    if Mutex.try_lock undo_lock then begin
      prerr_endline "REDO";
      let effective = self#process_action redo in
      if effective then self#forward ();
      Mutex.unlock undo_lock;
      effective
    end else
      (prerr_endline "REDO DISCARDED"; true)

  method private handle_insert iter s =
    if Mutex.try_lock undo_lock then begin
      let action = Insert (s, iter#offset, Glib.Utf8.length s) in
      history <- action :: history;
      redo <- [];
      self#dump_debug ();
      Mutex.unlock undo_lock
    end

  method private handle_delete ~start ~stop =
    if Mutex.try_lock undo_lock then begin
      let start_offset = start#offset in
      let stop_offset = stop#offset in
      let s = self#buffer#get_text ~start ~stop () in
      let action = Delete (s, start_offset, stop_offset - start_offset) in
      history <- action :: history;
      redo <- [];
      self#dump_debug ();
      Mutex.unlock undo_lock
    end

  initializer
    ignore (self#buffer#connect#insert_text ~callback:self#handle_insert);
    ignore (self#buffer#connect#delete_range ~callback:self#handle_delete);
    (* HACK: Redirect the undo/redo signals of the underlying GtkSourceView *)
    ignore (self#connect#undo (fun _ -> ignore (self#undo ()); GtkSignal.stop_emit()));
    ignore (self#connect#redo (fun _ -> ignore (self#redo ()); GtkSignal.stop_emit()));

end

let script_view ?(source_buffer:GSourceView2.source_buffer option)  ?draw_spaces =
  GtkSourceView2.SourceView.make_params [] ~cont:(
    GtkText.View.make_params ~cont:(
      GContainer.pack_container ~create:
	(fun pl -> let w = match source_buffer with
	  | None -> GtkSourceView2.SourceView.new_ ()
	  | Some buf -> GtkSourceView2.SourceView.new_with_buffer
            (Gobject.try_cast buf#as_buffer "GtkSourceBuffer") in
          let w = Gobject.unsafe_cast w in
		   Gobject.set_params (Gobject.try_cast w "GtkSourceView") pl;
		   Gaux.may (GtkSourceView2.SourceView.set_draw_spaces w) draw_spaces;
		   ((new script_view w) : script_view))))
