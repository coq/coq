(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Ideutils
open GText
open Gtk_parsing

type action =
  | Insert of string * int * int (* content*pos*length *)
  | Delete of string * int * int (* content*pos*length *)

let neg act = match act with
  | Insert (s,i,l) -> Delete (s,i,l)
  | Delete (s,i,l) -> Insert (s,i,l)

type source_view = [ Gtk.text_view | `sourceview ] Gtk.obj

let is_substring s1 s2 =
  let s1 = Glib.Utf8.to_unistring s1 in
  let s2 = Glib.Utf8.to_unistring s2 in
  let break = ref true in
  let i = ref 0 in
  let len1 = Array.length s1 in
  let len2 = Array.length s2 in
  while !break && !i < len1 & !i < len2 do
    break := s1.(!i) = s2.(!i);
    incr i;
  done;
  if !break then len2 - len1
  else -1

module StringOrd =
struct
  type t = string
  let compare = Pervasives.compare
end

module Proposals = Set.Make(StringOrd)

let get_completion (buffer : GText.buffer) w =
  let rec get_aux accu (iter : GText.iter) =
    match iter#forward_search w with
    | None -> accu
    | Some (start, stop) ->
      if starts_word start then
        let ne = find_word_end stop in
        if ne#compare stop = 0 then get_aux accu stop
        else
          let proposal = buffer#get_text ~start ~stop:ne () in
          get_aux (Proposals.add proposal accu) stop
      else get_aux accu stop
  in
  get_aux Proposals.empty buffer#start_iter

class script_view (tv : source_view) =
object (self)
  inherit GSourceView2.source_view (Gobject.unsafe_cast tv) as super

  val mutable history = []
  val mutable redo = []
  val mutable auto_complete = false
  val mutable auto_complete_length = 3
  val mutable last_completion = (-1, "", Proposals.empty)

  val undo_lock = Mutex.create ()

  method auto_complete = auto_complete

  method set_auto_complete flag =
    auto_complete <- flag

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

  method private do_auto_complete () =
    let iter = self#buffer#get_iter `INSERT in
    prerr_endline ("Completion at offset: " ^ string_of_int iter#offset);
    let start = find_word_start iter in
    if ends_word iter#backward_char then begin
      let w = self#buffer#get_text ~start ~stop:iter () in
      if String.length w >= auto_complete_length then begin
        prerr_endline ("Completion of prefix: '" ^ w ^ "'");
        let (off, prefix, proposals) = last_completion in
        let new_proposals = 
        (* check whether we have the last request in cache *)
          if (start#offset = off) && (0 <= is_substring prefix w) then
            Proposals.filter (fun p -> 0 < is_substring w p) proposals
          else
            let ans = get_completion self#buffer w in
            let () = last_completion <- (start#offset, w, ans) in
            ans
        in
        let prop =
          try Some (Proposals.choose new_proposals)
          with Not_found -> None
        in
        match prop with
        | None -> ()
        | Some proposal ->
          let suffix =
            let len1 = String.length proposal in
            let len2 = String.length w in
            String.sub proposal len2 (len1 - len2)
          in
          let offset = iter#offset in
          ignore (self#buffer#delete_selection ());
          ignore (self#buffer#insert_interactive suffix);
          let ins = self#buffer#get_iter (`OFFSET offset) in
          let sel = self#buffer#get_iter `INSERT in
          self#buffer#select_range sel ins
      end
    end

  method private may_auto_complete iter s =
    if auto_complete then self#do_auto_complete ()

  initializer
    (* Install undo managing *)
    ignore (self#buffer#connect#insert_text ~callback:self#handle_insert);
    ignore (self#buffer#connect#delete_range ~callback:self#handle_delete);
    (* Install auto-completion *)
    ignore (self#buffer#connect#after#insert_text ~callback:self#may_auto_complete);
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
