(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
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

let get_completion (buffer : GText.buffer) coqtop w handle_res =
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
  let get_semantic accu =
    let flags = [Interface.Name_Pattern ("^" ^ w), true] in
    let query h k =
      Coq.search flags h
	(function
	  | Interface.Good l ->
	    let fold accu elt =
              let rec last accu = function
		| [] -> accu
		| [basename] -> Proposals.add basename accu
		| _ :: l -> last accu l
              in
              last accu elt.Interface.coq_object_qualid
	    in
	    handle_res (List.fold_left fold accu l) k
	  | _ -> handle_res accu k)
    in
    Coq.try_grab coqtop query ignore;
  in
  get_semantic (get_aux Proposals.empty buffer#start_iter)

class script_view (tv : source_view) (ct : Coq.coqtop) =
object (self)
  inherit GSourceView2.source_view (Gobject.unsafe_cast tv) as super

  val mutable history = []
  val mutable redo = []
  val mutable auto_complete = false
  val mutable auto_complete_length = 3
  val mutable last_completion = (-1, "", Proposals.empty)
  (* this variable prevents CoqIDE from autocompleting when we have deleted something *)
  val mutable is_auto_completing = false

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
      Minilib.log "==========Undo Stack top=============";
      List.iter iter history;
      Printf.eprintf "Stack size %d\n" (List.length history);
      Minilib.log "==========Undo Stack Bottom==========";
      Minilib.log "==========Redo Stack start=============";
      List.iter iter redo;
      Printf.eprintf "Stack size %d\n" (List.length redo);
      Minilib.log "==========Redo Stack End=========="
    end

  method recenter_insert =
    self#scroll_to_mark
      ~use_align:false ~yalign:0.75 ~within_margin:0.25 `INSERT

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
    Minilib.log "UNDO";
    let effective = self#process_action history in
    if effective then self#backward ()

  method redo () =
    Minilib.log "REDO";
    let effective = self#process_action redo in
    if effective then self#forward ()

  method private handle_insert iter s =
    (* we're inserting, so we may autocomplete *)
    is_auto_completing <- true;
    (* Save the insert action *)
    let action = Insert (s, iter#offset, Glib.Utf8.length s) in
    history <- action :: history;
    redo <- [];
    self#dump_debug ()

  method private handle_delete ~start ~stop =
    (* disable autocomplete *)
    is_auto_completing <- false;
    (* Save the delete action *)
    let start_offset = start#offset in
    let stop_offset = stop#offset in
    let s = self#buffer#get_text ~start ~stop () in
    let action = Delete (s, start_offset, stop_offset - start_offset) in
    history <- action :: history;
    redo <- [];
    self#dump_debug ();

  method private do_auto_complete () =
    let iter = self#buffer#get_iter `INSERT in
    Minilib.log ("Completion at offset: " ^ string_of_int iter#offset);
    let start = find_word_start iter in
    if ends_word iter#backward_char then begin
      let w = self#buffer#get_text ~start ~stop:iter () in
      if String.length w >= auto_complete_length then begin
        Minilib.log ("Completion of prefix: '" ^ w ^ "'");
        let (off, prefix, proposals) = last_completion in
	let handle_proposals isnew new_proposals k =
	  if isnew then last_completion <- (start#offset, w, new_proposals);
          let prop =
            try Some (Proposals.choose new_proposals)
            with Not_found -> None
          in
          match prop with
            | None -> k ()
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
              self#buffer#select_range sel ins;
	      k ()
	in
        (* check whether we have the last request in cache *)
        if (start#offset = off) && (0 <= is_substring prefix w) then
          handle_proposals false
	    (Proposals.filter (fun p -> 0 < is_substring w p) proposals)
	    (fun () -> ())
        else
	  get_completion self#buffer ct w (handle_proposals true)
      end
    end

  method private may_auto_complete () =
    if auto_complete && is_auto_completing then self#do_auto_complete ()

  (* HACK: missing gtksourceview features *)
  method right_margin_position =
    let prop = {
      Gobject.name = "right-margin-position";
      conv = Gobject.Data.int;
    } in
    Gobject.get prop obj

  method set_right_margin_position pos =
    let prop = {
      Gobject.name = "right-margin-position";
      conv = Gobject.Data.int;
    } in
    Gobject.set prop obj pos

  method show_right_margin =
    let prop = {
      Gobject.name = "show-right-margin";
      conv = Gobject.Data.boolean;
    } in
    Gobject.get prop obj

  method set_show_right_margin show =
    let prop = {
      Gobject.name = "show-right-margin";
      conv = Gobject.Data.boolean;
    } in
    Gobject.set prop obj show

  method comment () =
    let rec get_line_start iter =
      if iter#starts_line then iter
      else get_line_start iter#backward_char
    in
    let (start, stop) =
      if self#buffer#has_selection then
        self#buffer#selection_bounds
      else
        let insert = self#buffer#get_iter `INSERT in
        (get_line_start insert, insert#forward_to_line_end)
    in
      let stop_mark = self#buffer#create_mark ~left_gravity:false stop in
      let () = self#buffer#begin_user_action () in
      let was_inserted = self#buffer#insert_interactive ~iter:start "(* " in
      let stop = self#buffer#get_iter_at_mark (`MARK stop_mark) in
      let () = if was_inserted then ignore (self#buffer#insert_interactive ~iter:stop " *)") in
      let () = self#buffer#end_user_action () in
      self#buffer#delete_mark (`MARK stop_mark)

  method uncomment () =
    let rec get_left_iter depth (iter : GText.iter) =
      let prev_close = iter#backward_search "*)" in
      let prev_open = iter#backward_search "(*" in
      let prev_object = match prev_close, prev_open with
      | None, None | Some _, None -> `NONE
      | None, Some (po, _) -> `OPEN po
      | Some (co, _), Some (po, _) -> if co#compare po < 0 then `OPEN po else `CLOSE co
      in
      match prev_object with
      | `NONE -> None
      | `OPEN po ->
        if depth <= 0 then Some po
        else get_left_iter (pred depth) po
      | `CLOSE co ->
        get_left_iter (succ depth) co
    in
    let rec get_right_iter depth (iter : GText.iter) =
      let next_close = iter#forward_search "*)" in
      let next_open = iter#forward_search "(*" in
      let next_object = match next_close, next_open with
      | None, None | None, Some _ -> `NONE
      | Some (_, co), None -> `CLOSE co
      | Some (_, co), Some (_, po) ->
        if co#compare po > 0 then `OPEN po else `CLOSE co
      in
      match next_object with
      | `NONE -> None
      | `OPEN po ->
        get_right_iter (succ depth) po
      | `CLOSE co ->
        if depth <= 0 then Some co
        else get_right_iter (pred depth) co
    in
    let insert = self#buffer#get_iter `INSERT in
    let left_elt = get_left_iter 0 insert in
    let right_elt = get_right_iter 0 insert in
    match left_elt, right_elt with
    | Some liter, Some riter ->
      let stop_mark = self#buffer#create_mark ~left_gravity:false riter in
      (* We remove one trailing/leading space if it exists *)
      let lcontent = self#buffer#get_text ~start:liter ~stop:(liter#forward_chars 3) () in
      let rcontent = self#buffer#get_text ~start:(riter#backward_chars 3) ~stop:riter () in
      let llen = if lcontent = "(* " then 3 else 2 in
      let rlen = if rcontent = " *)" then 3 else 2 in
      (* Atomic operation for the user *)
      let () = self#buffer#begin_user_action () in
      let was_deleted = self#buffer#delete_interactive ~start:liter ~stop:(liter#forward_chars llen) () in
      let riter = self#buffer#get_iter_at_mark (`MARK stop_mark) in
      if was_deleted then ignore (self#buffer#delete_interactive ~start:(riter#backward_chars rlen) ~stop:riter ());
      let () = self#buffer#end_user_action () in
      self#buffer#delete_mark (`MARK stop_mark)
    | _ -> ()

  initializer
    (* Install undo managing *)
    ignore (self#buffer#connect#insert_text ~callback:self#handle_insert);
    ignore (self#buffer#connect#delete_range ~callback:self#handle_delete);
    (* Install auto-completion *)
    ignore (self#buffer#connect#after#end_user_action ~callback:self#may_auto_complete);
    (* HACK: Redirect the undo/redo signals of the underlying GtkSourceView *)
    ignore (self#connect#undo
	      ~callback:(fun _ -> ignore (self#undo ()); GtkSignal.stop_emit()));
    ignore (self#connect#redo
	      ~callback:(fun _ -> ignore (self#redo ()); GtkSignal.stop_emit()));
    (* HACK: Redirect the move_line signal of the underlying GtkSourceView *)
    let move_line_marshal = GtkSignal.marshal2
      Gobject.Data.boolean Gobject.Data.int "move_line_marshal"
    in
    let move_line_signal = {
      GtkSignal.name = "move-lines";
      classe = Obj.magic 0;
      marshaller = move_line_marshal; }
    in
    let callback b i =
      let rec start_line iter =
        if iter#starts_line then iter
        else start_line iter#backward_char
      in
      let iter = start_line (self#buffer#get_iter `INSERT) in
      (* do we forward the signal? *)
      let proceed =
        if not b && i = 1 then
          iter#editable ~default:true &&
	  iter#forward_line#editable ~default:true
        else if not b && i = -1 then
          iter#editable ~default:true &&
	  iter#backward_line#editable ~default:true
        else false
      in
      if not proceed then GtkSignal.stop_emit ()
    in
    ignore(GtkSignal.connect ~sgn:move_line_signal ~callback obj);
    ()

end

let script_view ct ?(source_buffer:GSourceView2.source_buffer option)  ?draw_spaces =
  GtkSourceView2.SourceView.make_params [] ~cont:(
    GtkText.View.make_params ~cont:(
      GContainer.pack_container ~create:
	(fun pl ->
	  let w = match source_buffer with
	    | None -> GtkSourceView2.SourceView.new_ ()
	    | Some buf -> GtkSourceView2.SourceView.new_with_buffer
              (Gobject.try_cast buf#as_buffer "GtkSourceBuffer")
	  in
	  let w = Gobject.unsafe_cast w in
	  Gobject.set_params (Gobject.try_cast w "GtkSourceView") pl;
	  Gaux.may ~f:(GtkSourceView2.SourceView.set_draw_spaces w) draw_spaces;
	  ((new script_view w ct) : script_view))))
