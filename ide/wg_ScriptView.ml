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

type insert_action = {
  ins_val : string;
  ins_off : int;
  ins_len : int;
  ins_mrg : bool;
}

type delete_action = {
  del_val : string; (** Contents *)
  del_off : int; (** Absolute offset of the modification *)
  del_len : int; (** Length *)
  del_mrg : bool; (** Is the modification mergeable? *)
}

type action =
  | Insert of insert_action
  | Delete of delete_action
  | Action of action list
  | EndGrp (** pending begin_user_action *)

let merge_insert ins = function
| Insert ins' :: rem ->
  if ins.ins_mrg && ins'.ins_mrg &&
    (ins'.ins_off + ins'.ins_len = ins.ins_off) then
    let nins = {
      ins_val = ins'.ins_val ^ ins.ins_val;
      ins_off = ins'.ins_off;
      ins_len = ins'.ins_len + ins.ins_len;
      ins_mrg = true;
    } in
    Insert nins :: rem
  else
    Insert ins :: Insert ins' :: rem
| l ->
  Insert ins :: l

let merge_delete del = function
| Delete del' :: rem ->
  if del.del_mrg && del'.del_mrg &&
    (del.del_off + del.del_len = del'.del_off) then
    let ndel = {
      del_val = del.del_val ^ del'.del_val;
      del_off = del.del_off;
      del_len = del.del_len + del'.del_len;
      del_mrg = true;
    } in
    Delete ndel :: rem
  else
  Delete del :: Delete del' :: rem
| l ->
  Delete del :: l

let rec negate_action act = match act with
  | Insert act ->
    let act = {
      del_len = act.ins_len;
      del_off = act.ins_off;
      del_val = act.ins_val;
      del_mrg = act.ins_mrg;
    } in
    Delete act
  | Delete act ->
    let act = {
      ins_len = act.del_len;
      ins_off = act.del_off;
      ins_val = act.del_val;
      ins_mrg = act.del_mrg;
    } in
    Insert act
  | Action acts ->
    Action (List.rev_map negate_action acts)
  | EndGrp -> assert false

type source_view = [ Gtk.text_view | `sourceview ] Gtk.obj

class undo_manager (buffer : GText.buffer) =
object(self)
  val mutable lock_undo = true
  val mutable history = []
  val mutable redo = []

  method with_lock_undo : 'a. ('a -> unit) -> 'a -> unit =
    fun f x ->
    if lock_undo then
      let () = lock_undo <- false in
      try (f x; lock_undo <- true)
      with e -> (lock_undo <- true; raise e)
    else ()

  method private dump_debug () =
    let rec iter = function
    | Insert act ->
      Printf.eprintf "Insert of '%s' at %d (length %d, mergeable %b)\n%!"
        act.ins_val act.ins_off act.ins_len act.ins_mrg
    | Delete act ->
      Printf.eprintf "Delete '%s' from %d (length %d, mergeable %b)\n%!"
        act.del_val act.del_off act.del_len act.del_mrg
    | Action l ->
      Printf.eprintf "Action\n%!";
      List.iter iter l;
      Printf.eprintf "//Action\n%!";
    | EndGrp ->
      Printf.eprintf "End Group\n%!"
    in
    if false (* !debug *) then begin
      Printf.eprintf "+++++++++++++++++++++++++++++++++++++\n%!";
      Printf.eprintf "==========Undo Stack top=============\n%!";
      List.iter iter history;
      Printf.eprintf "Stack size %d\n" (List.length history);
      Printf.eprintf "==========Undo Stack Bottom==========\n%!";
      Printf.eprintf "==========Redo Stack start===========\n%!";
      List.iter iter redo;
      Printf.eprintf "Stack size %d\n" (List.length redo);
      Printf.eprintf "==========Redo Stack End=============\n%!";
      Printf.eprintf "+++++++++++++++++++++++++++++++++++++\n%!";
    end

  method clear_undo () =
    history <- [];
    redo <- []

  (** Warning: processing actually undo the action *)
  method private process_insert_action ins =
    let start = buffer#get_iter (`OFFSET ins.ins_off) in
    let stop = start#forward_chars ins.ins_len in
    buffer#delete_interactive ~start ~stop ()

  method private process_delete_action del =
    let iter = buffer#get_iter (`OFFSET del.del_off) in
    buffer#insert_interactive ~iter del.del_val

  (** We don't care about atomicity. Return:
    1. `OK when there was no error, `FAIL otherwise
    2. `NOOP if no write occurred, `WRITE otherwise
  *)
  method private process_action = function
  | Insert ins ->
    if self#process_insert_action ins then (`OK, `WRITE) else (`FAIL, `NOOP)
  | Delete del ->
    if self#process_delete_action del then (`OK, `WRITE) else (`FAIL, `NOOP)
  | Action lst ->
    let fold accu action = match accu with
    | (`FAIL, _) -> accu (** we stop now! *)
    | (`OK, status) ->
      let (res, nstatus) = self#process_action action in
      let merge op1 op2 = match op1, op2 with
      | `NOOP, `NOOP -> `NOOP (** only a noop when both are *)
      | _ -> `WRITE
      in
      (res, merge status nstatus)
    in
    List.fold_left fold (`OK, `NOOP) lst
  | EndGrp -> assert false

  method perform_undo () = match history with
  | [] -> ()
  | action :: rem ->
    let ans = self#process_action action in
    begin match ans with
    | (`OK, _) ->
      history <- rem;
      redo <- (negate_action action) :: redo
    | (`FAIL, `NOOP) -> () (** we do nothing *)
    | (`FAIL, `WRITE) -> self#clear_undo () (** we don't know how we failed, so start off *)
    end

  method perform_redo () = match redo with
  | [] -> ()
  | action :: rem ->
    let ans = self#process_action action in
    begin match ans with
    | (`OK, _) ->
      redo <- rem;
      history <- (negate_action action) :: history;
    | (`FAIL, `NOOP) -> () (** we do nothing *)
    | (`FAIL, `WRITE) -> self#clear_undo () (** we don't know how we failed *)
    end

  method undo () =
    Minilib.log "UNDO";
    self#with_lock_undo begin fun () ->
      buffer#begin_user_action ();
      self#perform_undo ();
      buffer#end_user_action ()
    end ()

  method redo () =
    Minilib.log "REDO";
    self#with_lock_undo begin fun () ->
      buffer#begin_user_action ();
      self#perform_redo ();
      buffer#end_user_action ()
    end ()

  method process_begin_user_action () =
    (* Push a new level of event on history stack *)
    history <- EndGrp :: history

  method begin_user_action () =
    self#with_lock_undo self#process_begin_user_action ()

  method process_end_user_action () =
    (** Search for the pending action *)
    let rec split accu = function
    | [] -> raise Not_found (** no pending begin action! *)
    | EndGrp :: rem ->
      let grp = List.rev accu in
      let rec flatten = function
      | [] -> rem
      | [Insert ins] -> merge_insert ins rem
      | [Delete del] -> merge_delete del rem
      | [Action l] -> flatten l
      | _ -> Action grp :: rem
      in
      flatten grp
    | action :: rem ->
      split (action :: accu) rem
    in
    try (history <- split [] history; self#dump_debug ())
    with Not_found ->
      Minilib.log "Error: Badly parenthezised user action";
      self#clear_undo ()

  method end_user_action () =
    self#with_lock_undo self#process_end_user_action ()

  method private process_handle_insert iter s =
    (* Save the insert action *)
    let len = Glib.Utf8.length s in
    let mergeable =
      (** heuristic: split at newline and atomic pastes *)
      len = 1 && (s <> "\n")
    in
    let ins = {
      ins_val = s;
      ins_off = iter#offset;
      ins_len = len;
      ins_mrg = mergeable;
    } in
    let () = history <- Insert ins :: history in
    ()

  method private handle_insert iter s =
    self#with_lock_undo (self#process_handle_insert iter) s

  method private process_handle_delete start stop =
    (* Save the delete action *)
    let text = buffer#get_text ~start ~stop () in
    let len = Glib.Utf8.length text in
    let mergeable = len = 1  && (text <> "\n") in
    let del = {
      del_val = text;
      del_off = start#offset;
      del_len = stop#offset - start#offset;
      del_mrg = mergeable;
    } in
    let action = Delete del in
    history <- action :: history;
    redo <- [];

  method private handle_delete ~start ~stop =
    self#with_lock_undo (self#process_handle_delete start) stop

  initializer
    let _ = buffer#connect#after#begin_user_action ~callback:self#begin_user_action in
    let _ = buffer#connect#after#end_user_action ~callback:self#end_user_action in
    let _ = buffer#connect#insert_text ~callback:self#handle_insert in
    let _ = buffer#connect#delete_range ~callback:self#handle_delete in
    ()

end

class script_view (tv : source_view) (ct : Coq.coqtop) =

let view = new GSourceView2.source_view (Gobject.unsafe_cast tv) in
let completion = new Wg_Completion.complete_model ct view#buffer in
let popup = new Wg_Completion.complete_popup completion (view :> GText.view) in

object (self)
  inherit GSourceView2.source_view (Gobject.unsafe_cast tv)

  val undo_manager = new undo_manager view#buffer

  method auto_complete = completion#active

  method set_auto_complete flag =
    completion#set_active flag

  method recenter_insert =
    self#scroll_to_mark
      ~use_align:false ~yalign:0.75 ~within_margin:0.25 `INSERT

  (* HACK: missing gtksourceview features *)
  method! right_margin_position =
    let prop = {
      Gobject.name = "right-margin-position";
      conv = Gobject.Data.int;
    } in
    Gobject.get prop obj

  method! set_right_margin_position pos =
    let prop = {
      Gobject.name = "right-margin-position";
      conv = Gobject.Data.int;
    } in
    Gobject.set prop obj pos

  method! show_right_margin =
    let prop = {
      Gobject.name = "show-right-margin";
      conv = Gobject.Data.boolean;
    } in
    Gobject.get prop obj

  method! set_show_right_margin show =
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

  method complete_popup = popup

  method undo = undo_manager#undo
  method redo = undo_manager#redo
  method clear_undo = undo_manager#clear_undo

  method private paste () =
    let cb = GData.clipboard Gdk.Atom.clipboard in
    match cb#text with
    | None -> ()
    | Some text ->
      let () = self#buffer#begin_user_action () in
      let _ = self#buffer#delete_selection () in
      let _ = self#buffer#insert_interactive text in
      self#buffer#end_user_action ()

  initializer
    let () = Gtk_parsing.fix_double_click self in
    let supersed cb _ =
      let _ = cb () in
      GtkSignal.stop_emit()
    in
    (* HACK: Redirect the undo/redo signals of the underlying GtkSourceView *)
    let _ = self#connect#undo ~callback:(supersed self#undo) in
    let _ = self#connect#redo ~callback:(supersed self#redo) in
    (* HACK: Redirect the paste signal *)
    let _ = self#connect#paste_clipboard ~callback:(supersed self#paste) in
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
    let _ = GtkSignal.connect ~sgn:move_line_signal ~callback obj in
    (** Plug on preferences *)
    let cb clr = self#misc#modify_base [`NORMAL, `NAME clr] in
    let _ = background_color#connect#changed ~callback:cb in
    let _ = self#misc#connect#realize ~callback:(fun () -> cb background_color#get) in

    let cb b = self#set_wrap_mode (if b then `WORD else `NONE) in
    stick dynamic_word_wrap self cb;
    stick show_line_number self self#set_show_line_numbers;
    stick auto_indent self self#set_auto_indent;
    stick highlight_current_line self self#set_highlight_current_line;

    (* Hack to handle missing binding in lablgtk *)
    let cb b =
      let flag = if b then 0b1001011 (* SPACE, TAB, NBSP, TRAILING *) else 0 in
      let conv = Gobject.({ name = "draw-spaces"; conv = Data.int }) in
      Gobject.set conv self#as_widget flag
    in
    stick show_spaces self cb;

    stick show_right_margin self self#set_show_right_margin;
    stick spaces_instead_of_tabs self self#set_insert_spaces_instead_of_tabs;
    stick tab_length self self#set_tab_width;
    stick auto_complete self self#set_auto_complete;

    let cb ft = self#misc#modify_font (Pango.Font.from_string ft) in
    stick text_font self cb;

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
