(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Preferences

let prefs = Preferences.current

(** A session is a script buffer + proof + messages,
    interacting with a coqtop, and a few other elements around *)

type session = {
  buffer : GText.buffer;
  script : Wg_ScriptView.script_view;
  proof : Wg_ProofView.proof_view;
  messages : Wg_MessageView.message_view;
  fileops : FileOps.ops;
  coqops : CoqOps.ops;
  coqtop : Coq.coqtop;
  command : Wg_Command.command_window;
  finder : Wg_Find.finder;
  tab_label : GMisc.label;
}

let create_buffer () =
  let buffer = GSourceView2.source_buffer
    ~tag_table:Tags.Script.table
    ~highlight_matching_brackets:true
    ?language:(lang_manager#language prefs.source_language)
    ?style_scheme:(style_manager#style_scheme prefs.source_style)
    ()
  in
  let _ = buffer#create_mark ~name:"start_of_input" buffer#start_iter in
  let _ = buffer#create_mark
    ~left_gravity:false ~name:"stop_of_input" buffer#end_iter in
  let _ = buffer#create_mark ~name:"prev_insert" buffer#start_iter in
  let _ = buffer#place_cursor ~where:buffer#start_iter in
  let _ = buffer#add_selection_clipboard Ideutils.cb in
  buffer

let create_script coqtop source_buffer =
  let script = Wg_ScriptView.script_view coqtop ~source_buffer
    ~show_line_numbers:true ~wrap_mode:`NONE ()
  in
  let _ = script#misc#set_name "ScriptWindow"
  in
  script

(** NB: Events during text edition:

    - [begin_user_action]
    - [insert_text] (or [delete_range] when deleting)
    - [changed]
    - [end_user_action]

   When pasting a text containing tags (e.g. the sentence terminators),
   there is actually many [insert_text] and [changed]. For instance,
   for "a. b.":

    - [begin_user_action]
    - [insert_text] (for "a")
    - [changed]
    - [insert_text] (for ".")
    - [changed]
    - [apply_tag] (for the tag of ".")
    - [insert_text] (for " b")
    - [changed]
    - [insert_text] (for ".")
    - [changed]
    - [apply_tag] (for the tag of ".")
    - [end_user_action]

  Since these copy-pasted tags may interact badly with the retag mechanism,
  we now don't monitor the "changed" event, but rather the "begin_user_action"
  and "end_user_action". We begin by setting a mark at the initial cursor
  point. At the end, the zone between the mark and the cursor is to be
  untagged and then retagged. *)

let set_buffer_handlers
  (buffer : GText.buffer) script (coqops : CoqOps.ops) coqtop
=
  let action_was_cancelled = ref true in
  let no_coq_action_required = ref true in
  let cur_action = ref 0 in
  let new_action_id =
    let id = ref 0 in
    fun () -> incr id; !id in
  let running_action = ref None in
  let cancel_signal reason =
    Minilib.log ("user_action cancelled: "^reason);
    action_was_cancelled := true;
    GtkSignal.stop_emit () in
  let del_mark () =
    try buffer#delete_mark (`NAME "target")
    with GText.No_such_mark _ -> () in
  let add_mark it = del_mark (); buffer#create_mark ~name:"target" it in
  let call_coq_or_cancel_action f =
    no_coq_action_required := false;
    let action = !cur_action in
    let action, fallback =
      Coq.seq (Coq.lift (fun () -> running_action := Some action)) f,
      fun () -> (* If Coq is busy due to the current action, we don't cancel *)
        match !running_action with
        | Some aid when aid = action -> ()
        | _ -> cancel_signal "Coq busy" in
    Coq.try_grab coqtop action fallback in
  let get_start () = buffer#get_iter_at_mark (`NAME "start_of_input") in
  let get_stop () = buffer#get_iter_at_mark (`NAME "stop_of_input") in
  let ensure_marks_exist () =
    try ignore(buffer#get_mark (`NAME "stop_of_input"))
    with GText.No_such_mark _ -> assert false in
  let get_insert () = buffer#get_iter_at_mark `INSERT in
  let debug_edit_zone () = if !Minilib.debug then begin
    buffer#remove_tag Tags.Script.edit_zone
      ~start:buffer#start_iter ~stop:buffer#end_iter;
    buffer#apply_tag Tags.Script.edit_zone
      ~start:(get_start()) ~stop:(get_stop())
    end in
  let backto_before_error it =
    let rec aux old it =
      if it#is_start || not(it#has_tag Tags.Script.error_bg) then old
      else aux it it#backward_char in
    aux it it in
  let insert_cb it s = if String.length s = 0 then () else begin
    Minilib.log ("insert_cb " ^ string_of_int it#offset);
    let text_mark = add_mark it in
    if it#has_tag Tags.Script.to_process then
      cancel_signal "Altering the script being processed in not implemented"
    else if it#has_tag Tags.Script.read_only then
      cancel_signal "Altering read_only text not allowed"
    else if it#has_tag Tags.Script.processed then
      call_coq_or_cancel_action (coqops#go_to_mark (`MARK text_mark))
    else if it#has_tag Tags.Script.error_bg then begin
      let prev_sentence_end = backto_before_error it in
      let text_mark = add_mark prev_sentence_end in
      call_coq_or_cancel_action (coqops#go_to_mark (`MARK text_mark))
    end end in
  let delete_cb ~start ~stop =
    Minilib.log (Printf.sprintf "delete_cb %d %d" start#offset stop#offset);
    cur_action := new_action_id ();
    let min_iter, max_iter =
      if start#compare stop < 0 then start, stop else stop, start in
    let text_mark = add_mark min_iter in
    let rec aux min_iter =
      if min_iter#equal max_iter then ()
      else if min_iter#has_tag Tags.Script.to_process then
        cancel_signal "Altering the script being processed in not implemented"
      else if min_iter#has_tag Tags.Script.read_only then
        cancel_signal "Altering read_only text not allowed"
      else if min_iter#has_tag Tags.Script.processed then
        call_coq_or_cancel_action (coqops#go_to_mark (`MARK text_mark))
      else if min_iter#has_tag Tags.Script.error_bg then
        let prev_sentence_end = backto_before_error min_iter in
        let text_mark = add_mark prev_sentence_end in
        call_coq_or_cancel_action (coqops#go_to_mark (`MARK text_mark))
      else aux min_iter#forward_char in
    aux min_iter in
  let begin_action_cb () =
    Minilib.log "begin_action_cb";
    action_was_cancelled := false;
    cur_action := new_action_id ();
    let where = get_insert () in
    buffer#move_mark (`NAME "prev_insert") ~where in
  let end_action_cb () =
    Minilib.log "end_action_cb";
    ensure_marks_exist ();
    if not !action_was_cancelled then begin
      (* If coq was asked to backtrack, the clenup must be done by the
         backtrack_until function, since it may move the stop_of_input
         to a point indicated by coq. *)
      if !no_coq_action_required then begin
        let start, stop = get_start (), get_stop () in
        buffer#remove_tag Tags.Script.error ~start ~stop;
        buffer#remove_tag Tags.Script.error_bg ~start ~stop;
        buffer#remove_tag Tags.Script.tooltip ~start ~stop;
        buffer#remove_tag Tags.Script.processed ~start ~stop;
        buffer#remove_tag Tags.Script.to_process ~start ~stop;
      end;
      Sentence.tag_on_insert buffer
    end in
  let mark_deleted_cb m =
    match GtkText.Mark.get_name m with
    | Some "insert" -> ()
    | Some s -> Minilib.log (s^" deleted")
    | None -> ()
  in
  let mark_set_cb it m =
    debug_edit_zone ();
    let ins = get_insert () in
    let line = ins#line + 1 in
    let off = ins#line_offset + 1 in
    let msg = Printf.sprintf "Line: %5d Char: %3d" line off in
    let () = !Ideutils.set_location msg in
    match GtkText.Mark.get_name m with
    | Some "insert" -> ()
    | Some s -> Minilib.log (s^" moved")
    | None -> ()
  in
  (** Pluging callbacks *)
  let _ = buffer#connect#insert_text ~callback:insert_cb in
  let _ = buffer#connect#delete_range ~callback:delete_cb in
  let _ = buffer#connect#begin_user_action ~callback:begin_action_cb in
  let _ = buffer#connect#end_user_action ~callback:end_action_cb in
  let _ = buffer#connect#after#mark_set ~callback:mark_set_cb in
  let _ = buffer#connect#after#mark_deleted ~callback:mark_deleted_cb in
  ()

let create_proof () =
  let proof = Wg_ProofView.proof_view () in
  let _ = proof#misc#set_can_focus true in
  let _ = GtkBase.Widget.add_events proof#as_widget
    [`ENTER_NOTIFY;`POINTER_MOTION]
  in
  proof

let create_messages () =
  let messages = Wg_MessageView.message_view () in
  let _ = messages#misc#set_can_focus true in
  messages

let create file coqtop_args =
  let basename = match file with
    |None -> "*scratch*"
    |Some f -> Glib.Convert.filename_to_utf8 (Filename.basename f)
  in
  let coqtop = Coq.spawn_coqtop coqtop_args in
  let reset () = Coq.reset_coqtop coqtop in
  let buffer = create_buffer () in
  let script = create_script coqtop buffer in
  let proof = create_proof () in
  let messages = create_messages () in
  let command = new Wg_Command.command_window basename coqtop in
  let finder = new Wg_Find.finder (script :> GText.view) in
  let fops = new FileOps.fileops (buffer :> GText.buffer) file reset in
  let _ = fops#update_stats in
  let cops =
    new CoqOps.coqops script proof messages coqtop (fun () -> fops#filename) in
  let _ = set_buffer_handlers (buffer :> GText.buffer) script cops coqtop in
  let _ = Coq.set_reset_handler coqtop cops#handle_reset_initial in
  let _ = Coq.init_coqtop coqtop cops#initialize in
  {
    buffer = (buffer :> GText.buffer);
    script=script;
    proof=proof;
    messages=messages;
    fileops=fops;
    coqops=cops;
    coqtop=coqtop;
    command=command;
    finder=finder;
    tab_label= GMisc.label ~text:basename ();
  }

let kill (sn:session) =
  (* To close the detached views of this script, we call manually
     [destroy] on it, triggering some callbacks in [detach_view].
     In a more modern lablgtk, rather use the page-removed signal ? *)
  sn.coqops#destroy ();
  sn.script#destroy ();
  Coq.close_coqtop sn.coqtop

let build_layout (sn:session) =
  let session_paned = GPack.paned `VERTICAL () in
  let session_box =
    GPack.vbox ~packing:(session_paned#pack1 ~shrink:false ~resize:true) ()
  in
  let eval_paned = GPack.paned `HORIZONTAL ~border_width:5
    ~packing:(session_box#pack ~expand:true) () in
  let script_frame = GBin.frame ~shadow_type:`IN
    ~packing:eval_paned#add1 () in
  let script_scroll = GBin.scrolled_window
    ~vpolicy:`AUTOMATIC ~hpolicy:`AUTOMATIC ~packing:script_frame#add () in
  let state_paned = GPack.paned `VERTICAL
    ~packing:eval_paned#add2 () in
  let proof_frame = GBin.frame ~shadow_type:`IN
    ~packing:state_paned#add1 () in
  let proof_scroll = GBin.scrolled_window
    ~vpolicy:`AUTOMATIC ~hpolicy:`AUTOMATIC ~packing:proof_frame#add () in
  let message_frame = GBin.frame ~shadow_type:`IN
    ~packing:state_paned#add2 () in
  let session_tab = GPack.hbox ~homogeneous:false () in
  let img = GMisc.image ~icon_size:`SMALL_TOOLBAR
    ~packing:session_tab#pack () in
  let _ =
    sn.buffer#connect#modified_changed
      ~callback:(fun () -> if sn.buffer#modified
        then img#set_stock `SAVE
        else img#set_stock `YES) in
  let _ =
    eval_paned#misc#connect#size_allocate
      ~callback:
      (let old_paned_width = ref 2 in
       let old_paned_height = ref 2 in
       fun {Gtk.width=paned_width;Gtk.height=paned_height} ->
         if !old_paned_width <> paned_width ||
            !old_paned_height <> paned_height
         then begin
           eval_paned#set_position
             (eval_paned#position * paned_width / !old_paned_width);
           state_paned#set_position
             (state_paned#position * paned_height / !old_paned_height);
           old_paned_width := paned_width;
           old_paned_height := paned_height;
	 end)
  in
  session_box#pack sn.finder#coerce;
  sn.command#pack_in (session_paned#pack2 ~shrink:false ~resize:false);
  script_scroll#add sn.script#coerce;
  proof_scroll#add sn.proof#coerce;
  message_frame#add sn.messages#coerce;
  session_tab#pack sn.tab_label#coerce;
  img#set_stock `YES;
  eval_paned#set_position 1;
  state_paned#set_position 1;
  (Some session_tab#coerce,None,session_paned#coerce)
