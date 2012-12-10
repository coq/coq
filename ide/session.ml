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

type print_items =
    (Coq.PrintOpt.t list * string * string * string * bool) list

let create file coqtop_args print_items =
  let basename = match file with
    |None -> "*scratch*"
    |Some f -> Glib.Convert.filename_to_utf8 (Filename.basename f)
  in
  let coqtop = Coq.spawn_coqtop coqtop_args in
  let reset () = Coq.reset_coqtop coqtop
  in
  let buffer = GSourceView2.source_buffer
    ~tag_table:Tags.Script.table
    ~highlight_matching_brackets:true
    ?language:(lang_manager#language prefs.source_language)
    ?style_scheme:(style_manager#style_scheme prefs.source_style)
    ()
  in
  let _ = buffer#create_mark ~name:"start_of_input" buffer#start_iter in
  let _ = buffer#create_mark ~name:"prev_insert" buffer#start_iter in
  let _ = buffer#place_cursor ~where:buffer#start_iter in
  let _ = buffer#add_selection_clipboard Ideutils.cb
  in
  let script = Wg_ScriptView.script_view coqtop ~source_buffer:buffer
    ~show_line_numbers:true ~wrap_mode:`NONE ()
  in
  let _ = script#misc#set_name "ScriptWindow"
  in
  let proof = Wg_ProofView.proof_view () in
  let _ = proof#misc#set_can_focus true in
  let _ =
    GtkBase.Widget.add_events proof#as_widget [`ENTER_NOTIFY;`POINTER_MOTION]
  in
  let messages = Wg_MessageView.message_view () in
  let _ = messages#misc#set_can_focus true
  in
  let command = new Wg_Command.command_window coqtop in
  let finder = new Wg_Find.finder (script :> GText.view) in
  let fops = new FileOps.fileops (buffer :> GText.buffer) file reset in
  let cops = new CoqOps.coqops script proof messages (fun () -> fops#filename)
  in
  let _ = Coq.set_reset_handler coqtop cops#handle_reset_initial in
  let _ = fops#update_stats in
  let _ = Coq.init_coqtop coqtop
    (fun h k ->
      cops#include_file_dir_in_path h
        (fun () ->
          let fold accu (opts, _, _, _, dflt) =
            List.fold_left (fun accu opt -> (opt, dflt) :: accu) accu opts
          in
          let options = List.fold_left fold [] print_items in
          Coq.PrintOpt.set options h k))
  in
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
  let message_scroll = GBin.scrolled_window
    ~vpolicy:`AUTOMATIC ~hpolicy:`AUTOMATIC ~packing:message_frame#add () in
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
  session_paned#pack2 ~shrink:false ~resize:false (sn.command#frame#coerce);
  script_scroll#add sn.script#coerce;
  proof_scroll#add sn.proof#coerce;
  message_scroll#add sn.messages#coerce;
  session_tab#pack sn.tab_label#coerce;
  img#set_stock `YES;
  eval_paned#set_position 1;
  state_paned#set_position 1;
  (Some session_tab#coerce,None,session_paned#coerce)
