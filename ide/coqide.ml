(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Preferences
open Gtk_parsing
open Ideutils

type ide_info = {
  start : GText.mark;
  stop : GText.mark;
}

(** Have we used admit or declarative mode's daimon ?
    If yes, we color differently *)

type safety = Safe | Unsafe

let safety_tag = function
  | Safe -> Tags.Script.processed
  | Unsafe -> Tags.Script.unjustified

class type analyzed_views=
object
  val mutable act_id : GtkSignal.id option
  val mutable deact_id : GtkSignal.id option
  val input_buffer : GText.buffer
  val input_view : Undo.undoable_view
  val last_array : string array
  val mutable last_index : bool
  val message_buffer : GText.buffer
  val message_view : GText.view
  val proof_buffer : GText.buffer
  val proof_view : GText.view
  val cmd_stack : ide_info Stack.t
  val mycoqtop : Coq.coqtop ref
  val mutable is_active : bool
  val mutable read_only : bool
  val mutable filename : string option
  val mutable stats : Unix.stats option
  val mutable detached_views : GWindow.window list
  method without_auto_complete : 'a 'b. ('a -> 'b) -> 'a -> 'b
  method set_auto_complete : bool -> unit

  method kill_detached_views : unit -> unit
  method add_detached_view : GWindow.window -> unit
  method remove_detached_view : GWindow.window -> unit

  method filename : string option
  method stats :  Unix.stats option
  method update_stats : unit
  method revert : unit
  method auto_save : unit
  method save : string -> bool
  method save_as : string -> bool
  method read_only : bool
  method set_read_only : bool -> unit
  method is_active : bool
  method activate : unit -> unit
  method active_keypress_handler : GdkEvent.Key.t -> bool
  method backtrack_to : GText.iter -> unit
  method backtrack_to_no_lock : GText.iter -> unit
  method clear_message : unit
  method disconnected_keypress_handler : GdkEvent.Key.t -> bool
  method find_phrase_starting_at :
    GText.iter -> (GText.iter * GText.iter) option
  method get_insert : GText.iter
  method get_start_of_input : GText.iter
  method go_to_insert : unit
  method indent_current_line : unit
  method go_to_next_occ_of_cur_word : unit
  method go_to_prev_occ_of_cur_word : unit
  method insert_command : string -> string -> unit
  method tactic_wizard : string list -> unit
  method insert_message : string -> unit
  method process_next_phrase : bool -> unit
  method process_until_iter_or_error : GText.iter -> unit
  method process_until_end_or_error : unit
  method recenter_insert : unit
  method reset_initial : unit
  method force_reset_initial : unit
  method set_message : string -> unit
  method show_goals : unit
  method show_goals_full : unit
  method undo_last_step : unit
  method help_for_keyword : unit -> unit
  method complete_at_offset : int -> bool
end


type viewable_script =
    {script : Undo.undoable_view;
     tab_label : GMisc.label;
     mutable filename : string;
     mutable encoding : string;
     proof_view : GText.view;
     message_view : GText.view;
     analyzed_view : analyzed_views;
     toplvl : Coq.coqtop ref;
     command : Command_windows.command_window;
    }

let kill_session s =
  s.analyzed_view#kill_detached_views ();
  Coq.kill_coqtop !(s.toplvl)

let build_session s =
  let session_paned = GPack.paned `VERTICAL () in
  let eval_paned = GPack.paned `HORIZONTAL ~border_width:5
    ~packing:(session_paned#pack1 ~shrink:false ~resize:true) () in
  let script_frame = GBin.frame ~shadow_type:`IN
    ~packing:eval_paned#add1 () in
  let script_scroll = GBin.scrolled_window ~vpolicy:`AUTOMATIC ~hpolicy:`AUTOMATIC
    ~packing:script_frame#add () in
  let state_paned = GPack.paned `VERTICAL
    ~packing:eval_paned#add2 () in
  let proof_frame = GBin.frame ~shadow_type:`IN
    ~packing:state_paned#add1 () in
  let proof_scroll = GBin.scrolled_window ~vpolicy:`AUTOMATIC ~hpolicy:`AUTOMATIC
    ~packing:proof_frame#add () in
  let message_frame = GBin.frame ~shadow_type:`IN
    ~packing:state_paned#add2 () in
  let message_scroll = GBin.scrolled_window ~vpolicy:`AUTOMATIC ~hpolicy:`AUTOMATIC
    ~packing:message_frame#add () in
  let session_tab = GPack.hbox ~homogeneous:false () in
  let img = GMisc.image ~icon_size:`SMALL_TOOLBAR
    ~packing:session_tab#pack () in
  let _ =
    s.script#buffer#connect#modified_changed
      ~callback:(fun () -> if s.script#buffer#modified
        then img#set_stock `SAVE
        else img#set_stock `YES) in
  let _ =
    eval_paned#misc#connect#size_allocate
      ~callback:
      (let old_paned_width = ref 2 in
       let old_paned_height = ref 2 in
       (fun {Gtk.width=paned_width;Gtk.height=paned_height} ->
	 if !old_paned_width <> paned_width || !old_paned_height <> paned_height then (
	   eval_paned#set_position (eval_paned#position * paned_width / !old_paned_width);
	   state_paned#set_position (state_paned#position * paned_height / !old_paned_height);
	   old_paned_width := paned_width;
	   old_paned_height := paned_height;
	 )))
  in
  session_paned#pack2 ~shrink:false ~resize:false (s.command#frame#coerce);
  script_scroll#add s.script#coerce;
  proof_scroll#add s.proof_view#coerce;
  message_scroll#add s.message_view#coerce;
  session_tab#pack s.tab_label#coerce;
  img#set_stock `YES;
  eval_paned#set_position 1;
  state_paned#set_position 1;
  (Some session_tab#coerce,None,session_paned#coerce)

let session_notebook =
  Typed_notebook.create build_session kill_session
    ~border_width:2 ~show_border:false ~scrollable:true ()

let cb = GData.clipboard Gdk.Atom.primary

let last_cb_content = ref ""

let update_notebook_pos () =
  let pos =
    match !current.vertical_tabs, !current.opposite_tabs with
      | false, false -> `TOP
      | false, true  -> `BOTTOM
      | true , false -> `LEFT
      | true , true  -> `RIGHT
  in
  session_notebook#set_tab_pos pos

let to_do_on_page_switch = ref []


(** * Coqide's handling of signals *)

(** We ignore Ctrl-C, and for most of the other catchable signals
    we launch an emergency save of opened files and then exit *)

let signals_to_crash = [Sys.sigabrt; Sys.sigalrm; Sys.sigfpe; Sys.sighup;
			Sys.sigill; Sys.sigpipe; Sys.sigquit;
			(* Sys.sigsegv; Sys.sigterm;*) Sys.sigusr2]

let crash_save i =
  (*  ignore (Unix.sigprocmask Unix.SIG_BLOCK signals_to_crash);*)
  Minilib.safe_prerr_endline "Trying to save all buffers in .crashcoqide files";
  let count = ref 0 in
  List.iter
    (function {script=view; analyzed_view = av } ->
      (let filename = match av#filename with
	| None ->
	  incr count;
	  "Unnamed_coqscript_"^(string_of_int !count)^".crashcoqide"
	| Some f -> f^".crashcoqide"
       in
       try
	 if try_export filename (view#buffer#get_text ()) then
	   Minilib.safe_prerr_endline ("Saved "^filename)
	 else Minilib.safe_prerr_endline ("Could not save "^filename)
       with _ -> Minilib.safe_prerr_endline ("Could not save "^filename))
    )
    session_notebook#pages;
  Minilib.safe_prerr_endline "Done. Please report.";
  if i <> 127 then exit i

let ignore_break () =
  List.iter
    (fun i ->
      try Sys.set_signal i (Sys.Signal_handle crash_save)
      with _ -> prerr_endline "Signal ignored (normal if Win32)")
    signals_to_crash;
  Sys.set_signal Sys.sigint Sys.Signal_ignore


(** * Locks *)

(* Locking machinery for Coq kernel *)
let coq_computing = Mutex.create ()

(* To prevent Coq from interrupting during undoing...*)
let coq_may_stop = Mutex.create ()

(* To prevent a force_reset_initial during a force_reset_initial *)
let resetting = Mutex.create ()

exception RestartCoqtop
exception Unsuccessful

let force_reset_initial () =
  prerr_endline "Reset Initial";
  session_notebook#current_term.analyzed_view#force_reset_initial

let break () =
  prerr_endline "User break received";
  Coq.break_coqtop !(session_notebook#current_term.toplvl)

let do_if_not_computing text f x =
  let threaded_task () =
    if Mutex.try_lock coq_computing then
      begin
	prerr_endline "Getting lock";
	List.iter
          (fun elt -> try f elt with
            | RestartCoqtop -> elt.analyzed_view#reset_initial
            | Sys_error str ->
              elt.analyzed_view#reset_initial;
              elt.analyzed_view#set_message
                ("Unable to communicate with coqtop, restarting coqtop.\n"^
		    "Error was: "^str)
            | e ->
              Mutex.unlock coq_computing;
              elt.analyzed_view#set_message
                ("Unknown error, please report:\n"^(Printexc.to_string e)))
          x;
	prerr_endline "Releasing lock";
	Mutex.unlock coq_computing;
      end
    else
      prerr_endline "Discarded order (computations are ongoing)"
  in
  prerr_endline ("Launching thread " ^ text);
  ignore (Glib.Timeout.add ~ms:300 ~callback:
            (fun () -> if Mutex.try_lock coq_computing
              then (Mutex.unlock coq_computing; false)
              else (pbar#pulse (); true)));
  ignore (Thread.create threaded_task ())

let warning msg =
  GToolbox.message_box ~title:"Warning"
    ~icon:(let img = GMisc.image () in
	   img#set_stock `DIALOG_WARNING;
	   img#set_icon_size `DIALOG;
	   img#coerce)
    msg

let remove_current_view_page () =
  let do_remove () =
    let c = session_notebook#current_page in
    session_notebook#remove_page c
  in
  let current = session_notebook#current_term in
  if not current.script#buffer#modified then do_remove ()
  else
    match GToolbox.question_box ~title:"Close"
      ~buttons:["Save Buffer and Close";
                "Close without Saving";
                "Don't Close"]
      ~default:0
      ~icon:(let img = GMisc.image () in
             img#set_stock `DIALOG_WARNING;
             img#set_icon_size `DIALOG;
             img#coerce)
      "This buffer has unsaved modifications"
    with
      | 1 ->
        begin match current.analyzed_view#filename with
          | None ->
            begin match select_file_for_save ~title:"Save file" () with
              | None -> ()
              | Some f ->
                if current.analyzed_view#save_as f then begin
                  flash_info ("File " ^ f ^ " saved") ;
                  do_remove ()
                end else
                  warning  ("Save Failed (check if " ^ f ^ " is writable)")
            end
          | Some f ->
            if current.analyzed_view#save f then begin
              flash_info ("File " ^ f ^ " saved") ;
              do_remove ()
            end else
              warning  ("Save Failed (check if " ^ f ^ " is writable)")
        end
      | 2 -> do_remove ()
      | _ -> ()

module Opt = Coq.PrintOpt

let print_items = [
  ([Opt.implicit],"Display implicit arguments","Display _implicit arguments",
   "i",false);
  ([Opt.coercions],"Display coercions","Display _coercions","c",false);
  ([Opt.raw_matching],"Display raw matching expressions",
   "Display raw _matching expressions","m",true);
  ([Opt.notations],"Display notations","Display _notations","n",true);
  ([Opt.all_basic],"Display all basic low-level contents",
   "Display _all basic low-level contents","a",false);
  ([Opt.existential],"Display existential variable instances",
   "Display _existential variable instances","e",false);
  ([Opt.universes],"Display universe levels","Display _universe levels",
   "u",false);
  ([Opt.all_basic;Opt.existential;Opt.universes], "Display all low-level contents",
   "Display all _low-level contents","l",false)
]

let setopts ct opts v =
  let opts = List.map (fun o -> (o, v)) opts in
  Coq.PrintOpt.set ct opts

(* Reset this to None on page change ! *)
let (last_completion:(string*int*int*bool) option ref) = ref None

let () = to_do_on_page_switch :=
  (fun i -> last_completion := None)::!to_do_on_page_switch

let rec complete input_buffer w (offset:int) =
  match !last_completion with
    | Some (lw,loffset,lpos,backward)
	when lw=w && loffset=offset ->
      begin
	let iter = input_buffer#get_iter (`OFFSET lpos) in
	if backward then
	  match complete_backward w iter with
	    | None ->
	      last_completion :=
		Some (lw,loffset,
		      (find_word_end
			 (input_buffer#get_iter (`OFFSET loffset)))#offset ,
		      false);
	      None
	    | Some (ss,start,stop) as result ->
	      last_completion :=
		Some (w,offset,ss#offset,true);
	      result
	else
	  match complete_forward w iter with
	    | None ->
	      last_completion := None;
	      None
	    | Some (ss,start,stop) as result ->
	      last_completion :=
		Some (w,offset,ss#offset,false);
	      result
      end
    | _ -> begin
      match complete_backward w (input_buffer#get_iter (`OFFSET offset)) with
	| None ->
	  last_completion :=
	    Some (w,offset,(find_word_end (input_buffer#get_iter
					     (`OFFSET offset)))#offset,false);
	  complete input_buffer w offset
	| Some (ss,start,stop) as result ->
	  last_completion := Some (w,offset,ss#offset,true);
	  result
    end

let get_current_word () =
  match session_notebook#current_term,cb#text with
    | {script=script; analyzed_view=av;},None ->
      prerr_endline "None selected";
      let it = av#get_insert in
      let start = find_word_start it in
      let stop = find_word_end start in
      script#buffer#move_mark `SEL_BOUND ~where:start;
      script#buffer#move_mark `INSERT ~where:stop;
      script#buffer#get_text ~slice:true ~start ~stop ()
    | _,Some t ->
      prerr_endline "Some selected";
      prerr_endline t;
      t


let input_channel b ic =
  let buf = String.create 1024 and len = ref 0 in
  while len := input ic buf 0 1024; !len > 0 do
    Buffer.add_substring b buf 0 !len
  done

let with_file handler name ~f =
  try
    let ic = open_in_gen [Open_rdonly;Open_creat] 0o644 name in
    try f ic; close_in ic with e -> close_in ic; raise e
  with Sys_error s -> handler s

(* For find_phrase_starting_at *)
exception Stop of int

let tag_of_sort = function
  | Coq_lex.Comment -> Tags.Script.comment
  | Coq_lex.Keyword -> Tags.Script.kwd
  | Coq_lex.Declaration -> Tags.Script.decl
  | Coq_lex.ProofDeclaration -> Tags.Script.proof_decl
  | Coq_lex.Qed -> Tags.Script.qed
  | Coq_lex.String -> failwith "No tag"

let apply_tag (buffer:GText.buffer) orig off_conv from upto sort =
  try
    let tag = tag_of_sort sort in
    let start = orig#forward_chars (off_conv from) in
    let stop = orig#forward_chars (off_conv upto) in
    buffer#apply_tag ~start ~stop tag
  with _ -> ()

let remove_tags (buffer:GText.buffer) from upto =
  List.iter (buffer#remove_tag ~start:from ~stop:upto)
    [ Tags.Script.comment; Tags.Script.kwd; Tags.Script.decl;
      Tags.Script.proof_decl; Tags.Script.qed ]

(** Cut a part of the buffer in sentences and tag them.
    May raise [Coq_lex.Unterminated] when the zone ends with
    an unterminated sentence. *)

let split_slice_lax (buffer:GText.buffer) from upto =
  remove_tags buffer from upto;
  buffer#remove_tag ~start:from ~stop:upto Tags.Script.sentence;
  let slice = buffer#get_text ~start:from ~stop:upto () in
  let rec split_substring str =
    let off_conv = byte_offset_to_char_offset str in
    let slice_len = String.length str in
    let end_off = Coq_lex.delimit_sentence (apply_tag buffer from off_conv) str
    in
    let start = from#forward_chars (off_conv end_off) in
    let stop = start#forward_char in
    buffer#apply_tag ~start ~stop Tags.Script.sentence;
    let next = end_off + 1 in
    if next < slice_len then begin
      ignore (from#nocopy#forward_chars (off_conv next));
      split_substring (String.sub str next (slice_len - next))
    end
  in
  split_substring slice

(** Searching forward and backward a position fulfilling some condition *)

let rec forward_search cond (iter:GText.iter) =
  if iter#is_end || cond iter then iter
  else forward_search cond iter#forward_char

let rec backward_search cond (iter:GText.iter) =
  if iter#is_start || cond iter then iter
  else backward_search cond iter#backward_char

let is_sentence_end s = s#has_tag Tags.Script.sentence
let is_char s c = s#char = Char.code c

(** Search backward the first character of a sentence, starting at [iter]
    and going at most up to [soi] (meant to be the end of the locked zone).
    Raise [Not_found] when no proper sentence start has been found,
    in particular when the final "." of the locked zone is followed
    by a non-blank character outside the locked zone. This non-blank
    character will be signaled as erroneous in [tag_on_insert] below. *)

let grab_sentence_start (iter:GText.iter) soi =
  let cond iter =
    if iter#compare soi < 0 then raise Not_found;
    let prev = iter#backward_char in
    is_sentence_end prev &&
      (not (is_char prev '.') ||
       List.exists (is_char iter) [' ';'\n';'\r';'\t'])
  in
  backward_search cond iter

(** Search forward the first character immediately after a sentence end *)

let rec grab_sentence_stop (start:GText.iter) =
  (forward_search is_sentence_end start)#forward_char

(** Search forward the first character immediately after a "." sentence end
    (and not just a "{" or "}" or comment end *)

let rec grab_ending_dot (start:GText.iter) =
  let is_ending_dot s = is_sentence_end s && s#char = Char.code '.' in
  (forward_search is_ending_dot start)#forward_char

(** Retag a zone that has been edited *)

let tag_on_insert =
  (* possible race condition here : editing two buffers with a timedelta smaller
   * than 1.5s might break the error recovery mechanism. *)
  let skip_last = ref (ref true) in (* ref to the mutable flag created on last call *)
  fun buffer ->
    try
      (* the start of the non-locked zone *)
      let soi = buffer#get_iter_at_mark (`NAME "start_of_input") in
      (* the inserted zone is between [prev_insert] and [insert] *)
      let insert = buffer#get_iter_at_mark `INSERT in
      let prev_insert = buffer#get_iter_at_mark (`NAME "prev_insert") in
      (* [prev_insert] is normally always before [insert] even when deleting.
	 Let's check this nonetheless *)
      let prev_insert =
	if insert#compare prev_insert < 0 then insert else prev_insert
      in
      let start = grab_sentence_start prev_insert soi in
      (** The status of "{" "}" as sentence delimiters is too fragile.
	  We retag up to the next "." instead. *)
      let stop = grab_ending_dot insert in
      let skip_curr = ref true in (* shall the callback be skipped ? by default yes*)
      (!skip_last) := true; (* skip the previously created callback *)
      skip_last := skip_curr;
      try split_slice_lax buffer start stop
      with Coq_lex.Unterminated ->
        skip_curr := false;
	let callback () =
	  if not !skip_curr then begin
	    try split_slice_lax buffer start buffer#end_iter
	    with Coq_lex.Unterminated -> ()
	  end; false
	in
	ignore (Glib.Timeout.add ~ms:1500 ~callback)
    with Not_found ->
      let err_pos = buffer#get_iter_at_mark (`NAME "start_of_input") in
      buffer#apply_tag Tags.Script.error ~start:err_pos ~stop:err_pos#forward_char

let force_retag buffer =
  try split_slice_lax buffer buffer#start_iter buffer#end_iter
  with Coq_lex.Unterminated -> ()

let toggle_proof_visibility (buffer:GText.buffer) (cursor:GText.iter) =
  (* move back twice if not into proof_decl,
   * once if into proof_decl and back_char into_proof_decl,
   * don't move if into proof_decl and back_char not into proof_decl *)
  if not (cursor#has_tag Tags.Script.proof_decl) then
    ignore (cursor#nocopy#backward_to_tag_toggle (Some Tags.Script.proof_decl));
  if cursor#backward_char#has_tag Tags.Script.proof_decl then
    ignore (cursor#nocopy#backward_to_tag_toggle (Some Tags.Script.proof_decl));
  let decl_start = cursor in
  let prf_end = decl_start#forward_to_tag_toggle (Some Tags.Script.qed) in
  let decl_end = grab_ending_dot decl_start in
  let prf_end = grab_ending_dot prf_end in
  let prf_end = prf_end#forward_char in
  if decl_start#has_tag Tags.Script.folded then (
    buffer#remove_tag ~start:decl_start ~stop:decl_end Tags.Script.folded;
    buffer#remove_tag ~start:decl_end ~stop:prf_end Tags.Script.hidden)
  else (
    buffer#apply_tag ~start:decl_start ~stop:decl_end Tags.Script.folded;
    buffer#apply_tag ~start:decl_end ~stop:prf_end Tags.Script.hidden)

(** The arguments that will be passed to coqtop. No quoting here, since
    no /bin/sh when using create_process instead of open_process. *)
let custom_project_files = ref []
let sup_args = ref []

class analyzed_view (_script:Undo.undoable_view) (_pv:GText.view) (_mv:GText.view) _cs _ct _fn =
object(self)
  val input_view = _script
  val input_buffer = _script#buffer
  val proof_view = _pv
  val proof_buffer = _pv#buffer
  val message_view = _mv
  val message_buffer = _mv#buffer
  val cmd_stack = _cs
  val mycoqtop = _ct
  val mutable is_active = false
  val mutable read_only = false
  val mutable filename = _fn
  val mutable stats = None
  val mutable last_modification_time = 0.
  val mutable last_auto_save_time = 0.
  val mutable detached_views = []
  val mutable find_forward_instead_of_backward = false

  val mutable auto_complete_on = !current.auto_complete
  val hidden_proofs = Hashtbl.create 32

  method private toggle_auto_complete =
    auto_complete_on <- not auto_complete_on
  method set_auto_complete t = auto_complete_on <- t
  method without_auto_complete : 'a 'b. ('a -> 'b) -> 'a -> 'b = fun f x ->
    let old = auto_complete_on in
    self#set_auto_complete false;
    let y = f x in
    self#set_auto_complete old;
    y
  method add_detached_view (w:GWindow.window) =
    detached_views <- w::detached_views
  method remove_detached_view (w:GWindow.window) =
    detached_views <- List.filter (fun e -> w#misc#get_oid<>e#misc#get_oid) detached_views

  method kill_detached_views () =
    List.iter (fun w -> w#destroy ()) detached_views;
    detached_views <- []

  method filename = filename
  method stats = stats
  method update_stats =
    match filename with
      | Some f -> stats <- my_stat f
      | _ -> ()

  method revert =
    match filename with
      | Some f -> begin
        let do_revert () = begin
          push_info "Reverting buffer";
          try
            if is_active then self#force_reset_initial;
            let b = Buffer.create 1024 in
            with_file flash_info f ~f:(input_channel b);
            let s = try_convert (Buffer.contents b) in
            input_buffer#set_text s;
            self#update_stats;
            input_buffer#place_cursor ~where:input_buffer#start_iter;
            input_buffer#set_modified false;
            pop_info ();
            flash_info "Buffer reverted";
            force_retag input_buffer;
          with _  ->
            pop_info ();
            flash_info "Warning: could not revert buffer";
        end
        in
        if input_buffer#modified then
          match (GToolbox.question_box
                   ~title:"Modified buffer changed on disk"
                   ~buttons:["Revert from File";
                             "Overwrite File";
                             "Disable Auto Revert"]
                   ~default:0
                   ~icon:(stock_to_widget `DIALOG_WARNING)
                   "Some unsaved buffers changed on disk"
          )
          with 1 -> do_revert ()
            | 2 -> if self#save f then flash_info "Overwritten" else
                flash_info "Could not overwrite file"
            | _ ->
              prerr_endline "Auto revert set to false";
              !current.global_auto_revert <- false;
              disconnect_revert_timer ()
        else do_revert ()
      end
      | None -> ()

  method save f =
    if try_export f (input_buffer#get_text ()) then begin
      filename <- Some f;
      input_buffer#set_modified false;
      stats <- my_stat f;
      (match self#auto_save_name with
        | None -> ()
        | Some fn -> try Sys.remove fn with _ -> ());
      true
    end
    else false

  method private auto_save_name =
    match filename with
      | None -> None
      | Some f ->
        let dir = Filename.dirname f in
        let base = (fst !current.auto_save_name) ^
          (Filename.basename f) ^
          (snd !current.auto_save_name)
        in Some (Filename.concat dir base)

  method private need_auto_save =
    input_buffer#modified &&
      last_modification_time > last_auto_save_time

  method auto_save =
    if self#need_auto_save then begin
      match self#auto_save_name with
        | None -> ()
        | Some fn ->
          try
            last_auto_save_time <- Unix.time();
            prerr_endline ("Autosave time : "^(string_of_float (Unix.time())));
            if try_export fn (input_buffer#get_text ()) then begin
              flash_info ~delay:1000 "Autosaved"
            end
            else warning
              ("Autosave failed (check if " ^ fn ^ " is writable)")
          with _ ->
            warning ("Autosave: unexpected error while writing "^fn)
    end

  method save_as f =
    if Sys.file_exists f then
      match (GToolbox.question_box ~title:"File exists on disk"
               ~buttons:["Overwrite";
                         "Cancel";]
               ~default:1
               ~icon:
               (let img = GMisc.image () in
                img#set_stock `DIALOG_WARNING;
                img#set_icon_size `DIALOG;
                img#coerce)
               ("File "^f^" already exists")
      )
      with 1 -> self#save f
        | _ -> false
    else self#save f

  method set_read_only b = read_only<-b
  method read_only = read_only
  method is_active = is_active
  method insert_message s =
    message_buffer#insert s;
    message_view#misc#draw None

  method set_message s =
    message_buffer#set_text s;
    message_view#misc#draw None

  method clear_message = message_buffer#set_text ""
  val mutable last_index = true
  val last_array = [|"";""|]
  method get_start_of_input =  input_buffer#get_iter_at_mark (`NAME "start_of_input")

  method get_insert = get_insert input_buffer

  method recenter_insert =
    (* BUG : to investigate further:
       FIXED : Never call  GMain.* in thread !
       PLUS : GTK BUG ??? Cannot be called from a thread...
       ADDITION: using sync instead of async causes deadlock...*)
    ignore (GtkThread.async (
      input_view#scroll_to_mark
        ~use_align:false
        ~yalign:0.75
        ~within_margin:0.25)
              `INSERT)


  method indent_current_line =
    let get_nb_space it =
      let it = it#copy in
      let nb_sep = ref 0 in
      let continue = ref true in
      while !continue do
        if it#char = space then begin
          incr nb_sep;
          if not it#nocopy#forward_char then continue := false;
        end else continue := false
      done;
      !nb_sep
    in
    let previous_line = self#get_insert in
    if previous_line#nocopy#backward_line then begin
      let previous_line_spaces = get_nb_space previous_line in
      let current_line_start = self#get_insert#set_line_offset 0 in
      let current_line_spaces = get_nb_space current_line_start in
      if input_buffer#delete_interactive
        ~start:current_line_start
        ~stop:(current_line_start#forward_chars current_line_spaces)
        ()
      then
        let current_line_start = self#get_insert#set_line_offset 0 in
        input_buffer#insert
          ~iter:current_line_start
          (String.make previous_line_spaces ' ')
    end


  method go_to_next_occ_of_cur_word =
    let cv = session_notebook#current_term in
    let av = cv.analyzed_view in
    let b = (cv.script)#buffer in
    let start = find_word_start (av#get_insert) in
    let stop = find_word_end start in
    let text = b#get_text ~start ~stop () in
    match stop#forward_search text with
      | None -> ()
      | Some(start, _) ->
        (b#place_cursor start;
         self#recenter_insert)

  method go_to_prev_occ_of_cur_word =
    let cv = session_notebook#current_term in
    let av = cv.analyzed_view in
    let b = (cv.script)#buffer in
    let start = find_word_start (av#get_insert) in
    let stop = find_word_end start in
    let text = b#get_text ~start ~stop () in
    match start#backward_search text with
      | None -> ()
      | Some(start, _) ->
        (b#place_cursor start;
         self#recenter_insert)

  val mutable full_goal_done = true

  method show_goals_full =
    if not full_goal_done then
      proof_view#buffer#set_text "";
    begin
      let menu_callback = if !current.contextual_menus_on_goal then
          (fun s () -> ignore (self#insert_this_phrase_on_success
                                 true true false ("progress "^s) s))
        else
          (fun _ _ -> ()) in
      try
        begin match Coq.goals !mycoqtop with
          | Interface.Fail (l, str) ->
            self#set_message ("Error in coqtop :\n"^str)
          | Interface.Good goals ->
            begin match Coq.evars !mycoqtop with
            | Interface.Fail (l, str) ->
              self#set_message ("Error in coqtop :\n"^str)
            | Interface.Good evs ->
              let hints = match Coq.hints !mycoqtop with
              | Interface.Fail (_, _) -> None
              | Interface.Good hints -> hints
              in
              Ideproof.display
                (Ideproof.mode_tactic menu_callback)
                proof_view goals hints evs
            end
        end
      with
        | e -> prerr_endline (Printexc.to_string e)
    end

  method show_goals = self#show_goals_full

  method private send_to_coq ct verbose phrase show_output show_error localize =
    let display_output msg =
      self#insert_message (if show_output then msg else "") in
    let display_error (loc,s) =
      if show_error then begin
        if not (Glib.Utf8.validate s) then
          flash_info "This error is so nasty that I can't even display it."
        else begin
          self#insert_message s;
          message_view#misc#draw None;
          if localize then
            (match loc with
              | None -> ()
              | Some (start,stop) ->
                let convert_pos = byte_offset_to_char_offset phrase in
                let start = convert_pos start in
                let stop = convert_pos stop in
                let i = self#get_start_of_input in
                let starti = i#forward_chars start in
                let stopi = i#forward_chars stop in
                input_buffer#apply_tag Tags.Script.error
                  ~start:starti
                  ~stop:stopi;
                input_buffer#place_cursor ~where:starti)
        end
      end in
    try
      full_goal_done <- false;
      prerr_endline "Send_to_coq starting now";
      (* It's important here to work with [ct] and not [!mycoqtop], otherwise
         we could miss a restart of coqtop and continue sending it orders. *)
      match Coq.interp ct ~verbose phrase with
        | Interface.Fail (l,str) -> sync display_error (l,str); None
        | Interface.Good msg -> sync display_output msg; Some Safe
          (* TODO: Restore someday the access to Decl_mode.get_damon_flag,
	     and also detect the use of admit, and then return Unsafe *)
    with
      | End_of_file -> (* Coqtop has died, let's trigger a reset_initial. *)
        raise RestartCoqtop
      | e -> sync display_error (None, Printexc.to_string e); None

  method find_phrase_starting_at (start:GText.iter) =
    try
      let start = grab_sentence_start start self#get_start_of_input in
      let stop = grab_sentence_stop start in
      if is_sentence_end stop#backward_char then Some (start,stop)
      else None
    with Not_found -> None

  method complete_at_offset (offset:int) =
    prerr_endline ("Completion at offset : " ^ string_of_int offset);
    let it () = input_buffer#get_iter (`OFFSET offset) in
    let iit = it () in
    let start = find_word_start iit in
    if ends_word iit then
      let w = input_buffer#get_text
        ~start
        ~stop:iit
        ()
      in
      if String.length w <> 0 then begin
        prerr_endline ("Completion of prefix : '" ^ w^"'");
        match complete input_buffer w start#offset with
          | None -> false
          | Some (ss,start,stop) ->
            let completion = input_buffer#get_text ~start ~stop () in
            ignore (input_buffer#delete_selection ());
            ignore (input_buffer#insert_interactive completion);
            input_buffer#move_mark `SEL_BOUND ~where:(it())#backward_char;
            true
      end else false
    else false

  method private process_one_phrase ct verbosely display_goals do_highlight =
    let get_next_phrase () =
      self#clear_message;
      prerr_endline "process_one_phrase starting now";
      if do_highlight then begin
        push_info "Coq is computing";
        input_view#set_editable false;
      end;
      match self#find_phrase_starting_at self#get_start_of_input with
        | None ->
          if do_highlight then begin
            input_view#set_editable true;
            pop_info ();
          end;
          None
        | Some(start,stop) ->
          prerr_endline "process_one_phrase : to_process highlight";
          if do_highlight then begin
            input_buffer#apply_tag Tags.Script.to_process ~start ~stop;
            prerr_endline "process_one_phrase : to_process applied";
          end;
          prerr_endline "process_one_phrase : getting phrase";
          Some((start,stop),start#get_slice ~stop) in
    let remove_tag (start,stop) =
      if do_highlight then begin
        input_buffer#remove_tag Tags.Script.to_process ~start ~stop;
        input_view#set_editable true;
        pop_info ();
      end in
    let mark_processed safe (start,stop) =
      let b = input_buffer in
      b#move_mark ~where:stop (`NAME "start_of_input");
      b#apply_tag (safety_tag safe) ~start ~stop;
      if (self#get_insert#compare) stop <= 0 then
        begin
          b#place_cursor ~where:stop;
          self#recenter_insert
        end;
      let ide_payload = { start = `MARK (b#create_mark start);
                          stop = `MARK (b#create_mark stop); } in
      Stack.push ide_payload cmd_stack;
      if display_goals then self#show_goals;
      remove_tag (start,stop)
    in
    match sync get_next_phrase () with
      | None -> raise Unsuccessful
      | Some ((_,stop) as loc,phrase) ->
	  if stop#backward_char#has_tag Tags.Script.comment
	  then sync mark_processed Safe loc
          else try match self#send_to_coq ct verbosely phrase true true true with
            | Some safe -> sync mark_processed safe loc
            | None -> sync remove_tag loc; raise Unsuccessful
	  with
	    | RestartCoqtop -> sync remove_tag loc; raise RestartCoqtop

  method process_next_phrase verbosely =
    try self#process_one_phrase !mycoqtop verbosely true true
    with Unsuccessful -> ()

  method private insert_this_phrase_on_success
    show_output show_msg localize coqphrase insertphrase =
    let mark_processed safe =
      let stop = self#get_start_of_input in
      if stop#starts_line then
        input_buffer#insert ~iter:stop insertphrase
      else input_buffer#insert ~iter:stop ("\n"^insertphrase);
      let start = self#get_start_of_input in
      input_buffer#move_mark ~where:stop (`NAME "start_of_input");
      input_buffer#apply_tag (safety_tag safe) ~start ~stop;
      if (self#get_insert#compare) stop <= 0 then
        input_buffer#place_cursor ~where:stop;
      let ide_payload = { start = `MARK (input_buffer#create_mark start);
                          stop = `MARK (input_buffer#create_mark stop); } in
      Stack.push ide_payload cmd_stack;
      self#show_goals;
       (*Auto insert save on success...
	 try (match Coq.get_current_goals () with
	 | [] ->
	 (match self#send_to_coq "Save.\n" true true true with
	 | Some ast ->
	 begin
	 let stop = self#get_start_of_input in
	 if stop#starts_line then
	 input_buffer#insert ~iter:stop "Save.\n"
	 else input_buffer#insert ~iter:stop "\nSave.\n";
	 let start = self#get_start_of_input in
	 input_buffer#move_mark ~where:stop (`NAME"start_of_input");
	 input_buffer#apply_tag_by_name "processed" ~start ~stop;
	 if (self#get_insert#compare) stop <= 0 then
	 input_buffer#place_cursor stop;
	 let start_of_phrase_mark =
	 `MARK (input_buffer#create_mark start) in
	 let end_of_phrase_mark =
	 `MARK (input_buffer#create_mark stop) in
	 push_phrase
	 reset_info start_of_phrase_mark end_of_phrase_mark ast
	 end
	 | None -> ())
	 | _ -> ())
	 with _ -> ()*) in
    match self#send_to_coq !mycoqtop false coqphrase show_output show_msg localize with
      | Some safe -> sync mark_processed safe; true
      | None ->
        sync
          (fun _ -> self#insert_message ("Unsuccessfully tried: "^coqphrase))
          ();
        false

  method process_until_iter_or_error stop =
    let stop' = `OFFSET stop#offset in
    let start = self#get_start_of_input#copy in
    let start' = `OFFSET start#offset in
    sync (fun _ ->
      input_buffer#apply_tag Tags.Script.to_process ~start ~stop;
      input_view#set_editable false) ();
    push_info "Coq is computing";
    let get_current () =
      if !current.stop_before then
        match self#find_phrase_starting_at self#get_start_of_input with
          | None -> self#get_start_of_input
          | Some (_, stop2) -> stop2
      else begin
        self#get_start_of_input
      end
    in
    let unlock () =
      sync (fun _ ->
	self#show_goals;
	(* Start and stop might be invalid if an eol was added at eof *)
	let start = input_buffer#get_iter start' in
	let stop =  input_buffer#get_iter stop' in
	input_buffer#remove_tag Tags.Script.to_process ~start ~stop;
	input_view#set_editable true) ()
    in
    (* All the [process_one_phrase] below should be done with the same [ct]
       instead of accessing multiple time [mycoqtop]. Otherwise a restart of
       coqtop could go unnoticed, and the new coqtop could receive strange
       things. *)
    let ct = !mycoqtop in
    (try
       while stop#compare (get_current()) >= 0
       do self#process_one_phrase ct false false false done
     with
       | Unsuccessful -> ()
       | RestartCoqtop -> unlock (); raise RestartCoqtop);
    unlock ();
    pop_info()

  method process_until_end_or_error =
    self#process_until_iter_or_error input_buffer#end_iter

  method reset_initial =
    mycoqtop := Coq.respawn_coqtop !mycoqtop;
    sync (fun () ->
      Stack.iter
	(function inf ->
          let start = input_buffer#get_iter_at_mark inf.start in
          let stop = input_buffer#get_iter_at_mark inf.stop in
          input_buffer#move_mark ~where:start (`NAME "start_of_input");
          input_buffer#remove_tag Tags.Script.processed ~start ~stop;
	  input_buffer#remove_tag Tags.Script.unjustified ~start ~stop;
          input_buffer#delete_mark inf.start;
          input_buffer#delete_mark inf.stop;
	)
	cmd_stack;
      Stack.clear cmd_stack;
      self#clear_message) ()

  method force_reset_initial =
    (* Do nothing if a force_reset_initial is already ongoing *)
    if Mutex.try_lock resetting then begin
      Coq.kill_coqtop !mycoqtop;
      (* If a computation is ongoing, an exception will trigger
	 the reset_initial in do_if_not_computing, not here. *)
      if Mutex.try_lock coq_computing then begin
	self#reset_initial;
	Mutex.unlock coq_computing
      end;
      Mutex.unlock resetting
    end

  (* Internal method for dialoging with coqtop about a backtrack.
     The ide's cmd_stack has already been cleared up to the desired point.
     The [finish] function is used to handle minor differences between
     [go_to_insert] and [undo_last_step] *)

  method private do_backtrack finish n =
    (* pop n more commands if coqtop has said so (e.g. for undoing a proof) *)
    let rec n_pop n =
      if n = 0 then ()
      else
	let phrase = Stack.pop cmd_stack in
	let stop = input_buffer#get_iter_at_mark phrase.stop in
        if stop#backward_char#has_tag Tags.Script.comment
	  then n_pop n
	  else n_pop (pred n)
    in
    match Coq.rewind !mycoqtop n with
      | Interface.Good n ->
	n_pop n;
        sync (fun _ ->
          let start =
            if Stack.is_empty cmd_stack then input_buffer#start_iter
            else input_buffer#get_iter_at_mark (Stack.top cmd_stack).stop in
	  let stop = self#get_start_of_input in
          input_buffer#remove_tag Tags.Script.processed ~start ~stop;
          input_buffer#remove_tag Tags.Script.unjustified ~start ~stop;
          input_buffer#move_mark ~where:start (`NAME "start_of_input");
          self#show_goals;
          self#clear_message;
          finish start) ()
      | Interface.Fail (l,str) ->
        sync self#set_message
          ("Error while backtracking :\n" ^ str ^ "\n" ^
	   "CoqIDE and coqtop may be out of sync, you may want to use Restart.")

  (* backtrack Coq to the phrase preceding iterator [i] *)
  method backtrack_to_no_lock i =
    prerr_endline "Backtracking_to iter starts now.";
    full_goal_done <- false;
    (* pop Coq commands until we reach iterator [i] *)
    let rec n_step n =
      if Stack.is_empty cmd_stack then n else
        let phrase = Stack.top cmd_stack in
	let stop = input_buffer#get_iter_at_mark phrase.stop in
        if i#compare stop >= 0 then n
	else begin
	  ignore (Stack.pop cmd_stack);
          if stop#backward_char#has_tag Tags.Script.comment
	  then n_step n
	  else n_step (succ n)
	end
    in
    begin
      try
	self#do_backtrack (fun _ -> ()) (n_step 0);
	(* We may have backtracked too much: let's replay *)
	self#process_until_iter_or_error i
      with _ ->
        push_info
	  ("WARNING: undo failed badly.\n" ^
	   "Coq might be in an inconsistent state.\n" ^
	   "Please restart and report.");
    end

  method backtrack_to i =
    if Mutex.try_lock coq_may_stop then
      (push_info "Undoing...";
       self#backtrack_to_no_lock i; Mutex.unlock coq_may_stop;
       pop_info ())
    else prerr_endline "backtrack_to : discarded (lock is busy)"

  method go_to_insert =
    let point = self#get_insert in
    if point#compare self#get_start_of_input>=0
    then self#process_until_iter_or_error point
    else self#backtrack_to point

  method undo_last_step =
    full_goal_done <- false;
    if Mutex.try_lock coq_may_stop then
      (push_info "Undoing last step...";
       (try
          let phrase = Stack.pop cmd_stack in
	  let stop = input_buffer#get_iter_at_mark phrase.stop in
	  let count =
	    if stop#backward_char#has_tag Tags.Script.comment then 0 else 1
	  in
	  let finish where =
	    input_buffer#place_cursor ~where;
	    self#recenter_insert;
	  in
	  self#do_backtrack finish count
        with Stack.Empty -> ()
       );
       pop_info ();
       Mutex.unlock coq_may_stop)
    else prerr_endline "undo_last_step discarded"


  method insert_command cp ip =
    async(fun _ -> self#clear_message)();
    ignore (self#insert_this_phrase_on_success true false false cp ip)

  method tactic_wizard l =
    async(fun _ -> self#clear_message)();
    ignore
      (List.exists
         (fun p ->
           self#insert_this_phrase_on_success true false false
             ("progress "^p^".\n") (p^".\n")) l)

  method active_keypress_handler k =
    let state = GdkEvent.Key.state k in
    begin
      match  state with
        | l when List.mem `MOD1 l ->
          let k = GdkEvent.Key.keyval k in
          if GdkKeysyms._Return=k
          then ignore(
            if (input_buffer#insert_interactive "\n") then
              begin
                let i= self#get_insert#backward_word_start in
                prerr_endline "active_kp_hf: Placing cursor";
                self#process_until_iter_or_error i
              end);
          true
        | l when List.mem `CONTROL l ->
          let k = GdkEvent.Key.keyval k in
          if GdkKeysyms._Break=k
          then break ();
          false
        | l ->
          if GdkEvent.Key.keyval k = GdkKeysyms._Tab then begin
            prerr_endline "active_kp_handler for Tab";
            self#indent_current_line;
            true
          end else false
    end


  method disconnected_keypress_handler k =
    match GdkEvent.Key.state k with
      | l when List.mem `CONTROL l ->
        let k = GdkEvent.Key.keyval k in
        if GdkKeysyms._c=k
        then break ();
        false
      | l -> false


  val mutable deact_id = None
  val mutable act_id = None

  method activate () = if not is_active then begin
    is_active <- true;
    act_id <- Some
      (input_view#event#connect#key_press ~callback:self#active_keypress_handler);
    prerr_endline "CONNECTED active : ";
    print_id (match act_id with Some x -> x | None -> assert false);
    match filename with
      | None -> ()
      | Some f ->
	let dir = Filename.dirname f in
	let ct = !mycoqtop in
	match Coq.inloadpath ct dir with
	  | Interface.Fail (_,str) ->
	    self#set_message
	      ("Could not determine lodpath, this might lead to problems:\n"^str)
	  | Interface.Good true -> ()
	  | Interface.Good false ->
	    let cmd = Printf.sprintf "Add LoadPath \"%s\". "  dir in
	    match Coq.interp ct cmd with
	      | Interface.Fail (l,str) ->
		self#set_message ("Couln't add loadpath:\n"^str)
	      | Interface.Good _ -> ()
  end

  method private electric_paren tag =
    let oparen_code = Glib.Utf8.to_unichar "("  ~pos:(ref 0) in
    let cparen_code = Glib.Utf8.to_unichar ")"  ~pos:(ref 0) in
    ignore (input_buffer#connect#insert_text ~callback:
              (fun it x ->
                input_buffer#remove_tag
                  ~start:input_buffer#start_iter
                  ~stop:input_buffer#end_iter
                  tag;
                if x = "" then () else
                  match x.[String.length x - 1] with
                    | ')' ->
                      let hit = self#get_insert in
                      let count = ref 0 in
                      if hit#nocopy#backward_find_char
                        (fun c ->
                          if c = oparen_code && !count = 0 then true
                          else if c = cparen_code then
                            (incr count;false)
                          else if c = oparen_code then
                            (decr count;false)
                          else false
                        )
                      then
                        begin
                          prerr_endline "Found matching parenthesis";
                          input_buffer#apply_tag tag ~start:hit ~stop:hit#forward_char
                        end
                      else ()
                    | _ -> ())
  )

  method help_for_keyword () =
    browse_keyword (self#insert_message) (get_current_word ())

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

  initializer
    ignore (message_buffer#connect#insert_text
              ~callback:(fun it s -> ignore
                (message_view#scroll_to_mark
                   ~use_align:false
                   ~within_margin:0.49
                   `INSERT)));
    ignore (input_buffer#connect#insert_text
              ~callback:(fun it s ->
                if (it#compare self#get_start_of_input)<0
                then GtkSignal.stop_emit ();
                if String.length s > 1 then
                  (prerr_endline "insert_text: Placing cursor";input_buffer#place_cursor ~where:it)));
    ignore (input_buffer#connect#after#apply_tag
              ~callback:(fun tag ~start ~stop ->
                if (start#compare self#get_start_of_input)>=0
                then
                  begin
                    input_buffer#remove_tag
                      Tags.Script.processed
                      ~start
                      ~stop;
                    input_buffer#remove_tag
                      Tags.Script.unjustified
                      ~start
                      ~stop
                  end
              )
    );
    ignore (input_buffer#connect#after#insert_text
              ~callback:(fun it s ->
                if auto_complete_on &&
                  String.length s = 1 && s <> " " && s <> "\n"
                then
                  let v = session_notebook#current_term.analyzed_view
                  in
                  let has_completed =
                    v#complete_at_offset
                      ((input_view#buffer#get_iter `SEL_BOUND)#offset)
                  in
                  if has_completed then
                    input_buffer#move_mark `SEL_BOUND ~where:(input_buffer#get_iter `SEL_BOUND)#forward_char;
              )
    );
    ignore (input_buffer#connect#begin_user_action
	      ~callback:(fun () ->
		           let here = input_buffer#get_iter_at_mark `INSERT in
			   input_buffer#move_mark (`NAME "prev_insert") here
	      )
    );
    ignore (input_buffer#connect#end_user_action
              ~callback:(fun () ->
                last_modification_time <- Unix.time ();
                let r = input_view#visible_rect in
                let stop =
                  input_view#get_iter_at_location
                    ~x:(Gdk.Rectangle.x r + Gdk.Rectangle.width r)
                    ~y:(Gdk.Rectangle.y r + Gdk.Rectangle.height r)
                in
                input_buffer#remove_tag
                  Tags.Script.error
                  ~start:self#get_start_of_input
                  ~stop;
                tag_on_insert input_buffer
              )
    );
    ignore (input_buffer#add_selection_clipboard cb);
    ignore (proof_buffer#add_selection_clipboard cb);
    ignore (message_buffer#add_selection_clipboard cb);
    self#electric_paren Tags.Script.paren;
    ignore (input_buffer#connect#after#mark_set
              ~callback:(fun it (m:Gtk.text_mark) ->
                !set_location
                  (Printf.sprintf
                     "Line: %5d Char: %3d" (self#get_insert#line + 1)
                     (self#get_insert#line_offset + 1));
                match GtkText.Mark.get_name m  with
                  | Some "insert" ->
                    input_buffer#remove_tag
                      ~start:input_buffer#start_iter
                      ~stop:input_buffer#end_iter
                      Tags.Script.paren;
                  | Some s ->
                    prerr_endline (s^" moved")
                  | None -> () )
    );
    ignore (input_buffer#connect#insert_text
              ~callback:(fun it s ->
                prerr_endline "Should recenter ?";
                if String.contains s '\n' then begin
                  prerr_endline "Should recenter : yes";
                  self#recenter_insert
                end));
end

let last_make = ref "";;
let last_make_index = ref 0;;
let search_compile_error_regexp =
  Str.regexp
    "File \"\\([^\"]+\\)\", line \\([0-9]+\\), characters \\([0-9]+\\)-\\([0-9]+\\)";;

let search_next_error () =
  let _ = Str.search_forward search_compile_error_regexp !last_make !last_make_index in
  let f = Str.matched_group 1 !last_make
  and l = int_of_string (Str.matched_group 2 !last_make)
  and b = int_of_string (Str.matched_group 3 !last_make)
  and e = int_of_string (Str.matched_group 4 !last_make)
  and msg_index = Str.match_beginning ()
  in
  last_make_index := Str.group_end 4;
  (f,l,b,e,
   String.sub !last_make msg_index (String.length !last_make - msg_index))



(**********************************************************************)
(* session creation and primitive handling                            *)
(**********************************************************************)

let create_session file =
  let script =
    Undo.undoable_view
      ~buffer:(GText.buffer ~tag_table:Tags.Script.table ())
      ~wrap_mode:`NONE () in
  let proof =
    GText.view
      ~buffer:(GText.buffer ~tag_table:Tags.Proof.table ())
      ~editable:false ~wrap_mode:`CHAR () in
  let message =
    GText.view
      ~buffer:(GText.buffer ~tag_table:Tags.Message.table ())
      ~editable:false ~wrap_mode:`WORD () in
  let basename = GMisc.label ~text:(match file with
				      |None -> "*scratch*"
				      |Some f -> (Glib.Convert.filename_to_utf8 (Filename.basename f))
				   ) () in
  let stack = Stack.create () in
  let coqtop_args = match file with
    |None -> !sup_args
    |Some the_file -> match !current.read_project with
	|Ignore_args -> !sup_args
	|Append_args -> (Project_file.args_from_project the_file !custom_project_files !current.project_file_name)
	   @(!sup_args)
	|Subst_args -> Project_file.args_from_project the_file !custom_project_files !current.project_file_name
  in
  let ct = ref (Coq.spawn_coqtop coqtop_args) in
  let command = new Command_windows.command_window ct current in
  let legacy_av = new analyzed_view script proof message stack ct file in
  let () = legacy_av#update_stats in
  let _ =
    script#buffer#create_mark ~name:"start_of_input" script#buffer#start_iter in
  let _ =
    script#buffer#create_mark ~name:"prev_insert" script#buffer#start_iter in
  let _ =
    proof#buffer#create_mark ~name:"end_of_conclusion" proof#buffer#start_iter in
  let _ =
    GtkBase.Widget.add_events proof#as_widget [`ENTER_NOTIFY;`POINTER_MOTION] in
  let () =
    List.iter (fun (opts,_,_,_,dflt) -> setopts !ct opts dflt) print_items in
  let _ = legacy_av#activate () in
  let _ =
    proof#event#connect#motion_notify ~callback:
      (fun e ->
        let win = match proof#get_window `WIDGET with
          | None -> assert false
          | Some w -> w in
        let x,y = Gdk.Window.get_pointer_location win in
        let b_x,b_y = proof#window_to_buffer_coords ~tag:`WIDGET ~x ~y in
        let it = proof#get_iter_at_location ~x:b_x ~y:b_y in
        let tags = it#tags in
        List.iter
          (fun t ->
            ignore (GtkText.Tag.event t#as_tag proof#as_widget e it#as_iter))
          tags;
        false) in
  script#misc#set_name "ScriptWindow";
  script#buffer#place_cursor ~where:(script#buffer#start_iter);
  proof#misc#set_can_focus true;
  message#misc#set_can_focus true;
  script#misc#modify_font !current.text_font;
  proof#misc#modify_font !current.text_font;
  message#misc#modify_font !current.text_font;
  { tab_label=basename;
    filename=begin match file with None -> "" |Some f -> f end;
    script=script;
    proof_view=proof;
    message_view=message;
    analyzed_view=legacy_av;
    encoding="";
    toplvl=ct;
    command=command
  }

(* XXX - to be used later
   let load_session session filename encs =
   session.encoding <- List.find (IdeIO.load filename session.script#buffer) encs;
   session.tab_label#set_text (Glib.Convert.filename_to_utf8 (Filename.basename filename));
   session.filename <- filename;
   session.script#buffer#set_modified false


   let save_session session filename encs =
   session.encoding <- List.find (IdeIO.save session.script#buffer filename) encs;
   session.tab_label#set_text (Glib.Convert.filename_to_utf8 (Filename.basename filename));
   session.filename <- filename;
   session.script#buffer#set_modified false


   let init_session session =
   session.script#buffer#set_modified false;
   session.script#clear_undo;
   session.script#buffer#place_cursor session.script#buffer#start_iter
*)




(*********************************************************************)
(* functions called by the user interface                            *)
(*********************************************************************)
(* XXX - to be used later
   let do_open session filename =
   try
   load_session session filename ["UTF-8";"ISO-8859-1";"ISO-8859-15"];
   init_session session;
   ignore (session_notebook#append_term session)
   with _ -> ()


   let do_save session =
   try
   if session.script#buffer#modified then
   save_session session session.filename [session.encoding]
   with _ -> ()


   let choose_open =
   let last_filename = ref "" in fun session ->
   let open_dialog = GWindow.file_chooser_dialog ~action:`OPEN ~title:"Open file" ~modal:true () in
   let enc_frame = GBin.frame ~label:"File encoding" ~packing:(open_dialog#vbox#pack ~fill:false) () in
   let enc_entry = GEdit.entry ~text:(String.concat " " ["UTF-8";"ISO-8859-1";"ISO-8859-15"]) ~packing:enc_frame#add () in
   let error_dialog = GWindow.message_dialog ~message_type:`ERROR ~modal:true ~buttons:GWindow.Buttons.ok
   ~message:"Invalid encoding, please indicate the encoding to use." () in
   let open_response = function
   | `OPEN -> begin
   match open_dialog#filename with
   | Some fn -> begin
   try
   load_session session fn (Util.split_string_at ' ' enc_entry#text);
   session.analyzed_view <- Some (new analyzed_view session);
   init_session session;
   session_notebook#goto_page (session_notebook#append_term session);
   last_filename := fn
   with
   | Not_found -> open_dialog#misc#hide (); error_dialog#show ()
   | _ ->
   error_dialog#set_markup "Unknown error while loading file, aborting.";
   open_dialog#destroy (); error_dialog#destroy ()
   end
   | None -> ()
   end
   | `DELETE_EVENT -> open_dialog#destroy (); error_dialog#destroy ()
   in
   let _ = open_dialog#connect#response open_response in
   let _ = error_dialog#connect#response (fun x -> error_dialog#misc#hide (); open_dialog#show ()) in
   let filter_any = GFile.filter ~name:"Any" ~patterns:["*"] () in
   let filter_coq = GFile.filter ~name:"Coq source" ~patterns:["*.v"] () in
   open_dialog#add_select_button_stock `OPEN `OPEN;
   open_dialog#add_button_stock `CANCEL `DELETE_EVENT;
   open_dialog#add_filter filter_any;
   open_dialog#add_filter filter_coq;
   ignore(open_dialog#set_filename !last_filename);
   open_dialog#show ()


   let choose_save session =
   let save_dialog = GWindow.file_chooser_dialog ~action:`SAVE ~title:"Save file" ~modal:true () in
   let enc_frame = GBin.frame ~label:"File encoding" ~packing:(save_dialog#vbox#pack ~fill:false) () in
   let enc_entry = GEdit.entry ~text:(String.concat " " [session.encoding;"UTF-8";"ISO-8859-1";"ISO-8859-15"]) ~packing:enc_frame#add () in
   let error_dialog = GWindow.message_dialog ~message_type:`ERROR ~modal:true ~buttons:GWindow.Buttons.ok
   ~message:"Invalid encoding, please indicate the encoding to use." () in
   let save_response = function
   | `SAVE -> begin
   match save_dialog#filename with
   | Some fn -> begin
   try
   save_session session fn (Util.split_string_at ' ' enc_entry#text)
   with
   | Not_found -> save_dialog#misc#hide (); error_dialog#show ()
   | _ ->
   error_dialog#set_markup "Unknown error while saving file, aborting.";
   save_dialog#destroy (); error_dialog#destroy ()
   end
   | None -> ()
   end
   | `DELETE_EVENT -> save_dialog#destroy (); error_dialog#destroy ()
   in
   let _ = save_dialog#connect#response save_response in
   let _ = error_dialog#connect#response (fun x -> error_dialog#misc#hide (); save_dialog#show ()) in
   let filter_any = GFile.filter ~name:"Any" ~patterns:["*"] () in
   let filter_coq = GFile.filter ~name:"Coq source" ~patterns:["*.v"] () in
   save_dialog#add_select_button_stock `SAVE `SAVE;
   save_dialog#add_button_stock `CANCEL `DELETE_EVENT;
   save_dialog#add_filter filter_any;
   save_dialog#add_filter filter_coq;
   ignore(save_dialog#set_filename session.filename);
   save_dialog#show ()
*)

(* Nota: using && here has the advantage of working both under win32 and unix.
   If someday we want the main command to be tried even if the "cd" has failed,
   then we should use " ; " under unix but " & " under win32 (cf. #2363).
*)

let local_cd file =
  "cd " ^ Filename.quote (Filename.dirname file) ^ " && "

let do_print session =
  let av = session.analyzed_view in
  match av#filename with
    |None ->  flash_info "Cannot print: this buffer has no name"
    |Some f_name ->  begin
      let cmd =
        local_cd f_name ^
          !current.cmd_coqdoc ^ " -ps " ^ Filename.quote (Filename.basename f_name) ^
          " | " ^ !current.cmd_print
      in
      let print_window = GWindow.window ~title:"Print" ~modal:true ~position:`CENTER ~wm_class:"CoqIDE" ~wm_name: "CoqIDE"  () in
      let vbox_print = GPack.vbox ~spacing:10 ~border_width:10 ~packing:print_window#add () in
      let _ = GMisc.label ~justify:`LEFT ~text:"Print using the following command:" ~packing:vbox_print#add () in
      let print_entry = GEdit.entry ~text:cmd ~editable:true ~width_chars:80 ~packing:vbox_print#add () in
      let hbox_print = GPack.hbox ~spacing:10 ~packing:vbox_print#add () in
      let print_cancel_button = GButton.button ~stock:`CANCEL ~label:"Cancel" ~packing:hbox_print#add () in
      let print_button  = GButton.button ~stock:`PRINT  ~label:"Print"  ~packing:hbox_print#add () in
      let callback_print () =
        let cmd = print_entry#text in
        let s,_ = run_command av#insert_message cmd in
        flash_info (cmd ^ if s = Unix.WEXITED 0 then " succeeded" else " failed");
        print_window#destroy ()
      in
      ignore (print_cancel_button#connect#clicked ~callback:print_window#destroy) ;
      ignore (print_button#connect#clicked ~callback:callback_print);
      print_window#misc#show ()
    end

let load_file handler f =
  let f = absolute_filename f in
  try
    prerr_endline "Loading file starts";
    let is_f = Minilib.same_file f in
      if not (Minilib.list_fold_left_i
		(fun i found x -> if found then found else
                   let {analyzed_view=av} = x in
                     (match av#filename with
			| None -> false
			| Some fn ->
			    if is_f fn
			    then (session_notebook#goto_page i; true)
			    else false))
              0 false session_notebook#pages)
      then begin
	prerr_endline "Loading: must open";
	let b = Buffer.create 1024 in
	prerr_endline "Loading: get raw content";
	with_file handler f ~f:(input_channel b);
	prerr_endline "Loading: convert content";
	let s = do_convert (Buffer.contents b) in
	prerr_endline "Loading: create view";
	let session = create_session (Some f) in
	prerr_endline "Loading: adding view";
	let index = session_notebook#append_term session in
	let av = session.analyzed_view in
	prerr_endline "Loading: stats";
	av#update_stats;
	let input_buffer = session.script#buffer in
	prerr_endline "Loading: fill buffer";
	input_buffer#set_text s;
	input_buffer#place_cursor ~where:input_buffer#start_iter;
	force_retag input_buffer;
	prerr_endline ("Loading: switch to view "^ string_of_int index);
	session_notebook#goto_page index;
	prerr_endline "Loading: highlight";
	input_buffer#set_modified false;
	prerr_endline "Loading: clear undo";
	session.script#clear_undo;
	prerr_endline "Loading: success"
      end
  with
    | e -> handler ("Load failed: "^(Printexc.to_string e))

let do_load = load_file flash_info

let saveall_f () =
  List.iter
    (function
       | {script = view ; analyzed_view = av} ->
           begin match av#filename with
             | None -> ()
             | Some f ->
		 ignore (av#save f)
           end
    )  session_notebook#pages

let forbid_quit_to_save () =
    begin try save_pref() with e -> flash_info "Cannot save preferences" end;
    (if List.exists
      (function
        | {script=view} -> view#buffer#modified
      )
      session_notebook#pages then
      match (GToolbox.question_box ~title:"Quit"
               ~buttons:["Save Named Buffers and Quit";
                         "Quit without Saving";
                         "Don't Quit"]
               ~default:0
               ~icon:
               (let img = GMisc.image () in
                img#set_stock `DIALOG_WARNING;
                img#set_icon_size `DIALOG;
                img#coerce)
               "There are unsaved buffers"
      )
      with 1 -> saveall_f () ; false
        | 2 -> false
        | _ -> true
    else false)||
      (let wait_window =
        GWindow.window ~modal:true ~wm_class:"CoqIde" ~wm_name:"CoqIde" ~kind:`POPUP
          ~title:"Terminating coqtops" () in
      let _ =
        GMisc.label ~text:"Terminating coqtops processes, please wait ..."
          ~packing:wait_window#add () in
      let warning_window =
        GWindow.message_dialog ~message_type:`WARNING ~buttons:GWindow.Buttons.yes_no
          ~message:
	  ("Some coqtops processes are still running.\n" ^
	     "If you quit CoqIDE right now, you may have to kill them manually.\n" ^
	     "Do you want to wait for those processes to terminate ?") () in
      let () = List.iter (fun _ -> session_notebook#remove_page 0) session_notebook#pages in
      let nb_try=ref (0) in
      let () = wait_window#show () in
      let () = while (Coq.coqtop_zombies () <> 0)&&(!nb_try <= 50) do
	incr nb_try;
	Thread.delay 0.1 ;
      done in
	if (!nb_try = 50) then begin
	  wait_window#misc#hide ();
	  match warning_window#run () with
	    | `YES -> warning_window#misc#hide (); true
	    | `NO | `DELETE_EVENT -> false
	end
	else false)

let main files =
  (* Statup preferences *)
  begin
    try load_pref ()
    with e ->
      flash_info ("Could not load preferences ("^Printexc.to_string e^").");
  end;

  (* Main window *)
  let w = GWindow.window
    ~wm_class:"CoqIde" ~wm_name:"CoqIde"
    ~allow_grow:true ~allow_shrink:true
    ~width:!current.window_width ~height:!current.window_height
    ~title:"CoqIde" ()
  in
  (try
     let icon_image = Filename.concat (List.find
       (fun x -> Sys.file_exists (Filename.concat x "coq.png"))
       Minilib.xdg_data_dirs) "coq.png" in
     let icon = GdkPixbuf.from_file icon_image in
     w#set_icon (Some icon)
   with _ -> ());

  let vbox = GPack.vbox ~homogeneous:false ~packing:w#add () in

  let new_f _ =
    match select_file_for_save ~title:"Create file" () with
      | None -> ()
      | Some f -> do_load f
  in
  let load_f _ =
    match select_file_for_open ~title:"Load file" () with
      | None -> ()
      | Some f -> do_load f
  in
  let save_f _ =
    let current = session_notebook#current_term in
    try
      (match current.analyzed_view#filename with
        | None ->
          begin match select_file_for_save ~title:"Save file" ()
            with
              | None -> ()
              | Some f ->
                if current.analyzed_view#save_as f then begin
                  current.tab_label#set_text (Filename.basename f);
                  flash_info ("File " ^ f ^ " saved")
                end
                else warning ("Save Failed (check if " ^ f ^ " is writable)")
          end
        | Some f ->
          if current.analyzed_view#save f then
            flash_info ("File " ^ f ^ " saved")
          else warning  ("Save Failed (check if " ^ f ^ " is writable)")

      )
    with
      | e -> warning "Save: unexpected error"
  in
  let saveas_f _ =
    let current = session_notebook#current_term in
    try (match current.analyzed_view#filename with
      | None ->
        begin match select_file_for_save ~title:"Save file as" ()
          with
            | None -> ()
            | Some f ->
              if current.analyzed_view#save_as f then begin
                current.tab_label#set_text (Filename.basename f);
                flash_info "Saved"
              end
              else flash_info "Save Failed"
        end
      | Some f ->
        begin match select_file_for_save
            ~dir:(ref (Filename.dirname f))
            ~filename:(Filename.basename f)
            ~title:"Save file as" ()
          with
            | None -> ()
            | Some f ->
              if current.analyzed_view#save_as f then begin
                current.tab_label#set_text (Filename.basename f);
                flash_info "Saved"
              end else flash_info "Save Failed"
        end);
    with e -> flash_info "Save Failed"
  in
  let revert_f {analyzed_view = av} =
    (try
       match av#filename,av#stats with
         | Some f,Some stats ->
           let new_stats = Unix.stat f in
           if new_stats.Unix.st_mtime > stats.Unix.st_mtime
           then av#revert
         | Some _, None -> av#revert
         | _ -> ()
     with _ -> av#revert)
  in
  let export_f kind _ =
    let v = session_notebook#current_term in
    let av = v.analyzed_view in
    match av#filename with
      | None ->
        flash_info "Cannot print: this buffer has no name"
      | Some f ->
        let basef = Filename.basename f in
        let output =
          let basef_we = try Filename.chop_extension basef with _ -> basef in
          match kind with
            | "latex" -> basef_we ^ ".tex"
            | "dvi" | "ps" | "pdf" | "html" -> basef_we ^ "." ^ kind
            | _ -> assert false
        in
        let cmd =
          local_cd f ^ !current.cmd_coqdoc ^ " --" ^ kind ^
	    " -o " ^ (Filename.quote output) ^ " " ^ (Filename.quote basef)
        in
        let s,_ = run_command av#insert_message cmd in
        flash_info (cmd ^
                      if s = Unix.WEXITED 0
                      then " succeeded"
                      else " failed")
  in
  let quit_f _ = if not (forbid_quit_to_save ()) then exit 0 in
  let get_active_view_for_cp () =
    let has_sel (i0,i1) = i0#compare i1 <> 0 in
    let current = session_notebook#current_term in
    if has_sel current.script#buffer#selection_bounds
    then current.script#as_view
    else if has_sel current.proof_view#buffer#selection_bounds
    then current.proof_view#as_view
    else current.message_view#as_view
  in
  (*
    let toggle_auto_complete_i =
    edit_f#add_check_item "_Auto Completion"
    ~active:!current.auto_complete
    ~callback:
    in
  *)
  (*
    auto_complete :=
    (fun b -> match session_notebook#current_term.analyzed_view with
    | Some av -> av#set_auto_complete b
    | None -> ());
  *)

(* begin of find/replace mechanism *)
  let last_found = ref None in
  let search_backward = ref false in
  let find_w = GWindow.window
    (* ~wm_class:"CoqIde" ~wm_name:"CoqIde" *)
    (* ~allow_grow:true ~allow_shrink:true *)
    (* ~width:!current.window_width ~height:!current.window_height *)
    ~position:`CENTER
    ~title:"CoqIde search/replace" ()
  in
  let find_box = GPack.table
    ~columns:3 ~rows:5
    ~col_spacings:10 ~row_spacings:10 ~border_width:10
    ~homogeneous:false ~packing:find_w#add () in

  let _ =
    GMisc.label ~text:"Find:"
      ~xalign:1.0
      ~packing:(find_box#attach ~left:0 ~top:0 ~fill:`X) ()
  in
  let find_entry = GEdit.entry
    ~editable: true
    ~packing: (find_box#attach ~left:1 ~top:0 ~expand:`X)
    ()
  in
  let _ =
    GMisc.label ~text:"Replace with:"
      ~xalign:1.0
      ~packing:(find_box#attach ~left:0 ~top:1 ~fill:`X) ()
  in
  let replace_entry = GEdit.entry
    ~editable: true
    ~packing: (find_box#attach ~left:1 ~top:1 ~expand:`X)
    ()
  in
  (* let _ =
     GButton.check_button
     ~label:"case sensitive"
     ~active:true
     ~packing: (find_box#attach ~left:1 ~top:2)
     ()
     in
  *)
  let find_backwards_check =
    GButton.check_button
      ~label:"search backwards"
      ~active:!search_backward
      ~packing: (find_box#attach ~left:1 ~top:3)
      ()
  in
  let close_find_button =
    GButton.button
      ~label:"Close"
      ~packing: (find_box#attach ~left:2 ~top:2)
      ()
  in
  let replace_find_button =
    GButton.button
      ~label:"Replace and find"
      ~packing: (find_box#attach ~left:2 ~top:1)
      ()
  in
  let find_again_button =
    GButton.button
      ~label:"_Find again"
      ~packing: (find_box#attach ~left:2 ~top:0)
      ()
  in
  let last_find () =
    let v = session_notebook#current_term.script in
    let b = v#buffer in
    let start,stop =
      match !last_found with
	| None -> let i = b#get_iter_at_mark `INSERT in (i,i)
	| Some(start,stop) ->
	  let start = b#get_iter_at_mark start
	  and stop = b#get_iter_at_mark stop
	  in
	  b#remove_tag Tags.Script.found ~start ~stop;
	  last_found:=None;
	  start,stop
    in
    (v,b,start,stop)
  in
  let do_replace () =
    let v = session_notebook#current_term.script in
    let b = v#buffer in
    match !last_found with
      | None -> ()
      | Some(start,stop) ->
	let start = b#get_iter_at_mark start
	and stop = b#get_iter_at_mark stop
	in
	b#delete ~start ~stop;
	b#insert ~iter:start replace_entry#text;
	last_found:=None
  in
  let find_from (v : Undo.undoable_view)
      (b : GText.buffer) (starti : GText.iter) text =
    prerr_endline ("Searching for " ^ text);
    match (if !search_backward then starti#backward_search text
      else starti#forward_search text)
    with
      | None -> ()
      | Some(start,stop) ->
	b#apply_tag Tags.Script.found ~start ~stop;
	let start = `MARK (b#create_mark start)
	and stop = `MARK (b#create_mark stop)
	in
	v#scroll_to_mark ~use_align:false ~yalign:0.75 ~within_margin:0.25
	  stop;
	last_found := Some(start,stop)
  in
  let do_find () =
    let (v,b,starti,_) = last_find () in
    find_from v b starti find_entry#text
  in
  let do_replace_find () =
    do_replace();
    do_find()
  in
  let close_find () =
    let (v,b,_,stop) = last_find () in
    b#place_cursor ~where:stop;
    find_w#misc#hide();
    v#coerce#misc#grab_focus()
  in
  to_do_on_page_switch :=
    (fun i -> if find_w#misc#visible then close_find())::
    !to_do_on_page_switch;
  let find_again () =
    let (v,b,start,_) = last_find () in
    let start =
      if !search_backward
      then start#backward_chars 1
      else start#forward_chars 1
    in
    find_from v b start find_entry#text
  in
  let click_on_backward () =
    search_backward := not !search_backward
  in
  let key_find ev =
    let s = GdkEvent.Key.state ev and k = GdkEvent.Key.keyval ev in
    if k = GdkKeysyms._Escape then
      begin
	let (v,b,_,stop) = last_find () in
	find_w#misc#hide();
	v#coerce#misc#grab_focus();
	true
      end
    else if k = GdkKeysyms._Escape then
      begin
	close_find();
	true
      end
    else if k = GdkKeysyms._Return ||
	   List.mem `CONTROL s && k = GdkKeysyms._f then
      begin
	find_again ();
	true
      end
    else if List.mem `CONTROL s && k = GdkKeysyms._b then
      begin
	find_backwards_check#set_active (not !search_backward);
	true
      end
    else false (* to let default callback execute *)
  in
  let find_f ~backward () =
    let save_dir = !search_backward in
    search_backward := backward;
    find_w#show ();
    find_w#present ();
    find_entry#misc#grab_focus ();
    search_backward := save_dir
  in
  let _ = find_again_button#connect#clicked find_again in
  let _ = close_find_button#connect#clicked close_find in
  let _ = replace_find_button#connect#clicked do_replace_find in
  let _ = find_backwards_check#connect#clicked click_on_backward in
  let _ = find_entry#connect#changed do_find in
  let _ = find_entry#event#connect#key_press ~callback:key_find in
  let _ = find_w#event#connect#delete ~callback:(fun _ -> find_w#misc#hide(); true) in
  (*
    let search_if = edit_f#add_item "Search _forward"
    ~key:GdkKeysyms._greater
    in
    let search_ib = edit_f#add_item "Search _backward"
    ~key:GdkKeysyms._less
    in
  *)
  (*
    let complete_i = edit_f#add_item "_Complete"
    ~key:GdkKeysyms._comma
    ~callback:
    (do_if_not_computing
    (fun b ->
    let v = session_notebook#current_term.analyzed_view

    in v#complete_at_offset
    ((v#view#buffer#get_iter `SEL_BOUND)#offset)
    ))
    in
    complete_i#misc#set_state `INSENSITIVE;
  *)
(* end of find/replace mechanism *)
(* begin Preferences *)
  let reset_revert_timer () =
    disconnect_revert_timer ();
    if !current.global_auto_revert then
      revert_timer := Some
	(GMain.Timeout.add ~ms:!current.global_auto_revert_delay
	   ~callback:
	   (fun () ->
	     do_if_not_computing "revert" (sync revert_f) session_notebook#pages;
	     true))
  in reset_revert_timer (); (* to enable statup preferences timer *)
  (* XXX *)
  let auto_save_f {analyzed_view = av} =
    (try
       av#auto_save
     with _ -> ())
  in

  let reset_auto_save_timer () =
    disconnect_auto_save_timer ();
    if !current.auto_save then
      auto_save_timer := Some
	(GMain.Timeout.add ~ms:!current.auto_save_delay
	   ~callback:
	   (fun () ->
	     do_if_not_computing "autosave" (sync auto_save_f) session_notebook#pages;
	     true))
  in reset_auto_save_timer (); (* to enable statup preferences timer *)
(* end Preferences *)
  let do_or_activate f () =
    do_if_not_computing "do_or_activate"
      (fun current ->
        let av = current.analyzed_view in
        ignore (f av);
        pop_info ();
        let msg = match Coq.status !(current.toplvl) with
        | Interface.Fail (l, str) ->
          "Oops, problem while fetching coq status."
        | Interface.Good status ->
          let path = match status.Interface.status_path with
          | [] | _ :: [] -> "" (* Drop the topmost level, usually "Top" *)
          | _ :: l -> " in " ^ String.concat "." l
          in
          let name = match status.Interface.status_proofname with
          | None -> ""
          | Some n -> ", proving " ^ n
          in
          "Ready" ^ path ^ name
        in
        push_info msg
      )
      [session_notebook#current_term]
  in
  let do_if_active f _ =
    do_if_not_computing "do_if_active"
      (fun sess -> ignore (f sess.analyzed_view))
      [session_notebook#current_term] in
  let match_callback _ =
    let w = get_current_word () in
    let cur_ct = !(session_notebook#current_term.toplvl) in
    try
      match Coq.mkcases cur_ct w with
        | Interface.Fail _ -> raise Not_found
        | Interface.Good cases ->
          let print_branch c l =
	    Format.fprintf c " | @[<hov 1>%a@]=> _@\n"
	      (print_list (fun c s -> Format.fprintf c "%s@ " s)) l
          in
          let b = Buffer.create 1024 in
          let fmt = Format.formatter_of_buffer b in
          Format.fprintf fmt "@[match var with@\n%aend@]@."
            (print_list print_branch) cases;
          let s = Buffer.contents b in
          prerr_endline s;
          let {script = view } = session_notebook#current_term in
          ignore (view#buffer#delete_selection ());
          let m = view#buffer#create_mark
            (view#buffer#get_iter `INSERT)
          in
          if view#buffer#insert_interactive s then
            let i = view#buffer#get_iter (`MARK m) in
            let _ = i#nocopy#forward_chars 9 in
            view#buffer#place_cursor ~where:i;
            view#buffer#move_mark ~where:(i#backward_chars 3)
              `SEL_BOUND
    with Not_found -> flash_info "Not an inductive type"
  in
(* External command callback *)
  let compile_f _ =
    let v = session_notebook#current_term in
    let av = v.analyzed_view in
    save_f ();
    match av#filename with
      | None ->
	flash_info "Active buffer has no name"
      | Some f ->
	let cmd = !current.cmd_coqc ^ " -I "
	  ^ (Filename.quote (Filename.dirname f))
	  ^ " " ^ (Filename.quote f) in
	let s,res = run_command av#insert_message cmd in
	if s = Unix.WEXITED 0 then
	  flash_info (f ^ " successfully compiled")
	else begin
	  flash_info (f ^ " failed to compile");
	  av#process_until_end_or_error;
	  av#insert_message "Compilation output:\n";
	  av#insert_message res
	end
  in
  let make_f _ =
    let v = session_notebook#current_term in
    let av = v.analyzed_view in
    match av#filename with
      | None ->
	flash_info "Cannot make: this buffer has no name"
      | Some f ->
	let cmd = local_cd f ^ !current.cmd_make in

	(*
	  save_f ();
	*)
	av#insert_message "Command output:\n";
	let s,res = run_command av#insert_message cmd in
	last_make := res;
	last_make_index := 0;
	flash_info (!current.cmd_make ^ if s = Unix.WEXITED 0 then " succeeded" else " failed")
  in
  let next_error _ =
    try
      let file,line,start,stop,error_msg = search_next_error () in
      do_load file;
      let v = session_notebook#current_term in
      let av = v.analyzed_view in
      let input_buffer = v.script#buffer in
      (*
	let init = input_buffer#start_iter in
	let i = init#forward_lines (line-1) in
      *)
      (*
	let convert_pos = byte_offset_to_char_offset phrase in
	let start = convert_pos start in
	let stop = convert_pos stop in
      *)
      (*
	let starti = i#forward_chars start in
	let stopi = i#forward_chars stop in
      *)
      let starti = input_buffer#get_iter_at_byte ~line:(line-1) start in
      let stopi = input_buffer#get_iter_at_byte ~line:(line-1) stop in
      input_buffer#apply_tag Tags.Script.error
	~start:starti
	~stop:stopi;
      input_buffer#place_cursor ~where:starti;
      av#set_message error_msg;
      v.script#misc#grab_focus ()
    with Not_found ->
      last_make_index := 0;
      let v = session_notebook#current_term in
      let av = v.analyzed_view in
      av#set_message "No more errors.\n"
  in
  let coq_makefile_f _ =
    let v = session_notebook#current_term in
    let av = v.analyzed_view in
    match av#filename with
      | None ->
	flash_info "Cannot make makefile: this buffer has no name"
      | Some f ->
	let cmd = local_cd f ^ !current.cmd_coqmakefile in
	let s,res = run_command av#insert_message cmd in
	flash_info
	  (!current.cmd_coqmakefile ^ if s = Unix.WEXITED 0 then " succeeded" else " failed")
  in

  let file_actions = GAction.action_group ~name:"File" () in
  let export_actions = GAction.action_group ~name:"Export" () in
  let edit_actions = GAction.action_group ~name:"Edit" () in
  let navigation_actions = GAction.action_group ~name:"Navigation" () in
  let tactics_actions = GAction.action_group ~name:"Tactics" () in
  let templates_actions = GAction.action_group ~name:"Templates" () in
  let queries_actions = GAction.action_group ~name:"Queries" () in
  let display_actions = GAction.action_group ~name:"Display" () in
  let compile_actions = GAction.action_group ~name:"Compile" () in
  let windows_actions = GAction.action_group ~name:"Windows" () in
  let help_actions = GAction.action_group ~name:"Help" () in
  let add_gen_actions menu_name act_grp l =
    let no_under = Minilib.string_map (fun x -> if x = '_' then '-' else x) in
    let add_simple_template menu_name act_grp text =
      let text' =
	let l = String.length text - 1 in
	if String.get text l = '.'
	then text ^"\n"
	else text ^" "
      in
      GAction.add_action (menu_name^" "^(no_under text)) ~label:text
	~callback:(fun _ -> let {script = view } = session_notebook#current_term in
			    ignore (view#buffer#insert_interactive text')) act_grp
    in
    List.iter (function
      | [] -> ()
      | [s] -> add_simple_template menu_name act_grp s
      | s::_ as ll -> let label = "_@..." in label.[1] <- s.[0];
		      GAction.add_action (menu_name^" "^(String.make 1 s.[0])) ~label act_grp;
		      List.iter (add_simple_template menu_name act_grp) ll
    ) l
  in
  let tactic_shortcut s sc = GAction.add_action s ~label:("_"^s)
    ~accel:(!current.modifier_for_tactics^sc)
    ~callback:(do_if_active (fun a -> a#insert_command
			       ("progress "^s^".\n") (s^".\n"))) in
  let query_shortcut s accel = GAction.add_action s ~label:("_"^s) ?accel
    ~callback:(fun _ -> let term = get_current_word () in
		 session_notebook#current_term.command#new_command ~command:s ~term ())
  in let add_complex_template (name, label, text, offset, len, key) =
    (* Templates/Lemma *)
    let callback _ =
      let {script = view } = session_notebook#current_term in
      if view#buffer#insert_interactive text then begin
	let iter = view#buffer#get_iter_at_mark `INSERT in
	ignore (iter#nocopy#backward_chars offset);
	view#buffer#move_mark `INSERT ~where:iter;
	ignore (iter#nocopy#backward_chars len);
	view#buffer#move_mark `SEL_BOUND ~where:iter;
      end in
      match key with
	|Some ac -> GAction.add_action name ~label ~callback ~accel:(!current.modifier_for_templates^ac)
	|None -> GAction.add_action name ~label ~callback ?accel:None
  in
    GAction.add_actions file_actions [
      GAction.add_action "File" ~label:"_File";
      GAction.add_action "New" ~callback:new_f ~stock:`NEW;
      GAction.add_action "Open" ~callback:load_f ~stock:`OPEN;
      GAction.add_action "Save" ~callback:save_f ~stock:`SAVE ~tooltip:"Save current buffer";
      GAction.add_action "Save as" ~label:"S_ave as" ~callback:saveas_f ~stock:`SAVE_AS;
      GAction.add_action "Save all" ~label:"Sa_ve all" ~callback:(fun _ -> saveall_f ());
      GAction.add_action "Revert all buffers" ~label:"_Revert all buffers" ~callback:(fun _ -> List.iter revert_f session_notebook#pages) ~stock:`REVERT_TO_SAVED;
      GAction.add_action "Close buffer" ~label:"_Close buffer" ~callback:(fun _ -> remove_current_view_page ()) ~stock:`CLOSE ~tooltip:"Close current buffer";
      GAction.add_action "Print..." ~label:"_Print..." ~callback:(fun _ -> do_print session_notebook#current_term) ~stock:`PRINT ~accel:"<Ctrl>p";
      GAction.add_action "Rehighlight" ~label:"Reh_ighlight" ~accel:"<Ctrl>l"
	~callback:(fun _ -> force_retag
                     session_notebook#current_term.script#buffer;
		     session_notebook#current_term.analyzed_view#recenter_insert)
	~stock:`REFRESH;
      GAction.add_action "Quit" ~callback:quit_f ~stock:`QUIT;
    ];
    GAction.add_actions export_actions [
      GAction.add_action "Export to" ~label:"E_xport to";
      GAction.add_action "Html" ~label:"_Html" ~callback:(export_f "html");
      GAction.add_action "Latex" ~label:"_LaTeX" ~callback:(export_f "latex");
      GAction.add_action "Dvi" ~label:"_Dvi" ~callback:(export_f "dvi");
      GAction.add_action "Pdf" ~label:"_Pdf" ~callback:(export_f "pdf");
      GAction.add_action "Ps" ~label:"_Ps" ~callback:(export_f "ps");
    ];
    GAction.add_actions edit_actions [
      GAction.add_action "Edit" ~label:"_Edit";
      GAction.add_action "Undo" ~accel:"<Ctrl>u"
	~callback:(fun _ -> do_if_not_computing "undo"
		     (fun sess ->
			ignore (sess.analyzed_view#without_auto_complete
				  (fun () -> session_notebook#current_term.script#undo) ()))
		     [session_notebook#current_term]) ~stock:`UNDO;
      GAction.add_action "Clear Undo Stack" ~label:"_Clear Undo Stack"
	~callback:(fun _ -> ignore session_notebook#current_term.script#clear_undo);
      GAction.add_action "Cut" ~callback:(fun _ -> GtkSignal.emit_unit
					    (get_active_view_for_cp ())
					    ~sgn:GtkText.View.S.cut_clipboard
					 ) ~stock:`CUT;
      GAction.add_action "Copy" ~callback:(fun _ -> GtkSignal.emit_unit
             (get_active_view_for_cp ())
             ~sgn:GtkText.View.S.copy_clipboard) ~stock:`COPY;
      GAction.add_action "Paste" ~callback:(fun _ ->
             try GtkSignal.emit_unit
                   session_notebook#current_term.script#as_view
                   ~sgn:GtkText.View.S.paste_clipboard
             with _ -> prerr_endline "EMIT PASTE FAILED") ~stock:`PASTE;
      GAction.add_action "Find in buffer" ~label:"_Find in buffer" ~callback:(fun _ -> find_f ~backward:false ()) ~stock:`FIND;
      GAction.add_action "Find backwards" ~label:"Find _backwards" ~callback:(fun _ -> find_f ~backward:true ()) ~accel:"<Ctrl>b";
      GAction.add_action "Complete Word" ~label:"Complete Word" ~callback:(fun _ ->
	     ignore (
	       let av = session_notebook#current_term.analyzed_view in
	       av#complete_at_offset (av#get_insert)#offset
	     )) ~accel:"<Ctrl>slash";
      GAction.add_action "External editor" ~label:"External editor" ~callback:(fun _ ->
	let av = session_notebook#current_term.analyzed_view in
	match av#filename with
	  | None -> warning "Call to external editor available only on named files"
	  | Some f ->
	    save_f ();
	    let com = Minilib.subst_command_placeholder !current.cmd_editor (Filename.quote f) in
	    let _ = run_command av#insert_message com in
	    av#revert) ~stock:`EDIT;
      GAction.add_action "Preferences" ~callback:(fun _ ->
	begin
	  try configure ~apply:update_notebook_pos ()
	  with _ -> flash_info "Cannot save preferences"
	end;
	reset_revert_timer ()) ~stock:`PREFERENCES;
      (* GAction.add_action "Save preferences" ~label:"_Save preferences" ~callback:(fun _ -> save_pref ()); *) ];
    GAction.add_actions navigation_actions [
      GAction.add_action "Navigation" ~label:"_Navigation";
      GAction.add_action "Forward" ~label:"_Forward" ~stock:`GO_DOWN
	~callback:(fun _ -> do_or_activate (fun a -> a#process_next_phrase true) ())
	~tooltip:"Forward one command" ~accel:(!current.modifier_for_navigation^"Down");
      GAction.add_action "Backward" ~label:"_Backward" ~stock:`GO_UP
	~callback:(fun _ -> do_or_activate (fun a -> a#undo_last_step) ())
	~tooltip:"Backward one command" ~accel:(!current.modifier_for_navigation^"Up");
      GAction.add_action "Go to" ~label:"_Go to" ~stock:`JUMP_TO
	~callback:(fun _ -> do_or_activate (fun a -> a#go_to_insert) ())
	~tooltip:"Go to cursor" ~accel:(!current.modifier_for_navigation^"Right");
      GAction.add_action "Start" ~label:"_Start" ~stock:`GOTO_TOP
	~callback:(fun _ -> force_reset_initial ())
	~tooltip:"Restart coq" ~accel:(!current.modifier_for_navigation^"Home");
      GAction.add_action "End" ~label:"_End" ~stock:`GOTO_BOTTOM
	~callback:(fun _ -> do_or_activate (fun a -> a#process_until_end_or_error) ())
	~tooltip:"Go to end" ~accel:(!current.modifier_for_navigation^"End");
      GAction.add_action "Interrupt" ~label:"_Interrupt" ~stock:`STOP
	~callback:(fun _ -> break ()) ~tooltip:"Interrupt computations"
	~accel:(!current.modifier_for_navigation^"Break");
      GAction.add_action "Hide" ~label:"_Hide" ~stock:`MISSING_IMAGE
	~callback:(fun _ -> let sess = session_notebook#current_term in
		     toggle_proof_visibility sess.script#buffer
		       sess.analyzed_view#get_insert) ~tooltip:"Hide proof"
	~accel:(!current.modifier_for_navigation^"h");
      GAction.add_action "Previous" ~label:"_Previous" ~stock:`GO_BACK
	~callback:(fun _ -> do_or_activate (fun a -> a#go_to_prev_occ_of_cur_word) ())
	~tooltip:"Previous occurence" ~accel:(!current.modifier_for_navigation^"less");
      GAction.add_action "Next" ~label:"_Next" ~stock:`GO_FORWARD
	~callback:(fun _ -> do_or_activate (fun a -> a#go_to_next_occ_of_cur_word) ())
	~tooltip:"Next occurence" ~accel:(!current.modifier_for_navigation^"greater");
    ];
    GAction.add_actions tactics_actions [
      GAction.add_action "Try Tactics" ~label:"_Try Tactics";
      GAction.add_action "Wizard" ~tooltip:"Proof Wizard" ~label:"<Proof Wizard>"
	~stock:`DIALOG_INFO ~callback:(do_if_active (fun a -> a#tactic_wizard
						       !current.automatic_tactics))
	~accel:(!current.modifier_for_tactics^"dollar");
      tactic_shortcut "auto" "a";
      tactic_shortcut "auto with *" "asterisk";
      tactic_shortcut "eauto" "e";
      tactic_shortcut "eauto with *" "ampersand";
      tactic_shortcut "intuition" "i";
      tactic_shortcut "omega" "o";
      tactic_shortcut "simpl" "s";
      tactic_shortcut "tauto" "p";
      tactic_shortcut "trivial" "v";
    ];
    add_gen_actions "Tactic" tactics_actions Coq_commands.tactics;
    GAction.add_actions templates_actions [
      GAction.add_action "Templates" ~label:"Te_mplates";
      add_complex_template
	("Lemma", "_Lemma __", "Lemma new_lemma : .\nIdeproof.\n\nSave.\n",
	 19, 9, Some "L");
      add_complex_template
	("Theorem", "_Theorem __", "Theorem new_theorem : .\nIdeproof.\n\nSave.\n",
	 19, 11, Some "T");
      add_complex_template
	("Definition", "_Definition __", "Definition ident := .\n",
	 6, 5, Some "D");
      add_complex_template
	("Inductive", "_Inductive __", "Inductive ident : :=\n  | : .\n",
	 14, 5, Some "I");
      add_complex_template
	("Fixpoint", "_Fixpoint __", "Fixpoint ident (_ : _) {struct _} : _ :=\n.\n",
	 29, 5, Some "F");
      add_complex_template ("Scheme", "_Scheme __",
			    "Scheme new_scheme := Induction for _ Sort _\
\nwith _ := Induction for _ Sort _.\n",61,10, Some "S");
      GAction.add_action "match" ~label:"match ..." ~callback:match_callback
	~accel:(!current.modifier_for_templates^"C");
    ];
    add_gen_actions "Template" templates_actions Coq_commands.commands;
    GAction.add_actions queries_actions [
      GAction.add_action "Queries" ~label:"_Queries";
      query_shortcut "SearchAbout" (Some "F2");
      query_shortcut "Check" (Some "F3");
      query_shortcut "Print" (Some "F4");
      query_shortcut "About" (Some "F5");
      query_shortcut "Locate" None;
      query_shortcut "Whelp Locate" None;
    ];
    GAction.add_action "Display" ~label:"_Display" display_actions;
    List.iter
      (fun (opts,name,label,key,dflt) ->
         GAction.add_toggle_action name ~active:dflt ~label
	   ~accel:(!current.modifier_for_display^key)
          ~callback:(fun v -> do_or_activate (fun a ->
            let () = setopts !(session_notebook#current_term.toplvl) opts v#get_active in
            a#show_goals) ()) display_actions)
      print_items;
    GAction.add_actions compile_actions [
      GAction.add_action "Compile" ~label:"_Compile";
      GAction.add_action "Compile buffer" ~label:"_Compile buffer" ~callback:compile_f;
      GAction.add_action "Make" ~label:"_Make" ~callback:make_f ~accel:"F6";
      GAction.add_action "Next error" ~label:"_Next error" ~callback:next_error
	~accel:"F7";
      GAction.add_action "Make makefile" ~label:"Make makefile" ~callback:coq_makefile_f;
    ];
    GAction.add_actions windows_actions [
      GAction.add_action "Windows" ~label:"_Windows";
      GAction.add_toggle_action "Show/Hide Query Pane" ~label:"Show/Hide _Query Pane"
	~callback:(fun _ -> let ccw = session_notebook#current_term.command in
		     if ccw#frame#misc#visible
		     then ccw#frame#misc#hide ()
		     else ccw#frame#misc#show ())
	~accel:"Escape";
      GAction.add_toggle_action "Show/Hide Toolbar" ~label:"Show/Hide _Toolbar"
	~active:(!current.show_toolbar) ~callback:
	(fun _ -> !current.show_toolbar <- not !current.show_toolbar;
	   !show_toolbar !current.show_toolbar);
      GAction.add_action "Detach View" ~label:"Detach _View"
	~callback:(fun _ -> do_if_not_computing "detach view"
		     (function {script=v;analyzed_view=av} ->
			let w = GWindow.window ~show:true
			  ~width:(!current.window_width*2/3)
			  ~height:(!current.window_height*2/3)
			  ~position:`CENTER
			  ~title:(match av#filename with
				    | None -> "*Unnamed*"
				    | Some f -> f)
			  ()
			in
			let sb = GBin.scrolled_window
			  ~packing:w#add ()
			in
			let nv = GText.view
			  ~buffer:v#buffer
			  ~packing:sb#add
			  ()
			in
			  nv#misc#modify_font
			    !current.text_font;
			  ignore (w#connect#destroy
				    ~callback:
				    (fun () -> av#remove_detached_view w));
			  av#add_detached_view w)
		     [session_notebook#current_term]);
    ];
    GAction.add_actions help_actions [
      GAction.add_action "Help" ~label:"_Help";
      GAction.add_action "Browse Coq Manual" ~label:"Browse Coq _Manual"
	~callback:(fun _ ->
		     let av = session_notebook#current_term.analyzed_view in
		       browse av#insert_message (doc_url ()));
      GAction.add_action "Browse Coq Library" ~label:"Browse Coq _Library"
	~callback:(fun _ ->
		     let av = session_notebook#current_term.analyzed_view in
		       browse av#insert_message !current.library_url);
      GAction.add_action "Help for keyword" ~label:"Help for _keyword"
	~callback:(fun _ -> let av = session_notebook#current_term.analyzed_view in
		     av#help_for_keyword ()) ~stock:`HELP;
      GAction.add_action "About Coq" ~label:"_About" ~stock:`ABOUT;
    ];
    Coqide_ui.init ();
    Coqide_ui.ui_m#insert_action_group file_actions 0;
    Coqide_ui.ui_m#insert_action_group export_actions 0;
    Coqide_ui.ui_m#insert_action_group edit_actions 0;
    Coqide_ui.ui_m#insert_action_group navigation_actions 0;
    Coqide_ui.ui_m#insert_action_group tactics_actions 0;
    Coqide_ui.ui_m#insert_action_group templates_actions 0;
    Coqide_ui.ui_m#insert_action_group queries_actions 0;
    Coqide_ui.ui_m#insert_action_group display_actions 0;
    Coqide_ui.ui_m#insert_action_group compile_actions 0;
    Coqide_ui.ui_m#insert_action_group windows_actions 0;
    Coqide_ui.ui_m#insert_action_group help_actions 0;
    w#add_accel_group Coqide_ui.ui_m#get_accel_group ;
    if Coq_config.gtk_platform <> `QUARTZ
    then vbox#pack (Coqide_ui.ui_m#get_widget "/CoqIde MenuBar");
    let tbar = GtkButton.Toolbar.cast ((Coqide_ui.ui_m#get_widget "/CoqIde ToolBar")#as_widget)
    in let () = GtkButton.Toolbar.set ~orientation:`HORIZONTAL ~style:`ICONS
	~tooltips:true tbar in
    let toolbar = new GObj.widget tbar in
    vbox#pack toolbar;

    show_toolbar :=
      (fun b -> if b then toolbar#misc#show () else toolbar#misc#hide ());

    ignore (w#event#connect#delete ~callback:(fun _ -> quit_f (); true));

  (* The vertical Separator between Scripts and Goals *)
  vbox#pack ~expand:true session_notebook#coerce;
  update_notebook_pos ();
  let nb = session_notebook in
  let lower_hbox = GPack.hbox ~homogeneous:false ~packing:vbox#pack () in
  lower_hbox#pack ~expand:true status#coerce;
  let search_lbl = GMisc.label ~text:"Search:"
    ~show:false
    ~packing:(lower_hbox#pack ~expand:false) ()
  in
  let search_history = ref [] in
  let (search_input,_) = GEdit.combo_box_entry_text ~strings:!search_history ~show:false
    ~packing:(lower_hbox#pack ~expand:false) ()
  in
  let ready_to_wrap_search = ref false in

  let start_of_search = ref None in
  let start_of_found = ref None in
  let end_of_found = ref None in
  let search_forward = ref true in
  let matched_word = ref None in

  let memo_search () =
    matched_word := Some search_input#entry#text
  in
  let end_search () =
    prerr_endline "End Search";
    memo_search ();
    let v = session_notebook#current_term.script in
    v#buffer#move_mark `SEL_BOUND ~where:(v#buffer#get_iter_at_mark `INSERT);
    v#coerce#misc#grab_focus ();
    search_input#entry#set_text "";
    search_lbl#misc#hide ();
    search_input#misc#hide ()
  in
  let end_search_focus_out () =
    prerr_endline "End Search(focus out)";
    memo_search ();
    let v = session_notebook#current_term.script in
    v#buffer#move_mark `SEL_BOUND ~where:(v#buffer#get_iter_at_mark `INSERT);
    search_input#entry#set_text "";
    search_lbl#misc#hide ();
    search_input#misc#hide ()
  in
  ignore (search_input#entry#connect#activate ~callback:end_search);
  ignore (search_input#entry#event#connect#key_press
	    ~callback:(fun k -> let kv = GdkEvent.Key.keyval k in
				if
				  kv = GdkKeysyms._Right
				  || kv = GdkKeysyms._Up
				    || kv = GdkKeysyms._Left
				      || (kv = GdkKeysyms._g
					 && (List.mem `CONTROL (GdkEvent.Key.state k)))
				then end_search ();
				false));
  ignore (search_input#entry#event#connect#focus_out
	    ~callback:(fun _ -> end_search_focus_out (); false));
  to_do_on_page_switch :=
    (fun i ->
      start_of_search := None;
      ready_to_wrap_search:=false)::!to_do_on_page_switch;

  (* TODO : make it work !!! *)
  let rec search_f () =
    search_lbl#misc#show ();
    search_input#misc#show ();

    prerr_endline "search_f called";
    if !start_of_search = None then begin
      (* A full new search is starting *)
      start_of_search :=
	Some (session_notebook#current_term.script#buffer#create_mark
		(session_notebook#current_term.script#buffer#get_iter_at_mark `INSERT));
      start_of_found := !start_of_search;
      end_of_found := !start_of_search;
      matched_word := Some "";
    end;
    let txt = search_input#entry#text in
    let v = session_notebook#current_term.script in
    let iit = v#buffer#get_iter_at_mark `SEL_BOUND
    and insert_iter = v#buffer#get_iter_at_mark `INSERT
    in
    prerr_endline ("SELBOUND="^(string_of_int iit#offset));
    prerr_endline ("INSERT="^(string_of_int insert_iter#offset));

    (match
	if !search_forward then iit#forward_search txt
	else let npi = iit#forward_chars (Glib.Utf8.length txt) in
	     match
	       (npi#offset = (v#buffer#get_iter_at_mark `INSERT)#offset),
	       (let t = iit#get_text ~stop:npi in
		flash_info (t^"\n"^txt);
		t = txt)
	     with
	       | true,true ->
		 (flash_info "T,T";iit#backward_search txt)
	       | false,true -> flash_info "F,T";Some (iit,npi)
	       | _,false ->
		 (iit#backward_search txt)

     with
       | None ->
	 if !ready_to_wrap_search then begin
	   ready_to_wrap_search := false;
	   flash_info "Search wrapped";
	   v#buffer#place_cursor
	     ~where:(if !search_forward then v#buffer#start_iter else
		 v#buffer#end_iter);
	   search_f ()
	 end else begin
	   if !search_forward then flash_info "Search at end"
	   else flash_info "Search at start";
	   ready_to_wrap_search := true
	 end
       | Some (start,stop) ->
	 prerr_endline "search: before moving marks";
	 prerr_endline ("SELBOUND="^(string_of_int (v#buffer#get_iter_at_mark `SEL_BOUND)#offset));
	 prerr_endline ("INSERT="^(string_of_int (v#buffer#get_iter_at_mark `INSERT)#offset));

	 v#buffer#move_mark `SEL_BOUND ~where:start;
	 v#buffer#move_mark `INSERT ~where:stop;
	 prerr_endline "search: after moving marks";
	 prerr_endline ("SELBOUND="^(string_of_int (v#buffer#get_iter_at_mark `SEL_BOUND)#offset));
	 prerr_endline ("INSERT="^(string_of_int (v#buffer#get_iter_at_mark `INSERT)#offset));
	 v#scroll_to_mark `SEL_BOUND
    )
  in
  ignore (search_input#entry#event#connect#key_release
	    ~callback:
	    (fun ev ->
	      if GdkEvent.Key.keyval ev = GdkKeysyms._Escape then begin
		let v = session_notebook#current_term.script in
		(match !start_of_search with
		  | None ->
		    prerr_endline "search_key_rel: Placing sel_bound";
		    v#buffer#move_mark
		      `SEL_BOUND
		      ~where:(v#buffer#get_iter_at_mark `INSERT)
		  | Some mk -> let it = v#buffer#get_iter_at_mark
				 (`MARK mk) in
			       prerr_endline "search_key_rel: Placing cursor";
			       v#buffer#place_cursor ~where:it;
			       start_of_search := None
		);
		search_input#entry#set_text "";
		v#coerce#misc#grab_focus ();
	      end;
	      false
	    ));
  ignore (search_input#entry#connect#changed ~callback:search_f);
  push_info "Ready";
  (* Location display *)
  let l = GMisc.label
    ~text:"Line:     1 Char:   1"
    ~packing:lower_hbox#pack () in
  l#coerce#misc#set_name "location";
  set_location := l#set_text;
  (* Progress Bar *)
  lower_hbox#pack pbar#coerce;
  pbar#set_text "CoqIde started";
  (* XXX *)
  change_font :=
    (fun fd ->
      List.iter
	(fun {script=view; proof_view=prf_v; message_view=msg_v} ->
          view#misc#modify_font fd;
          prf_v#misc#modify_font fd;
          msg_v#misc#modify_font fd
        )
	session_notebook#pages;
    );
  let about_full_string =
    "\nCoq is developed by the Coq Development Team\
     \n(INRIA - CNRS - LIX - LRI - PPS)\
     \nWeb site: " ^ Coq_config.wwwcoq ^
    "\nFeature wish or bug report: http://coq.inria.fr/bugs/\
     \n\
     \nCredits for CoqIDE, the Integrated Development Environment for Coq:\
     \n\
     \nMain author  : Benjamin Monate\
     \nContributors : Jean-Christophe Filliâtre\
     \n               Pierre Letouzey, Claude Marché\
     \n               Bruno Barras, Pierre Corbineau\
     \n               Julien Narboux, Hugo Herbelin, ... \
     \n\
     \nVersion information\
     \n-------------------\
     \n"
  in
  let initial_about (b:GText.buffer) =
    let initial_string =
      "Welcome to CoqIDE, an Integrated Development Environment for Coq\n"
    in
    let coq_version = Coq.short_version () in
    b#insert ~iter:b#start_iter "\n\n";
    if Glib.Utf8.validate ("You are running " ^ coq_version) then
      b#insert ~iter:b#start_iter ("You are running " ^ coq_version);
    if Glib.Utf8.validate initial_string then
      b#insert ~iter:b#start_iter initial_string;
    (try
       let image = Filename.concat (List.find
	 (fun x -> Sys.file_exists (Filename.concat x "coq.png"))
	 Minilib.xdg_data_dirs) "coq.png" in
       let startup_image = GdkPixbuf.from_file image in
       b#insert ~iter:b#start_iter "\n\n";
       b#insert_pixbuf ~iter:b#start_iter ~pixbuf:startup_image;
       b#insert ~iter:b#start_iter "\n\n\t\t   "
     with _ -> ())
  in

  let about (b:GText.buffer) =
    (try
       let image = Filename.concat (List.find
	 (fun x -> Sys.file_exists (Filename.concat x "coq.png"))
	 Minilib.xdg_data_dirs) "coq.png" in
       let startup_image = GdkPixbuf.from_file image in
       b#insert ~iter:b#start_iter "\n\n";
       b#insert_pixbuf ~iter:b#start_iter ~pixbuf:startup_image;
       b#insert ~iter:b#start_iter "\n\n\t\t   "
     with _ -> ());
    if Glib.Utf8.validate about_full_string
    then b#insert about_full_string;
    let coq_version = Coq.version () in
    if Glib.Utf8.validate coq_version
    then b#insert coq_version

  in
  (* Remove default pango menu for textviews *)
  w#show ();
  ignore ((help_actions#get_action "About Coq")#connect#activate
	    ~callback:(fun _ -> let prf_v = session_notebook#current_term.proof_view in
                                 prf_v#buffer#set_text ""; about prf_v#buffer));
  (*

  *)
  resize_window := (fun () ->
    w#resize
      ~width:!current.window_width
      ~height:!current.window_height);
  ignore(nb#connect#switch_page
	   ~callback:
	   (fun i ->
	     prerr_endline ("switch_page: starts " ^ string_of_int i);
	     List.iter (function f -> f i) !to_do_on_page_switch;
	     prerr_endline "switch_page: success")
  );
  if List.length files >=1 then
    begin
      List.iter (fun f ->
	if Sys.file_exists f then do_load f else
          let f = if Filename.check_suffix f ".v" then f else f^".v" in
	  load_file (fun s -> print_endline s; exit 1) f)
        files;
      session_notebook#goto_page 0;
    end
  else
    begin
      let session = create_session None in
      let index = session_notebook#append_term session in
      session_notebook#goto_page index;
    end;
  initial_about session_notebook#current_term.proof_view#buffer;
  !show_toolbar !current.show_toolbar;
  session_notebook#current_term.script#misc#grab_focus ();;

(* This function check every half of second if GeoProof has send
   something on his private clipboard *)

let rec check_for_geoproof_input () =
  let cb_Dr = GData.clipboard (Gdk.Atom.intern "_GeoProof") in
  while true do
    Thread.delay 0.1;
    let s = cb_Dr#text in
    (match s with
	Some s ->
	  if s <> "Ack" then
	    session_notebook#current_term.script#buffer#insert (s^"\n");
	  cb_Dr#set_text "Ack"
      | None -> ()
    );
  (* cb_Dr#clear does not work so i use : *)
  (* cb_Dr#set_text "Ack" *)
  done

(** By default, the coqtop we try to launch is exactly the current coqide
    full name, with the last occurrence of "coqide" replaced by "coqtop".
    This should correctly handle the ".opt", ".byte", ".exe" situations.
    If the replacement fails, we default to "coqtop", hoping it's somewhere
    in the path. Note that the -coqtop option to coqide allows to override
    this default coqtop path *)

let default_coqtop_path () =
  let prog = Sys.executable_name in
  try
    let pos = String.length prog - 6 in
    let i = Str.search_backward (Str.regexp_string "coqide") prog pos in
    String.blit "coqtop" 0 prog i 6;
    prog
  with _ -> "coqtop"

let read_coqide_args argv =
  let rec filter_coqtop coqtop project_files out = function
    | "-coqtop" :: prog :: args ->
      if coqtop = "" then filter_coqtop prog project_files out args
      else
	(output_string stderr "Error: multiple -coqtop options"; exit 1)
    | "-f" :: file :: args ->
	filter_coqtop coqtop
	  ((Minilib.canonical_path_name (Filename.dirname file),
	    Project_file.read_project_file file) :: project_files) out args
    | "-f" :: [] -> output_string stderr "Error: missing project file name"; exit 1
    | arg::args -> filter_coqtop coqtop project_files (arg::out) args
    | [] -> ((if coqtop = "" then default_coqtop_path () else coqtop),
	     List.rev project_files,List.rev out)
  in
  let coqtop,project_files,argv = filter_coqtop "" [] [] argv in
    Minilib.coqtop_path := coqtop;
    custom_project_files := project_files;
  argv

let process_argv argv =
  try
    let continue,filtered = Coq.filter_coq_opts (List.tl argv) in
    if not continue then
      (List.iter Minilib.safe_prerr_endline filtered; exit 0);
    let opts = List.filter (fun arg -> String.get arg 0 == '-') filtered in
    if opts <> [] then
      (Minilib.safe_prerr_endline ("Illegal option: "^List.hd opts); exit 1);
    filtered
  with _ ->
    (Minilib.safe_prerr_endline "coqtop choked on one of your option"; exit 1)
