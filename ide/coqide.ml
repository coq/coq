(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Preferences
open Vernacexpr
open Coq
open Ideutils
  
let out_some s = match s with 
  | None -> failwith "Internal error in out_some" | Some f -> f
      
let cb_ = ref None
let cb () = ((out_some !cb_):GData.clipboard)
let last_cb_content = ref ""
  
let (message_view:GText.view option ref) = ref None
let (proof_view:GText.view option ref) = ref None
  
let (_notebook:GPack.notebook option ref) = ref None
let notebook () = out_some !_notebook
  
(* Tabs contain the name of the edited file and 2 status informations: 
   Saved state + Focused proof buffer *)
let decompose_tab w = 
  let vbox = new GPack.box ((Gobject.try_cast w "GtkBox"):Gtk.box Gtk.obj) in
  let l = vbox#children in
    match l with 
      | [img;lbl] -> 
	  let img = new GMisc.image 
	    ((Gobject.try_cast img#as_widget "GtkImage"):
	       Gtk.image Gtk.obj) 
	  in
	  let lbl = GMisc.label_cast lbl in
	    vbox,img,lbl
      | _ -> assert false
	  
let set_tab_label i n =
  let nb = notebook () in
  let _,_,lbl = decompose_tab (nb#get_tab_label(nb#get_nth_page i))#as_widget 
  in
    lbl#set_use_markup true;
    (* lbl#set_text n *) lbl#set_label n
    
    
let set_tab_image ~icon i = 
  let nb = notebook () in
  let _,img,_ = decompose_tab (nb#get_tab_label(nb#get_nth_page i))#as_widget
  in
    img#set_icon_size `SMALL_TOOLBAR;
    img#set_stock icon
      
let set_current_tab_image ~icon = set_tab_image ~icon (notebook())#current_page
  
let set_current_tab_label n = set_tab_label (notebook())#current_page n 
  
let get_tab_label i =
  let nb = notebook () in
  let _,_,lbl = decompose_tab (nb#get_tab_label(nb#get_nth_page i))#as_widget 
  in
    lbl#text
      
let get_full_tab_label i = 
  let nb = notebook () in
  let _,_,lbl = decompose_tab (nb#get_tab_label(nb#get_nth_page i))#as_widget 
  in
    lbl
      
let get_current_tab_label () = get_tab_label (notebook())#current_page
  
let get_current_page () = 
  let i = (notebook())#current_page in
    (notebook())#get_nth_page i
      
(* This function must remove "focused proof" decoration *)				      
let reset_tab_label i = 
  set_tab_label i (get_tab_label i)
    
let to_do_on_page_switch = ref []
  
module Vector = struct 
  exception Found of int
  type 'a t = ('a option) array ref
  let create () = ref [||]
  let length t = Array.length !t
  let get t i = out_some (Array.get !t i)
  let set t i v = Array.set !t i (Some v)
  let remove t i = Array.set !t i None
  let append t e = t := Array.append !t [|Some e|]; (Array.length !t)-1
  let iter f t =  Array.iter (function | None -> () | Some x -> f x) !t
  let find_or_fail f t = 
    let test i = function | None -> () | Some e -> if f e then raise (Found i) in 
      Array.iteri test t
	
  let exists f t =
    let l = Array.length !t in
    let rec test i = 
      (i < l) && (((!t.(i) <> None) && f (out_some !t.(i))) || test (i+1)) 
    in 
      test 0
end

type 'a viewable_script =
    {view : Undo.undoable_view;
     mutable analyzed_view : 'a option;
    }


class type analyzed_views= 
object('self)
  val mutable act_id : GtkSignal.id option
  val current_all : 'self viewable_script
  val mutable deact_id : GtkSignal.id option
  val input_buffer : GText.buffer
  val input_view : Undo.undoable_view
  val last_array : string array
  val mutable last_index : bool
  val message_buffer : GText.buffer
  val message_view : GText.view
  val proof_buffer : GText.buffer
  val proof_view : GText.view
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

  method view : Undo.undoable_view
  method filename : string option
  method stats :  Unix.stats option
  method set_filename : string option -> unit
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
  method deactivate : unit -> unit
  method disconnected_keypress_handler : GdkEvent.Key.t -> bool
  method electric_handler : GtkSignal.id
  method find_phrase_starting_at :
    GText.iter -> (GText.iter * GText.iter) option
  method get_insert : GText.iter
  method get_start_of_input : GText.iter
  method go_to_insert : unit
  method indent_current_line : unit
  method insert_command : string -> string -> unit
  method tactic_wizard : string list -> unit
  method insert_message : string -> unit
  method insert_this_phrase_on_success :
    bool -> bool -> bool -> string -> string -> bool
  method process_next_phrase : bool -> bool -> bool -> bool
  method process_until_iter_or_error : GText.iter -> unit
  method process_until_end_or_error : unit
  method recenter_insert : unit
  method reset_initial : unit
  method send_to_coq :
    bool -> bool -> string ->
    bool -> bool -> bool -> (bool*(Util.loc * Vernacexpr.vernac_expr)) option
  method set_message : string -> unit
  method show_pm_goal : unit
  method show_goals : unit
  method show_goals_full : unit
  method undo_last_step : unit
  method help_for_keyword : unit -> unit
  method complete_at_offset : int -> bool

  method blaster : unit -> unit
end

let (input_views:analyzed_views viewable_script Vector.t) = Vector.create ()


let signals_to_crash = [Sys.sigabrt; Sys.sigalrm; Sys.sigfpe; Sys.sighup; 
			Sys.sigill; Sys.sigpipe; Sys.sigquit; 
			(* Sys.sigsegv; Sys.sigterm;*) Sys.sigusr2]

let crash_save i =
  (*  ignore (Unix.sigprocmask Unix.SIG_BLOCK signals_to_crash);*)
  Pervasives.prerr_endline "Trying to save all buffers in .crashcoqide files";
  let count = ref 0 in 
    Vector.iter 
      (function {view=view; analyzed_view = Some av } -> 
	 (let filename = match av#filename with 
	    | None -> 
		incr count; 
		"Unnamed_coqscript_"^(string_of_int !count)^".crashcoqide"
	    | Some f -> f^".crashcoqide"
	  in
	    try 
	      if try_export filename (view#buffer#get_text ()) then
		Pervasives.prerr_endline ("Saved "^filename)
	      else Pervasives.prerr_endline ("Could not save "^filename)
	    with _ -> Pervasives.prerr_endline ("Could not save "^filename))
	 | _ -> Pervasives.prerr_endline "Unanalyzed view found. Please report."
      )
      input_views;
    Pervasives.prerr_endline "Done. Please report.";
    if i <> 127 then exit i

let ignore_break () =
  List.iter
    (fun i ->
       try Sys.set_signal i (Sys.Signal_handle crash_save)
       with _ -> prerr_endline "Signal ignored (normal if Win32)")
    signals_to_crash;
  Sys.set_signal Sys.sigint Sys.Signal_ignore

(* Locking machinery for Coq kernel *)
let coq_computing = Mutex.create ()

(* To prevent Coq from interrupting during undoing...*)
let coq_may_stop = Mutex.create ()

let break () = 
  prerr_endline "User break received:";
  if not (Mutex.try_lock coq_computing) then 
    begin
      prerr_endline " trying to stop computation:";
      if Mutex.try_lock coq_may_stop then begin
	  Util.interrupt := true;
	  prerr_endline " interrupt flag set. Computation should stop soon...";
	  Mutex.unlock coq_may_stop
	end else prerr_endline " interruption refused (may not stop now)";
    end
  else begin
      Mutex.unlock coq_computing;
      prerr_endline " ignored (not computing)"
    end

let do_if_not_computing text f x = 
  let threaded_task () =
    if Mutex.try_lock coq_computing 
    then 
      begin
	let w = Blaster_window.blaster_window () in
	  if not (Mutex.try_lock w#lock) then 
	    begin 
	      break ();
	      let lck = Mutex.create () in
		Mutex.lock lck;
		prerr_endline "Waiting on blaster...";
		Condition.wait w#blaster_killed lck;
		prerr_endline "Waiting on blaster ok";
		Mutex.unlock lck
	    end 
	  else 
	    Mutex.unlock w#lock;
	  let idle = 
	    Glib.Timeout.add ~ms:300
	      ~callback:(fun () -> async !pulse ();true) in
	    begin
	      prerr_endline "Getting lock";
	      try
		f x;
		Glib.Timeout.remove idle;
		prerr_endline "Releasing lock";
		Mutex.unlock coq_computing;
	      with e ->
		Glib.Timeout.remove idle;
		prerr_endline "Releasing lock (on error)";
		Mutex.unlock coq_computing;
		raise e
	    end
      end 
    else 
      prerr_endline 
	"Discarded order (computations are ongoing)" 
  in
    prerr_endline ("Launching thread " ^ text);
    ignore (Thread.create threaded_task ())

let add_input_view tv = 
  Vector.append input_views tv

let get_input_view i = 
  if 0 <= i && i < Vector.length input_views
  then
    Vector.get input_views i
  else raise Not_found 

let active_view = ref None

let get_active_view () = Vector.get input_views (out_some !active_view)

let set_active_view i = 
  (match !active_view with  None -> () | Some i -> 
     reset_tab_label i);
  (notebook ())#goto_page i; 
  let txt = get_current_tab_label () in
    set_current_tab_label ("<span background=\"light green\">"^txt^"</span>");
    active_view := Some i

let set_current_view i = (notebook ())#goto_page i

let kill_input_view i = 
  let v = Vector.get input_views i in
    (match v.analyzed_view with 
       | Some v -> v#kill_detached_views ()
       | None -> ());
    v.view#destroy ();
    v.analyzed_view <- None;
    Vector.remove input_views i

let get_current_view_page () = (notebook ())#current_page
let get_current_view () = Vector.get input_views (notebook ())#current_page
let remove_current_view_page () = 
  let c =  (notebook ())#current_page in
    kill_input_view c;
    ((notebook ())#get_nth_page c)#misc#hide ()

let is_word_char c =
  (* TODO: avoid num and prime at the head of a word *)
  Glib.Unichar.isalnum c || c = underscore || c = prime

let starts_word it = 
  prerr_endline ("Starts word ? '"^(Glib.Utf8.from_unichar it#char)^"'");
  (not it#copy#nocopy#backward_char ||
     (let c = it#backward_char#char in
	not (is_word_char c)))

let ends_word it = 
  (not it#copy#nocopy#forward_char ||
     let c = it#forward_char#char in
       not (is_word_char c)
  )

let inside_word it = 
  let c = it#char in
    not (starts_word it) &&
      not (ends_word it) &&
      is_word_char c

let is_on_word_limit it = inside_word it || ends_word it 

let rec find_word_start it =
  prerr_endline "Find word start";
  if not it#nocopy#backward_char then 
    (prerr_endline "find_word_start: cannot backward"; it)
  else if is_word_char it#char
  then find_word_start it
  else (it#nocopy#forward_char; 
	prerr_endline ("Word start at: "^(string_of_int it#offset));it)
let find_word_start (it:GText.iter) = find_word_start it#copy

let rec find_word_end it =
  prerr_endline "Find word end";
  if let c = it#char in c<>0 && is_word_char c
  then begin 
      ignore (it#nocopy#forward_char);
      find_word_end it
    end else (prerr_endline ("Word end at: "^(string_of_int it#offset));it)
let find_word_end it = find_word_end it#copy


let get_word_around it = 
  let start = find_word_start it in
  let stop =  find_word_end it in
    start,stop


let rec complete_backward w (it:GText.iter) = 
  prerr_endline "Complete backward...";
  match it#backward_search w with 
    | None -> (prerr_endline "backward_search failed";None)
    | Some (start,stop) -> 
	prerr_endline ("complete_backward got a match:"^(string_of_int start#offset)^(string_of_int stop#offset));
	if starts_word start then 
	  let ne = find_word_end stop in
	    if ne#compare stop = 0
	    then complete_backward w start
	    else Some (start,stop,ne)
	else complete_backward w start
	  
let rec complete_forward w (it:GText.iter) = 
  prerr_endline "Complete forward...";
  match it#forward_search w with 
    | None -> None
    | Some (start,stop) -> 
	if starts_word start then 	
	  let ne = find_word_end stop in
	    if ne#compare stop = 0 then 
	      complete_forward w stop
	    else Some (stop,stop,ne)
	else complete_forward w stop

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
  let av = out_some ((get_current_view ()).analyzed_view) in 
    match GtkBase.Clipboard.wait_for_text (cb ())#as_clipboard with
      | None -> 
	  prerr_endline "None selected";
	  let it = av#get_insert in
	  let start = find_word_start it in
	  let stop = find_word_end start in
	    av#view#buffer#move_mark `SEL_BOUND start;
	    av#view#buffer#move_mark `INSERT stop;
	    av#view#buffer#get_text ~slice:true ~start ~stop ()
      | Some t ->
 	  prerr_endline "Some selected";
	  prerr_endline t;
	  t
	    

let input_channel b ic =
  let buf = String.create 1024 and len = ref 0 in
    while len := input ic buf 0 1024; !len > 0 do
      Buffer.add_substring b buf 0 !len
    done

let with_file name ~f =
  let ic = open_in_gen [Open_rdonly;Open_creat] 0o644 name in
    try f ic; close_in ic with exn -> 
      close_in ic; !flash_info ("Error: "^Printexc.to_string exn)

type info =  {start:GText.mark;
	      stop:GText.mark;
	      ast:Util.loc * Vernacexpr.vernac_expr;
	      reset_info:Coq.reset_info;
	     }

exception Size of int
let (processed_stack:info Stack.t) = Stack.create ()
let push x = Stack.push x processed_stack
let pop () = try Stack.pop processed_stack with Stack.Empty -> raise (Size 0)
let top () = try Stack.top processed_stack with Stack.Empty -> raise (Size 0)
let is_empty () = Stack.is_empty processed_stack

  
(* push a new Coq phrase *)

let update_on_end_of_proof id =
  let lookup_lemma = function
    | { ast = _, ( VernacDefinition (_, _, ProveBody _, _)
	| VernacDeclareTacticDefinition _
	| VernacStartTheoremProof _) ; 
	reset_info = Reset (_, r) } -> 
	if not !r then begin 
	    prerr_endline "Toggling Reset info to true";
	    r := true; raise Exit end
	else begin
	    prerr_endline "Toggling Changing Reset id"; 
	    r := false
	  end
    | { ast = _, (VernacAbort _ | VernacAbortAll | VernacGoal _) } -> raise Exit
    | _ -> ()
  in
    try Stack.iter lookup_lemma processed_stack with Exit -> ()

let update_on_end_of_segment id =
  let lookup_section = function 
    | { ast = _, ( VernacBeginSection id'
	| VernacDefineModule (_,id',_,_,None)
	| VernacDeclareModule (_,id',_,_)
	| VernacDeclareModuleType (id',_,None)); 
	reset_info = Reset (_, r) } 
	when id = id' -> raise Exit
    | { reset_info = Reset (_, r) } -> r := false
    | _ -> ()
  in
    try Stack.iter lookup_section processed_stack with Exit -> ()

let push_phrase start_of_phrase_mark end_of_phrase_mark ast = 
  let x = {start = start_of_phrase_mark;
	   stop = end_of_phrase_mark;
	   ast = ast;
	   reset_info = Coq.compute_reset_info (snd ast)
	  } 
  in
    push x;
    match snd ast with
      | VernacEndProof (Proved (_, None)) -> update_on_end_of_proof ()
      | VernacEndSegment id -> update_on_end_of_segment id
      | _ -> ()

let repush_phrase x =
  let x = { x with reset_info = Coq.compute_reset_info (snd x.ast) } in
    push x;
    match snd x.ast with
      | VernacEndProof (Proved (_, None)) -> update_on_end_of_proof ()
      | VernacEndSegment id -> update_on_end_of_segment id
      | _ -> ()

(* For electric handlers *)
exception Found

(* For find_phrase_starting_at *)
exception Stop of int

let activate_input i = 
  (match !active_view with
     | None -> () 
     | Some n ->
	 let a_v = out_some (Vector.get input_views n).analyzed_view in
	   a_v#deactivate ();
	   a_v#reset_initial
  );
  let activate_function = (out_some (Vector.get input_views i).analyzed_view)#activate in
    activate_function ();
    set_active_view i

let warning msg = 
  GToolbox.message_box ~title:"Warning"
    ~icon:(let img = GMisc.image () in
	     img#set_stock `DIALOG_WARNING;
	     img#set_icon_size `DIALOG;
	     img#coerce)
    msg


class analyzed_view index =
  let {view = input_view_} as current_all_ =  get_input_view index in
  let proof_view_ = out_some !proof_view in
  let message_view_ = out_some !message_view in
object(self)
  val current_all =  current_all_
  val input_view = current_all_.view
  val proof_view = out_some !proof_view
  val message_view = out_some !message_view
  val input_buffer = input_view_#buffer
  val proof_buffer = proof_view_#buffer
  val message_buffer = message_view_#buffer 
  val mutable is_active = false
  val mutable read_only = false
  val mutable filename = None 
  val mutable stats = None
  val mutable last_modification_time = 0.
  val mutable last_auto_save_time = 0.
  val mutable detached_views = []

  val mutable auto_complete_on = !current.auto_complete

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

  method view = input_view
  method filename = filename
  method stats = stats
  method set_filename f = 
    filename <- f;
    match f with 
      | Some f -> stats <- my_stat f
      | None -> ()

  method update_stats = 
    match filename with 
      | Some f -> stats <- my_stat f 
      | _ -> ()

  method revert = 
    match filename with 
      | Some f -> begin
	    let do_revert () = begin
		!push_info "Reverting buffer";
		try
		  if is_active then self#reset_initial;
		  let b = Buffer.create 1024 in
		    with_file f ~f:(input_channel b);
		    let s = try_convert (Buffer.contents b) in
		      input_buffer#set_text s;
		      self#update_stats;
		      input_buffer#place_cursor input_buffer#start_iter;
		      input_buffer#set_modified false;
		      !pop_info ();
		      !flash_info "Buffer reverted";
		      Highlight.highlight_all input_buffer;
		with _  -> 
		  !pop_info ();
		  !flash_info "Warning: could not revert buffer";
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
		  | 2 -> if self#save f then !flash_info "Overwritten" else
			!flash_info "Could not overwrite file"
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
		    !flash_info ~delay:1000 "Autosaved"
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
	       ("File "^f^"already exists")
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

  method show_pm_goal = 
      proof_buffer#insert 
	(Printf.sprintf "    *** Declarative Mode ***\n");
      try 
	let (hyps,metas) = get_current_pm_goal () in
	List.iter
	  (fun ((_,_,_,(s,_)) as _hyp) -> 
	     proof_buffer#insert (s^"\n"))
	  hyps;
	proof_buffer#insert 
	  (String.make 38 '_' ^ "\n");
	List.iter
	  (fun (_,_,m) -> 
	     proof_buffer#insert (m^"\n"))
	  metas;
	let my_mark = `NAME "end_of_conclusion" in
	  proof_buffer#move_mark
	    ~where:((proof_buffer#get_iter_at_mark `INSERT)) 
	    my_mark;
	  ignore (proof_view#scroll_to_mark my_mark) 
    with Not_found ->  
      match Decl_mode.get_end_command (Pfedit.get_pftreestate ()) with
	  Some endc ->
	    proof_buffer#insert 
	      ("Subproof completed, now type "^endc^".") 
	| None ->
	    proof_buffer#insert "Proof completed."

  method show_goals = 
    try
      proof_view#buffer#set_text "";
      match Decl_mode.get_current_mode () with
	  Decl_mode.Mode_none ->  proof_buffer#insert (Coq.print_no_goal ())
	| Decl_mode.Mode_tactic ->   
	    begin
	      let s = Coq.get_current_goals () in
		match s with 
		  | [] -> proof_buffer#insert (Coq.print_no_goal ())
		  | (hyps,concl)::r -> 
		      let goal_nb = List.length s in
			proof_buffer#insert 
			  (Printf.sprintf "%d subgoal%s\n" 
			     goal_nb
			     (if goal_nb<=1 then "" else "s"));
			List.iter
			  (fun ((_,_,_,(s,_)) as _hyp) -> 
			     proof_buffer#insert (s^"\n"))
			  hyps;
			proof_buffer#insert 
			  (String.make 38 '_' ^ "(1/"^
			     (string_of_int goal_nb)^
			     ")\n") ;
			let _,_,_,sconcl = concl in
			  proof_buffer#insert sconcl;
			  proof_buffer#insert "\n";
			  let my_mark = `NAME "end_of_conclusion" in
			    proof_buffer#move_mark
			      ~where:((proof_buffer#get_iter_at_mark `INSERT)) 
			      my_mark;
			    proof_buffer#insert "\n\n";
			    let i = ref 1 in
			      List.iter 
				(function (_,(_,_,_,concl)) -> 
				   incr i;
				   proof_buffer#insert 
				     (String.make 38 '_' ^"("^
					(string_of_int !i)^
					"/"^
					(string_of_int goal_nb)^
					")\n");
				   proof_buffer#insert concl;
				   proof_buffer#insert "\n\n";
				)
				r;
			      ignore (proof_view#scroll_to_mark my_mark) 
	    end
	| Decl_mode.Mode_proof -> 
	    self#show_pm_goal
    with e -> 
      prerr_endline ("Don't worry be happy despite: "^Printexc.to_string e)
	
	      
  val mutable full_goal_done = true

  method show_goals_full = 
    if not full_goal_done then
      begin
	try
	  proof_view#buffer#set_text "";
	  match Decl_mode.get_current_mode () with
	      Decl_mode.Mode_none ->  
		proof_buffer#insert (Coq.print_no_goal ())
	    | Decl_mode.Mode_tactic ->   
		begin
		  match Coq.get_current_goals () with 
		      [] -> Util.anomaly "show_goals_full"
		  | ((hyps,concl)::r) as s ->
		      let last_shown_area = 
			proof_buffer#create_tag [`BACKGROUND "light green"]
		      in
		      let goal_nb = List.length s in
			proof_buffer#insert (Printf.sprintf "%d subgoal%s\n" 
					 goal_nb
					 (if goal_nb<=1 then "" else "s"));
		  let coq_menu commands = 
		    let tag = proof_buffer#create_tag []
		    in 
		      ignore
			(tag#connect#event ~callback:
			   (fun ~origin ev it ->
			      begin match GdkEvent.get_type ev with 
				| `BUTTON_PRESS -> 
				    let ev = (GdkEvent.Button.cast ev) in
				      if (GdkEvent.Button.button ev) = 3
				      then begin 
					let loc_menu = GMenu.menu () in
					let factory = 
					  new GMenu.factory loc_menu in
					let add_coq_command (cp,ip) = 
					  ignore 
					    (factory#add_item cp 
					       ~callback:
				     (fun () -> ignore
					(self#insert_this_phrase_on_success 
					   true
					   true 
					   false 
					   ("progress "^ip^"\n") 
					   (ip^"\n"))
				     )
				  )
			      in
			      List.iter add_coq_command commands;
			      loc_menu#popup 
				~button:3
				~time:(GdkEvent.Button.time ev);
			    end
			| `MOTION_NOTIFY -> 
			    proof_buffer#remove_tag
			    ~start:proof_buffer#start_iter
			    ~stop:proof_buffer#end_iter
			    last_shown_area;
			    prerr_endline "Before find_tag_limits";
			    
			    let s,e = find_tag_limits tag 
					(new GText.iter it) 
			    in
			    prerr_endline "After find_tag_limits";
			    proof_buffer#apply_tag 
			      ~start:s 
			      ~stop:e 
			      last_shown_area;
			    
			    prerr_endline "Applied tag";
			    ()
			| _ -> ()
			end;false
		     )
		  );
		tag
	      in
	      List.iter
		(fun ((_,_,_,(s,_)) as hyp) -> 
		   let tag = coq_menu (hyp_menu hyp) in
		   proof_buffer#insert ~tags:[tag] (s^"\n"))
		hyps;
	      proof_buffer#insert 
		(String.make 38 '_' ^"(1/"^
		 (string_of_int goal_nb)^
		 ")\n") 
	      ;
	      let tag = coq_menu (concl_menu concl) in
	      let _,_,_,sconcl = concl in
	      proof_buffer#insert ~tags:[tag] sconcl;
	      proof_buffer#insert "\n";
	      let my_mark = `NAME "end_of_conclusion" in
	      proof_buffer#move_mark
		~where:((proof_buffer#get_iter_at_mark `INSERT)) my_mark;
	      proof_buffer#insert "\n\n";
	      let i = ref 1 in
	      List.iter 
		(function (_,(_,_,_,concl)) -> 
		   incr i;
		   proof_buffer#insert 
		     (String.make 38 '_' ^"("^
		      (string_of_int !i)^
		      "/"^
		      (string_of_int goal_nb)^
		      ")\n");
		   proof_buffer#insert concl;
		   proof_buffer#insert "\n\n";
		)
		r;
		ignore (proof_view#scroll_to_mark my_mark) ;
		full_goal_done <- true
		end
	    | Decl_mode.Mode_proof ->
		self#show_pm_goal
	  with e -> prerr_endline (Printexc.to_string e)
      end
      
  method send_to_coq verbosely replace phrase show_output show_error localize =
    let display_output msg =
      self#insert_message (if show_output then msg else "") in
    let display_error e =
      let (s,loc) = Coq.process_exn e in
      assert (Glib.Utf8.validate s);
      self#insert_message s;
      message_view#misc#draw None;
      if localize then 
	(match Util.option_map Util.unloc loc with 
	  | None -> ()
	  | Some (start,stop) ->
	      let convert_pos = byte_offset_to_char_offset phrase in
	      let start = convert_pos start in
	      let stop = convert_pos stop in
	      let i = self#get_start_of_input in 
	      let starti = i#forward_chars start in
	      let stopi = i#forward_chars stop in
	      input_buffer#apply_tag_by_name "error"
   		~start:starti
		~stop:stopi;
	      input_buffer#place_cursor starti) in
    try 
      full_goal_done <- false;
      prerr_endline "Send_to_coq starting now";
      Decl_mode.clear_daimon_flag ();
      if replace then begin
	let r,info = Coq.interp_and_replace ("info " ^ phrase) in
	let complete = not (Decl_mode.get_daimon_flag ()) in 
	let msg = read_stdout () in
        sync display_output msg;
	Some (complete,r)	
      end else begin
	let r = Coq.interp verbosely phrase in
	let complete = not (Decl_mode.get_daimon_flag ()) in 
	let msg = read_stdout () in
        sync display_output msg;
        Some (complete,r)
      end
    with e ->
      if show_error then sync display_error e;
      None

  method find_phrase_starting_at (start:GText.iter) = 
    prerr_endline "find_phrase_starting_at starting now";
    let trash_bytes = ref "" in
    let end_iter = start#copy in
    let lexbuf_function s count =
      let i = ref 0 in
      let n_trash = String.length !trash_bytes in
	String.blit !trash_bytes 0 s 0 n_trash;
	i := n_trash;
	try
	  while !i <= count - 1 do
	    let c = end_iter#char in
	      if c = 0 then raise (Stop !i);
	      let c' = Glib.Utf8.from_unichar c in
	      let n = String.length c' in
		if (n<=0) then exit (-2);
		if n > count - !i  then 
		  begin
		    let ri = count - !i in
		      String.blit c' 0 s !i ri;
		      trash_bytes := String.sub c' ri (n-ri);
		      i := count ;
		  end else begin
		      String.blit c' 0 s !i n;
		      i:= !i + n
		    end;
		if not end_iter#nocopy#forward_char then 
		  raise (Stop !i)
	  done;
	  count
	with Stop x ->
	  x
    in
      try
	trash_bytes := "";
	let _ = Find_phrase.get (Lexing.from_function lexbuf_function) 
	in
	  end_iter#nocopy#set_offset (start#offset + !Find_phrase.length);
	  Some (start,end_iter)
      with
	  (*
	    | Find_phrase.EOF s -> 
	  (* Phrase is at the end of the buffer*)
	    let si = start#offset in
	    let ei = si + !Find_phrase.length in
	    end_iter#nocopy#set_offset (ei - 1);
	    input_buffer#insert ~iter:end_iter "\n";
	    Some (input_buffer#get_iter (`OFFSET si),
	    input_buffer#get_iter (`OFFSET ei))
	  *)
	| _ -> None

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
		      input_buffer#move_mark `SEL_BOUND (it())#backward_char;
		      true
	    end else false
      else false

	
  method process_next_phrase verbosely display_goals do_highlight = 
    let get_next_phrase () =
      self#clear_message;
      prerr_endline "process_next_phrase starting now";
      if do_highlight then begin
	  !push_info "Coq is computing";
	  input_view#set_editable false;
	end;
      match self#find_phrase_starting_at self#get_start_of_input with 
	| None ->
	    if do_highlight then begin
		input_view#set_editable true;
		!pop_info ();
	      end;
            None
	| Some(start,stop) ->
	    prerr_endline "process_next_phrase : to_process highlight";
	    if do_highlight then begin
		input_buffer#apply_tag_by_name ~start ~stop "to_process";
		prerr_endline "process_next_phrase : to_process applied";
	      end;
	    prerr_endline "process_next_phrase : getting phrase";
            Some((start,stop),start#get_slice ~stop) in
    let remove_tag (start,stop) =
      if do_highlight then begin
	  input_buffer#remove_tag_by_name ~start ~stop "to_process" ;
	  input_view#set_editable true;
	  !pop_info ();
	end in
      let mark_processed complete (start,stop) ast =
        let b = input_buffer in
	b#move_mark ~where:stop (`NAME "start_of_input");
	b#apply_tag_by_name 
	  (if complete then "processed" else "unjustified") ~start ~stop;
	if (self#get_insert#compare) stop <= 0 then 
	  begin
	    b#place_cursor stop;
	    self#recenter_insert
	  end;
	let start_of_phrase_mark = `MARK (b#create_mark start) in
	let end_of_phrase_mark = `MARK (b#create_mark stop) in
	push_phrase 
	  start_of_phrase_mark 
	  end_of_phrase_mark ast;
	if display_goals then self#show_goals;
        remove_tag (start,stop) in
      begin
        match sync get_next_phrase () with
            None -> false
          | Some (loc,phrase) ->
            (match self#send_to_coq verbosely false phrase true true true with
	      | Some (complete,ast) -> 
		  sync (mark_processed complete) loc ast; true
	      | None -> sync remove_tag loc; false)
      end
    
  method insert_this_phrase_on_success 
    show_output show_msg localize coqphrase insertphrase = 
    let mark_processed complete ast =
      let stop = self#get_start_of_input in
      if stop#starts_line then
	input_buffer#insert ~iter:stop insertphrase
      else input_buffer#insert ~iter:stop ("\n"^insertphrase); 
      let start = self#get_start_of_input in
      input_buffer#move_mark ~where:stop (`NAME "start_of_input");
      input_buffer#apply_tag_by_name 
	(if complete then "processed" else "unjustified") ~start ~stop;
      if (self#get_insert#compare) stop <= 0 then 
	input_buffer#place_cursor stop;
      let start_of_phrase_mark = `MARK (input_buffer#create_mark start) in
      let end_of_phrase_mark = `MARK (input_buffer#create_mark stop) in
      push_phrase start_of_phrase_mark end_of_phrase_mark ast;
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
	            push_phrase start_of_phrase_mark end_of_phrase_mark ast
	          end
	      | None -> ())
	| _ -> ())
      with _ -> ()*) in
    match self#send_to_coq false false coqphrase show_output show_msg localize with
      | Some (complete,ast) -> sync (mark_processed complete) ast; true
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
	      input_buffer#apply_tag_by_name ~start ~stop "to_process";
	      input_view#set_editable false) ();
      !push_info "Coq is computing";
      let get_current () =
	if !current.stop_before then
          match self#find_phrase_starting_at self#get_start_of_input with
            | None -> self#get_start_of_input
            | Some (_, stop2) -> stop2
	else begin
            self#get_start_of_input
	  end
      in   
	(try 
	    while ((stop#compare (get_current())>=0) 
		    && (self#process_next_phrase false false false))
	    do Util.check_for_interrupt () done
	  with Sys.Break -> 
	    prerr_endline "Interrupted during process_until_iter_or_error");
	sync (fun _ ->
	  self#show_goals;
	  (* Start and stop might be invalid if an eol was added at eof *)
	  let start = input_buffer#get_iter start' in
	  let stop =  input_buffer#get_iter stop' in
	    input_buffer#remove_tag_by_name ~start ~stop "to_process" ;
	    input_view#set_editable true) ();
	!pop_info()

  method process_until_end_or_error = 
    self#process_until_iter_or_error input_buffer#end_iter

  method reset_initial =
    sync (fun _ ->
	    Stack.iter 
              (function inf -> 
		 let start = input_buffer#get_iter_at_mark inf.start in
		 let stop = input_buffer#get_iter_at_mark inf.stop in
		   input_buffer#move_mark ~where:start (`NAME "start_of_input");
		   input_buffer#remove_tag_by_name "processed" ~start ~stop;
		   input_buffer#remove_tag_by_name "unjustified" ~start ~stop;
		   input_buffer#delete_mark inf.start;
		   input_buffer#delete_mark inf.stop;
              ) 
              processed_stack;
	    Stack.clear processed_stack;
	    self#clear_message)();
    Coq.reset_initial ()


  (* backtrack Coq to the phrase preceding iterator [i] *)
  method backtrack_to_no_lock i =
    prerr_endline "Backtracking_to iter starts now.";
    (* re-synchronize Coq to the current state of the stack *)
    let rec synchro () =
      if is_empty () then
	Coq.reset_initial ()
      else begin
	  let t = pop () in
	    begin match t.reset_info with
	      | Reset (id, ({contents=true} as v)) -> v:=false; 
		  (match snd t.ast with
		     | VernacBeginSection _ | VernacDefineModule _ 
		     | VernacDeclareModule _ | VernacDeclareModuleType _
		     | VernacEndSegment _ 
		       -> reset_to_mod id
		     | _ ->  reset_to id)
	      | _ -> synchro ()
	    end;
	    interp_last t.ast;
	    repush_phrase t
	end
    in
    let add_undo t = match t with | Some n -> Some (succ n) | None -> None
    in
      (* pop Coq commands until we reach iterator [i] *)
    let  rec pop_commands done_smthg undos =
      if is_empty () then 
	done_smthg, undos
      else
	let t = top () in 
	  if i#compare (input_buffer#get_iter_at_mark t.stop) < 0 then begin
	      ignore (pop ());
	      let undos = if is_tactic (snd t.ast) then add_undo undos else None in
		pop_commands true undos
	    end else
	    done_smthg, undos
    in
    let done_smthg, undos = pop_commands false (Some 0) in
      prerr_endline "Popped commands";
      if done_smthg then
	begin 
	  try 
	    (match undos with 
	       | None -> synchro () 
	       | Some n -> try Pfedit.undo n with _ -> synchro ());
            sync (fun _ ->
		    let start =
		      if is_empty () then input_buffer#start_iter 
		      else input_buffer#get_iter_at_mark (top ()).stop in
		      prerr_endline "Removing (long) processed tag...";
		      input_buffer#remove_tag_by_name 
			~start 
			~stop:self#get_start_of_input
			"processed";
		      input_buffer#remove_tag_by_name 
			~start 
			~stop:self#get_start_of_input
			"unjustified";
		      prerr_endline "Moving (long) start_of_input...";
		      input_buffer#move_mark ~where:start (`NAME "start_of_input");
		      self#show_goals;
		      clear_stdout ();
		      self#clear_message)
              ();
	  with _ -> 
	    !push_info "WARNING: undo failed badly -> Coq might be in an inconsistent state.
Please restart and report NOW.";
      end
    else prerr_endline "backtrack_to : discarded (...)"
      
  method backtrack_to i = 
    if Mutex.try_lock coq_may_stop then 
      (!push_info "Undoing...";self#backtrack_to_no_lock i ; Mutex.unlock coq_may_stop;
       !pop_info ())
    else prerr_endline "backtrack_to : discarded (lock is busy)"

  method go_to_insert =
    let point = self#get_insert in
      if point#compare self#get_start_of_input>=0
      then self#process_until_iter_or_error point
      else self#backtrack_to point

  method undo_last_step =
    if Mutex.try_lock coq_may_stop then  
      (!push_info "Undoing last step...";
       (try
	    let last_command = top () in
	    let start = input_buffer#get_iter_at_mark last_command.start in
	    let update_input () =
	      prerr_endline "Removing processed tag...";
	      input_buffer#remove_tag_by_name 
		~start
		~stop:(input_buffer#get_iter_at_mark last_command.stop) 
		"processed";
	      input_buffer#remove_tag_by_name 
	        ~start
	        ~stop:(input_buffer#get_iter_at_mark last_command.stop) 
	      "unjustified";
	      prerr_endline "Moving start_of_input";
	      input_buffer#move_mark
		~where:start
		(`NAME "start_of_input");
	      input_buffer#place_cursor start;
	      self#recenter_insert;
	      self#show_goals;
	      self#clear_message
	    in
	      begin match last_command with 
		| {ast=_, (VernacSolve _ | VernacTime (VernacSolve _))} -> 
		    begin 
		      try Pfedit.undo 1; ignore (pop ()); sync update_input () 
		      with _ -> self#backtrack_to_no_lock start
		    end
		| {ast=_,t;reset_info=Reset (id, {contents=true})} ->
		    ignore (pop ());
		    (match t with 
		       | VernacBeginSection _ | VernacDefineModule _ 
		       | VernacDeclareModule _ | VernacDeclareModuleType _
		       | VernacEndSegment _
			 -> reset_to_mod id
		       | _ ->  reset_to id);
		    sync update_input ()
		| { ast = _, ( VernacStartTheoremProof _ 
		    | VernacGoal _
		    | VernacDeclareTacticDefinition _
		    | VernacDefinition (_,_,ProveBody _,_));
		    reset_info=Reset(id,{contents=false})} ->
		    ignore (pop ());
		    (try 
			 Pfedit.delete_current_proof () 
		     with e ->
		       begin 
			 prerr_endline "WARNING : found a closed environment";
			 raise e
		       end);
		    sync update_input ()
		| { ast = (_, a) } when is_state_preserving a ->
		    ignore (pop ());
		    sync update_input ()
		| _ -> 
		    self#backtrack_to_no_lock start
	      end;
	with
	  | Size 0 -> (* !flash_info "Nothing to Undo"*)()
       );
       !pop_info ();
       Mutex.unlock coq_may_stop)
    else prerr_endline "undo_last_step discarded"

      
  method blaster () = 
    
    ignore (Thread.create 
	      (fun () ->  
		 prerr_endline "Blaster called";
		 let c = Blaster_window.present_blaster_window () in
		   if Mutex.try_lock c#lock then begin
		       c#clear ();
                      Decl_mode.check_not_proof_mode "No blaster in Proof mode";
		       let current_gls = try get_current_goals () with _ -> [] in
			 
		       let set_goal i (s,t) = 
			 let gnb = string_of_int i in
			 let s = gnb ^":"^s in
			 let t' = gnb ^": progress "^t in
			 let t'' = gnb ^": "^t in
			   c#set
			     ("Goal "^gnb)
			     s 
			     (fun () -> try_interptac t')
			     (sync(fun () -> self#insert_command t'' t''))
		       in
		       let set_current_goal (s,t) = 
			 c#set
			   "Goal 1"
			   s 
			   (fun () -> try_interptac ("progress "^t))
			   (sync(fun () -> self#insert_command t t))
		       in
			 begin match current_gls with 
			   | [] -> ()
			   | (hyp_l,current_gl)::r ->
			       List.iter set_current_goal (concl_menu current_gl);
			       List.iter 
				 (fun hyp -> 
				    List.iter set_current_goal (hyp_menu hyp))
				 hyp_l;
			       let i = ref 2 in
				 List.iter 
				   (fun (hyp_l,gl) -> 
				      List.iter (set_goal !i) (concl_menu gl);
				      incr i)
				   r
			 end;
			 let _ =  c#blaster () in
			   Mutex.unlock c#lock
		     end else prerr_endline "Blaster discarded")
	      ())
      
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

  method deactivate () = 
    is_active <- false;
    (match act_id with None -> () 
       | Some id ->
	   reset_initial ();
	   input_view#misc#disconnect id;
	   prerr_endline "DISCONNECTED old active : ";
	   print_id id;
    );
    deact_id <- Some 
      (input_view#event#connect#key_press self#disconnected_keypress_handler);
    prerr_endline "CONNECTED  inactive : ";
    print_id (out_some deact_id)

  method activate () =
    is_active <- true;
    (match deact_id with None -> () 
       | Some id -> input_view#misc#disconnect id;
	   prerr_endline "DISCONNECTED old inactive : ";
	   print_id id
    );
    act_id <- Some 
      (input_view#event#connect#key_press self#active_keypress_handler);
    prerr_endline "CONNECTED active : ";
    print_id (out_some act_id);
    match 
      (out_some ((Vector.get input_views index).analyzed_view)) #filename 
    with
      | None -> ()
      | Some f -> let dir = Filename.dirname f in
		    if not (is_in_loadpath dir) then
		      begin
			ignore (Coq.interp false
				  (Printf.sprintf "Add LoadPath \"%s\". "  dir))
		      end
			
  method electric_handler = 
    input_buffer#connect#insert_text ~callback:
      (fun it x -> 
	 begin try
	     if last_index then begin
		 last_array.(0)<-x;
		 if (last_array.(1) ^ last_array.(0) = ".\n") then raise Found
	       end else begin
		   last_array.(1)<-x;
		   if (last_array.(0) ^ last_array.(1) = ".\n") then raise Found
		 end
	   with Found -> 
	     begin
	       ignore (self#process_next_phrase false true true)
	     end;
	 end;
	 last_index <- not last_index;)

  method private electric_paren tag =
    let oparen_code = Glib.Utf8.to_unichar "("  (ref 0) in
    let cparen_code = Glib.Utf8.to_unichar ")"  (ref 0) in
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
			     (prerr_endline "insert_text: Placing cursor";input_buffer#place_cursor it)));
    ignore (input_buffer#connect#after#apply_tag
	      ~callback:(fun tag ~start ~stop ->
			   if (start#compare self#get_start_of_input)>=0
			   then 
			     begin
			       input_buffer#remove_tag_by_name 
				 ~start
				 ~stop
				 "processed";
			       input_buffer#remove_tag_by_name 
				 ~start
				 ~stop
				 "unjustified"
			     end
			)
	   );
    ignore (input_buffer#connect#after#insert_text
	      ~callback:(fun it s ->
			   if auto_complete_on && 
			     String.length s = 1 && s <> " " && s <> "\n" 
			   then 
			     let v = out_some (get_current_view ()).analyzed_view 
			     in 
			     let has_completed = 
			       v#complete_at_offset 
				 ((v#view#buffer#get_iter `SEL_BOUND)#offset)
			     in
			       if has_completed then 
				 input_buffer#move_mark `SEL_BOUND (input_buffer#get_iter `SEL_BOUND)#forward_char;
			       
			       
			)
	   );
    ignore (input_buffer#connect#modified_changed
	      ~callback:
	      (fun () ->
		 if input_buffer#modified then 
		   set_tab_image index 
		     ~icon:(match (out_some (current_all.analyzed_view))#filename with 
			      | None -> `SAVE_AS
			      | Some _ -> `SAVE
			   )
		 else set_tab_image index ~icon:`YES;
	      ));
    ignore (input_buffer#connect#changed
	      ~callback:(fun () -> 
			   last_modification_time <- Unix.time ();
			   let r = input_view#visible_rect in
			   let stop = 
			     input_view#get_iter_at_location 
			       ~x:(Gdk.Rectangle.x r + Gdk.Rectangle.width r)
			       ~y:(Gdk.Rectangle.y r + Gdk.Rectangle.height r)
			   in
			     input_buffer#remove_tag_by_name 
			       ~start:self#get_start_of_input
			       ~stop
			       "error";
			     Highlight.highlight_around_current_line
			       input_buffer 
			)
	   );
    ignore (input_buffer#add_selection_clipboard (cb()));
    let paren_highlight_tag = input_buffer#create_tag ~name:"paren" [`BACKGROUND "purple"]  in
      self#electric_paren paren_highlight_tag;
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
				     paren_highlight_tag;
			       | Some s -> 
				   prerr_endline (s^" moved")
			       | None -> () )
	     );
      ignore (input_buffer#connect#insert_text
		(fun it s -> 
		   prerr_endline "Should recenter ?";
		   if String.contains s '\n' then begin
		       prerr_endline "Should recenter : yes";
		       self#recenter_insert
		     end))
end

let create_input_tab filename =
  let b = GText.buffer () in 
  let _ = GMisc.label () in 
  let v_box = GPack.hbox ~homogeneous:false () in
  let _ = GMisc.image ~packing:v_box#pack () in
  let _ = GMisc.label ~text:filename ~packing:v_box#pack () in
  let fr1 = GBin.frame ~shadow_type:`ETCHED_OUT
    ~packing:((notebook ())#append_page
		~tab_label:v_box#coerce) () 
  in 
  let sw1 = GBin.scrolled_window
    ~vpolicy:`AUTOMATIC 
    ~hpolicy:`AUTOMATIC
    ~packing:fr1#add () 
  in
  let tv1 = Undo.undoable_view ~buffer:b ~packing:(sw1#add) () in
    prerr_endline ("Language: "^ b#start_iter#language);
    tv1#misc#set_name "ScriptWindow";
    let _ = tv1#set_editable true in
    let _ = tv1#set_wrap_mode `NONE in
      b#place_cursor ~where:(b#start_iter);
      ignore (tv1#event#connect#button_press ~callback:
		(fun ev -> GdkEvent.Button.button ev = 3));
      (*  ignore (tv1#event#connect#button_press ~callback:
	  (fun ev -> 
	  if (GdkEvent.Button.button ev=2) then
	  (try 
	  prerr_endline "Paste invoked";
	  GtkSignal.emit_unit 
	  (get_current_view()).view#as_view 
	  GtkText.View.Signals.paste_clipboard;
	  true
	  with _ -> false)
	  else false
	  ));*)
      tv1#misc#grab_focus ();
      ignore (tv1#buffer#create_mark 
		~name:"start_of_input" 
		tv1#buffer#start_iter);
      ignore (tv1#buffer#create_tag 
		~name:"kwd" 
		[`FOREGROUND "blue"]);
      ignore (tv1#buffer#create_tag 
		~name:"decl" 
		[`FOREGROUND "orange red"]);
      ignore (tv1#buffer#create_tag 
		~name:"comment" 
		[`FOREGROUND "brown"]);
      ignore (tv1#buffer#create_tag 
		~name:"reserved" 
		[`FOREGROUND "dark red"]);
      ignore (tv1#buffer#create_tag 
		~name:"error" 
		[`UNDERLINE `DOUBLE ; `FOREGROUND "red"]);
      ignore (tv1#buffer#create_tag 
		~name:"to_process" 
		[`BACKGROUND "light blue" ;`EDITABLE false]);
      ignore (tv1#buffer#create_tag 
		~name:"processed" 
		[`BACKGROUND "light green" ;`EDITABLE false]);
      ignore (tv1#buffer#create_tag (* Proof mode *)
	        ~name:"unjustified" 
               [`UNDERLINE `SINGLE ; `FOREGROUND "red";
	         `BACKGROUND "gold" ;`EDITABLE false]);
      ignore (tv1#buffer#create_tag 
		~name:"found" 
		[`BACKGROUND "blue"; `FOREGROUND "white"]);
      tv1


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

let main files = 
  (* Statup preferences *)
  load_pref ();

  (* Main window *)
  let w = GWindow.window 
    ~wm_class:"CoqIde" ~wm_name:"CoqIde"
    ~allow_grow:true ~allow_shrink:true 
    ~width:!current.window_width ~height:!current.window_height 
    ~title:"CoqIde" ()
  in
    (try
	 let icon_image = lib_ide_file "coq.ico" in
	 let icon = GdkPixbuf.from_file icon_image in
	   w#set_icon (Some icon)
     with _ -> ());

    let vbox = GPack.vbox ~homogeneous:false ~packing:w#add () in


    (* Menu bar *)
    let menubar = GMenu.menu_bar ~packing:vbox#pack () in

    (* Toolbar *)
    let toolbar = GButton.toolbar 
      ~orientation:`HORIZONTAL 
      ~style:`ICONS
      ~tooltips:true 
      ~packing:(* handle#add *)
      (vbox#pack ~expand:false ~fill:false)
      ()
    in
      show_toolbar := 
	(fun b -> if b then toolbar#misc#show () else toolbar#misc#hide ());

      let factory = new GMenu.factory ~accel_path:"<CoqIde MenuBar>/" menubar in
      let accel_group = factory#accel_group in

      (* File Menu *)
      let file_menu = factory#add_submenu "_File" in

      let file_factory = new GMenu.factory ~accel_path:"<CoqIde MenuBar>/File/" file_menu ~accel_group in

      (* File/Load Menu *)
      let load f =
	let f = absolute_filename f in		
	  try
	    prerr_endline "Loading file starts";
	    Vector.find_or_fail 
	      (function 
		 | {analyzed_view=Some av} -> 
		     (match av#filename with 
			| None -> false 
			| Some fn -> same_file f fn)
		 | _ -> false) 
	      !input_views;
	    prerr_endline "Loading: must open";
	    let b = Buffer.create 1024 in
	      prerr_endline "Loading: get raw content";
	      with_file f ~f:(input_channel b);
	      prerr_endline "Loading: convert content";
	      let s = do_convert (Buffer.contents b) in
		prerr_endline "Loading: create view";
		let view = create_input_tab (Glib.Convert.filename_to_utf8 
					       (Filename.basename f)) 
		in
		  prerr_endline "Loading: change font";
		  view#misc#modify_font !current.text_font;
		  prerr_endline "Loading: adding view";
		  let index = add_input_view {view = view;
					      analyzed_view = None;
					     }
		  in
		  let av = (new analyzed_view index) in 
		    prerr_endline "Loading: register view";
		    (get_input_view index).analyzed_view <- Some av;
		    prerr_endline "Loading: set filename";
		    av#set_filename (Some f);
		    prerr_endline "Loading: stats";
		    av#update_stats;
		    let input_buffer = view#buffer in
		      prerr_endline "Loading: fill buffer";
		      input_buffer#set_text s;
		      input_buffer#place_cursor input_buffer#start_iter;
		      prerr_endline ("Loading: switch to view "^ string_of_int index);
		      set_current_view index;
		      set_tab_image index ~icon:`YES;
		      prerr_endline "Loading: highlight";
		      Highlight.highlight_all input_buffer;
		      input_buffer#set_modified false;
		      prerr_endline "Loading: clear undo";
		      av#view#clear_undo;
		      prerr_endline "Loading: success"
	  with       
	    | Vector.Found i -> set_current_view i
	    | e -> !flash_info ("Load failed: "^(Printexc.to_string e))
      in
      let load_m = file_factory#add_item "_Open/Create" 
	~key:GdkKeysyms._O in
      let load_f () = 	  
	match select_file ~title:"Load file" () with 
	  | None -> ()
	  | Some f -> load f
      in
	ignore (load_m#connect#activate (load_f));

	(* File/Save Menu *)
	let save_m = file_factory#add_item "_Save" 
	  ~key:GdkKeysyms._S in

	  
	let save_f () = 
	  let current = get_current_view () in
	    try
	      (match (out_some current.analyzed_view)#filename with 
		 | None ->
		     begin match GToolbox.select_file ~title:"Save file" ()
		       with
			 | None -> ()
			 | Some f -> 
			     if (out_some current.analyzed_view)#save_as f then begin
				 set_current_tab_label (Filename.basename f);
				 !flash_info ("File " ^ f ^ " saved")
			       end
			     else warning ("Save Failed (check if " ^ f ^ " is writable)")
		     end
		 | Some f -> 
		     if (out_some current.analyzed_view)#save f then 
		       !flash_info ("File " ^ f ^ " saved")
		     else warning  ("Save Failed (check if " ^ f ^ " is writable)")
		       
	      )
	    with 
	      | e -> warning "Save: unexpected error"
	in   
	  ignore (save_m#connect#activate save_f);

	  (* File/Save As Menu *)
	  let saveas_m = file_factory#add_item "S_ave as" 
	  in
	  let saveas_f () = 
	    let current = get_current_view () in
	      try (match (out_some current.analyzed_view)#filename with 
		     | None -> 
			 begin match GToolbox.select_file ~title:"Save file as" ()
			   with
			     | None -> ()
			     | Some f -> 
				 if (out_some current.analyzed_view)#save_as f then begin
				     set_current_tab_label (Filename.basename f);
				     !flash_info "Saved"
				   end
				 else !flash_info "Save Failed"
			 end
		     | Some f -> 
			 begin match GToolbox.select_file 
			     ~dir:(ref (Filename.dirname f)) 
			     ~filename:(Filename.basename f)
			     ~title:"Save file as" ()
			   with
			     | None -> ()
			     | Some f -> 
				 if (out_some current.analyzed_view)#save_as f then begin
				     set_current_tab_label (Filename.basename f);
				     !flash_info "Saved"
				   end else !flash_info "Save Failed"
			 end);
	      with e -> !flash_info "Save Failed"
	  in   
	    ignore (saveas_m#connect#activate saveas_f);
	    
	    (* File/Save All Menu *)
	    let saveall_m = file_factory#add_item "Sa_ve All" in
	    let saveall_f () = 
	      Vector.iter
		(function 
		   | {view = view ; analyzed_view = Some av} -> 
		       begin match av#filename with 
			 | None -> ()
			 | Some f ->
			     ignore (av#save f)
		       end
		   | _ -> ()
		)  input_views
	    in
	    let has_something_to_save () = 
	      Vector.exists
		(function 
		   | {view=view} -> view#buffer#modified        
		)
		input_views
	    in
	      ignore (saveall_m#connect#activate saveall_f);
	      
	      (* File/Revert Menu *)
	      let revert_m = file_factory#add_item "_Revert All Buffers" in
	      let revert_f () = 
		Vector.iter 
		  (function 
		       {view = view ; analyzed_view = Some av} -> 
			 (try 
			      match av#filename,av#stats with 
				| Some f,Some stats -> 
				    let new_stats = Unix.stat f in
				      if new_stats.Unix.st_mtime > stats.Unix.st_mtime 
				      then av#revert
				| Some _, None -> av#revert
				| _ -> ()
			  with _ -> av#revert)
		     | _ -> ()
		  )  input_views
	      in
		ignore (revert_m#connect#activate revert_f);
		
		(* File/Close Menu *)
		let close_m =
                  file_factory#add_item "_Close Buffer" ~key:GdkKeysyms._W in
		let close_f () = 
		  let v = out_some !active_view in
		  let act = get_current_view_page () in
		    if v = act then !flash_info "Cannot close an active view"
		    else remove_current_view_page ()
		in
		  ignore (close_m#connect#activate close_f);
		  
		  (* File/Print Menu *)
		  let print_f () =
		    let v = get_current_view () in
		    let av = out_some v.analyzed_view in
		      match av#filename with
			| None -> 
			    !flash_info "Cannot print: this buffer has no name"
			| Some f ->
			    let cmd = 
			      "cd " ^ Filename.dirname f ^ "; " ^
				!current.cmd_coqdoc ^ " -ps " ^ Filename.basename f ^ 
				" | " ^ !current.cmd_print
			    in
			    let s,_ = run_command av#insert_message cmd in
			      !flash_info (cmd ^ if s = Unix.WEXITED 0 then " succeeded" else " failed")
		  in
		  let _ = file_factory#add_item "_Print"
	            ~key:GdkKeysyms._P
                    ~callback:print_f in

		  (* File/Export to Menu *)
		  let export_f kind () =
		    let v = get_current_view () in
		    let av = out_some v.analyzed_view in
		      match av#filename with
			| None -> 
			    !flash_info "Cannot print: this buffer has no name"
			| Some f ->
			    let basef = Filename.basename f in
			    let output = 
			      let basef_we = try Filename.chop_extension basef with _ -> basef in
				match kind with
				  | "latex" -> basef_we ^ ".tex"
				  | "dvi" | "ps" | "html" -> basef_we ^ "." ^ kind
				  | _ -> assert false
			    in
			    let cmd = 
			      "cd " ^ Filename.dirname f ^ "; " ^
				!current.cmd_coqdoc ^ " --" ^ kind ^ " -o " ^ output ^ " " ^ basef
			    in
			    let s,_ = run_command av#insert_message cmd in
			      !flash_info (cmd ^ 
					     if s = Unix.WEXITED 0 
					     then " succeeded" 
					     else " failed")
		  in
		  let file_export_m =  file_factory#add_submenu "E_xport to" in

		  let file_export_factory = new GMenu.factory ~accel_path:"<CoqIde MenuBar>/Export/" file_export_m ~accel_group in
		  let _ = 
		    file_export_factory#add_item "_Html" ~callback:(export_f "html") 
		  in
		  let _ = 
		    file_export_factory#add_item "_LaTeX" ~callback:(export_f "latex")
		  in
		  let _ = 
		    file_export_factory#add_item "_Dvi" ~callback:(export_f "dvi") 
		  in
		  let _ = 
		    file_export_factory#add_item "_Ps" ~callback:(export_f "ps") 
		  in

		  (* File/Rehighlight Menu *)
		  let rehighlight_m = file_factory#add_item "Reh_ighlight" ~key:GdkKeysyms._L in
		    ignore (rehighlight_m#connect#activate 
			      (fun () -> 
				 Highlight.highlight_all 
				   (get_current_view()).view#buffer;
				 (out_some (get_current_view()).analyzed_view)#recenter_insert));

		    (* File/Quit Menu *)
		    let quit_f () =
		      save_pref();
		      if has_something_to_save () then 
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
			with 1 -> saveall_f () ; exit 0
			  | 2 -> exit 0
			  | _ -> ()
		      else exit 0
		    in
		    let _ = file_factory#add_item "_Quit" ~key:GdkKeysyms._Q 
		      ~callback:quit_f
		    in
		      ignore (w#event#connect#delete (fun _ -> quit_f (); true));

		      (* Edit Menu *)
		      let edit_menu = factory#add_submenu "_Edit" in
		      let edit_f = new GMenu.factory ~accel_path:"<CoqIde MenuBar>/Edit/" edit_menu ~accel_group in
			ignore(edit_f#add_item "_Undo" ~key:GdkKeysyms._u ~callback:
				 (do_if_not_computing "undo"
				    (fun () -> 
				       ignore ((out_some ((get_current_view()).analyzed_view))#
						 without_auto_complete 
						 (fun () -> (get_current_view()).view#undo) ()))));
			ignore(edit_f#add_item "_Clear Undo Stack" 
				 (* ~key:GdkKeysyms._exclam *)
				 ~callback:
				 (fun () -> 
				    ignore (get_current_view()).view#clear_undo));
			ignore(edit_f#add_separator ());
			ignore(edit_f#add_item "Cut" ~key:GdkKeysyms._X ~callback:
				 (fun () -> GtkSignal.emit_unit
				    (get_current_view()).view#as_view 
				    GtkText.View.S.cut_clipboard));
			ignore(edit_f#add_item "Copy" ~key:GdkKeysyms._C ~callback:
				 (fun () -> GtkSignal.emit_unit
				    (get_current_view()).view#as_view 
				    GtkText.View.S.copy_clipboard));
			ignore(edit_f#add_item "Paste" ~key:GdkKeysyms._V ~callback:
				 (fun () -> 
				    try GtkSignal.emit_unit
				      (get_current_view()).view#as_view 
				      GtkText.View.S.paste_clipboard
				    with _ -> prerr_endline "EMIT PASTE FAILED"));
			ignore (edit_f#add_separator ());


			(*
			  let toggle_auto_complete_i = 
			  edit_f#add_check_item "_Auto Completion" 
			  ~active:!current.auto_complete
			  ~callback:
			  in
			*)
			(*
			  auto_complete := 
			  (fun b -> match (get_current_view()).analyzed_view with
			  | Some av -> av#set_auto_complete b
			  | None -> ());
			*)

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
			let _ = 
			  GButton.check_button
			    ~label:"case sensitive"
			    ~active:true
			    ~packing: (find_box#attach ~left:1 ~top:2)
			    ()
			in
			  (*
			    let find_backwards_check = 
			    GButton.check_button
			    ~label:"search backwards"
			    ~active:false
			    ~packing: (find_box#attach ~left:1 ~top:3)
			    ()
			    in
			  *)
			let close_find_button =
			  GButton.button
			    ~label:"Close"
			    ~packing: (find_box#attach ~left:2 ~top:0)
			    ()
			in
			let replace_button =
			  GButton.button
			    ~label:"Replace"
			    ~packing: (find_box#attach ~left:2 ~top:1)
			    ()
			in
			let replace_find_button =
			  GButton.button
			    ~label:"Replace and find"
			    ~packing: (find_box#attach ~left:2 ~top:2)
			    ()
			in
			let find_again_button =
			  GButton.button
			    ~label:"_Find again"
			    ~packing: (find_box#attach ~left:2 ~top:3)
			    ()
			in
			let find_again_backward_button =
			  GButton.button
			    ~label:"Find _backward"
			    ~packing: (find_box#attach ~left:2 ~top:4)
			    ()
			in
			let last_find () =
			  let v = (get_current_view()).view in
			  let b = v#buffer in
			  let start,stop =
			    match !last_found with 
			      | None -> let i = b#get_iter_at_mark `INSERT in (i,i)
			      | Some(start,stop) ->
				  let start = b#get_iter_at_mark start
				  and stop = b#get_iter_at_mark stop
				  in
				    b#remove_tag_by_name ~start ~stop "found";
				    last_found:=None;
				    start,stop
			  in
			    (v,b,start,stop)
			in
			let do_replace () =
			  let v = (get_current_view()).view in
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
				b#apply_tag_by_name "found" ~start ~stop;
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
			    b#place_cursor stop;
			    find_w#misc#hide();
			    v#coerce#misc#grab_focus()
			in
			  to_do_on_page_switch := 
			    (fun i -> if find_w#misc#visible then close_find()):: 
			      !to_do_on_page_switch;
			  let find_again_forward () =
			    search_backward := false;
			    let (v,b,start,_) = last_find () in
			    let start = start#forward_chars 1 in
			      find_from v b start find_entry#text
			  in
			  let find_again_backward () =
			    search_backward := true;
			    let (v,b,start,_) = last_find () in
			    let start = start#backward_chars 1 in
			      find_from v b start find_entry#text
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
			      else if k = GdkKeysyms._Return then
				begin
				  close_find();
				  true
				end 
			      else if List.mem `CONTROL s && k = GdkKeysyms._f then
				begin
				  find_again_forward ();
				  true
				end
			      else if List.mem `CONTROL s && k = GdkKeysyms._b then
				begin
				  find_again_backward ();
				  true
				end
			      else false (* to let default callback execute *)
			  in
			  let find_f ~backward () = 
			    search_backward := backward;
			    find_w#show ();
			    find_w#present ();
			    find_entry#misc#grab_focus ()
			  in
			  let _ = edit_f#add_item "_Find in buffer"
			    ~key:GdkKeysyms._F
			    ~callback:(find_f ~backward:false)
			  in
			  let _ = edit_f#add_item "Find _backwards"
			    ~key:GdkKeysyms._B
			    ~callback:(find_f ~backward:true)
			  in
			  let _ = close_find_button#connect#clicked close_find in
			  let _ = replace_button#connect#clicked do_replace in
			  let _ = replace_find_button#connect#clicked do_replace_find in
			  let _ = find_again_button#connect#clicked find_again_forward in
			  let _ = find_again_backward_button#connect#clicked find_again_backward in
			  let _ = find_entry#connect#changed do_find in
			  let _ = find_entry#event#connect#key_press ~callback:key_find in
			  let _ = find_w#event#connect#delete (fun _ -> find_w#misc#hide(); true) in
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
			      let v = out_some (get_current_view ()).analyzed_view 
			      
			      in v#complete_at_offset 
			      ((v#view#buffer#get_iter `SEL_BOUND)#offset)
			      ))
			      in
			      complete_i#misc#set_state `INSENSITIVE;
			    *)
			    
			    ignore(edit_f#add_item "Complete Word" ~key:GdkKeysyms._slash ~callback:
				     (fun () -> 
					ignore (
						 let av = out_some ((get_current_view()).analyzed_view) in 
						   av#complete_at_offset (av#get_insert)#offset
					       )));

			    ignore(edit_f#add_separator ());
			    (* external editor *)
			    let _ = 
			      edit_f#add_item "External editor" ~callback:
				(fun () -> 	 
				   let av = out_some ((get_current_view()).analyzed_view) in 
				     match av#filename with
				       | None -> ()
				       | Some f ->
					   save_f ();
					   let l,r = !current.cmd_editor in
					   let _ = run_command av#insert_message (l ^ f ^ r) in
					     av#revert)
			    in
			    let _ = edit_f#add_separator () in
			      (* Preferences *)
			    let reset_revert_timer () =
			      disconnect_revert_timer ();
			      if !current.global_auto_revert then 
				revert_timer := Some
				  (GMain.Timeout.add ~ms:!current.global_auto_revert_delay 
				     ~callback:
				     (fun () -> 
					do_if_not_computing "revert" (sync revert_f) ();
					true))
			    in reset_revert_timer (); (* to enable statup preferences timer *)

			      let auto_save_f () = 
				Vector.iter 
				  (function 
				       {view = view ; analyzed_view = Some av} -> 
					 (try 
					      av#auto_save
					  with _ -> ())
				     | _ -> ()
				  )  
				  input_views
			      in

			      let reset_auto_save_timer () =
				disconnect_auto_save_timer ();
				if !current.auto_save then 
				  auto_save_timer := Some
				    (GMain.Timeout.add ~ms:!current.auto_save_delay 
				       ~callback:
				       (fun () -> 
					  do_if_not_computing "autosave" (sync auto_save_f) ();
					  true))
			      in reset_auto_save_timer (); (* to enable statup preferences timer *)


				let _ =
				  edit_f#add_item "_Preferences"
				    ~callback:(fun () -> configure ();reset_revert_timer ())
				in
				  (*
				    let save_prefs_m =
				    configuration_factory#add_item "_Save preferences"
				    ~callback:(fun () -> save_pref ())
				    in
				  *)
				  (* Navigation Menu *)
				let navigation_menu =  factory#add_submenu "_Navigation" in
				let navigation_factory = 
				  new GMenu.factory navigation_menu 
				    ~accel_path:"<CoqIde MenuBar>/Navigation/"
				    ~accel_group 
				    ~accel_modi:!current.modifier_for_navigation 
				in
				let do_or_activate f () = 
				  let current = get_current_view () in
				  let analyzed_view = out_some current.analyzed_view in
				    if analyzed_view#is_active then 
				      ignore (f analyzed_view)
				    else
				      begin
					!flash_info "New proof started";
					activate_input (notebook ())#current_page;
					ignore (f analyzed_view)
				      end
				in

				let do_or_activate f = 
				  do_if_not_computing "do_or_activate"
				    (do_or_activate
				       (fun av -> f av ; !pop_info();!push_info (Coq.current_status())))
				in

				let add_to_menu_toolbar text ~tooltip ?key ~callback icon = 
				  begin
				    match key with None -> () 
				      | Some key -> ignore (navigation_factory#add_item text ~key ~callback)
				  end;
				  ignore (toolbar#insert_button
					    ~tooltip
					    ~text:tooltip
					    ~icon:(stock_to_widget ~size:`LARGE_TOOLBAR icon)
					    ~callback
					    ())
				in
				  add_to_menu_toolbar 
				    "_Save" 
				    ~tooltip:"Save current buffer" 
				    ~callback:save_f
				    `SAVE;
				  add_to_menu_toolbar 
				    "_Close" 
				    ~tooltip:"Close current buffer" 
				    ~callback:close_f
				    `CLOSE;
				  add_to_menu_toolbar 
				    "_Forward" 
				    ~tooltip:"Forward one command" 
				    ~key:GdkKeysyms._Down 
				    ~callback:(do_or_activate (fun a -> a#process_next_phrase true true true))
				    `GO_DOWN;
				  add_to_menu_toolbar "_Backward"
				    ~tooltip:"Backward one command" 
				    ~key:GdkKeysyms._Up
				    ~callback:(do_or_activate (fun a -> a#undo_last_step))
				    `GO_UP;
				  add_to_menu_toolbar 
				    "_Go to" 
				    ~tooltip:"Go to cursor" 
				    ~key:GdkKeysyms._Right
				    ~callback:(do_or_activate (fun a-> a#go_to_insert))
				    `JUMP_TO;
				  add_to_menu_toolbar 
				    "_Start" 
				    ~tooltip:"Go to start" 
				    ~key:GdkKeysyms._Home
				    ~callback:(do_or_activate (fun a -> a#reset_initial))
				    `GOTO_TOP;
				  add_to_menu_toolbar 
				    "_End" 
				    ~tooltip:"Go to end" 
				    ~key:GdkKeysyms._End
				    ~callback:(do_or_activate (fun a -> a#process_until_end_or_error))
				    `GOTO_BOTTOM;
				  add_to_menu_toolbar "_Interrupt"
				    ~tooltip:"Interrupt computations"    
				    ~key:GdkKeysyms._Break 
				    ~callback:break
				    `STOP
				  ;

				  (* Tactics Menu *)
				  let tactics_menu =  factory#add_submenu "_Try Tactics" in
				  let tactics_factory = 
				    new GMenu.factory tactics_menu 
				      ~accel_path:"<CoqIde MenuBar>/Tactics/"
				      ~accel_group 
				      ~accel_modi:!current.modifier_for_tactics
				  in
				  let do_if_active_raw f () = 
				    let current = get_current_view () in
				    let analyzed_view = out_some current.analyzed_view in
				      if analyzed_view#is_active then ignore (f analyzed_view)
				  in
				  let do_if_active f =
				    do_if_not_computing "do_if_active" (do_if_active_raw f) in

				    (*
				      let blaster_i = 
				      tactics_factory#add_item "_Blaster"
				      ~key:GdkKeysyms._b
				      ~callback: (do_if_active_raw (fun a -> a#blaster ()))
				    (* Custom locking mechanism! *)
				      in
				      blaster_i#misc#set_state `INSENSITIVE;
				    *)
				    
				    ignore (tactics_factory#add_item "_auto" 
					      ~key:GdkKeysyms._a
					      ~callback:(do_if_active (fun a -> a#insert_command "progress auto.\n" "auto.\n"))
					   );
				    ignore (tactics_factory#add_item "_auto with *"
					      ~key:GdkKeysyms._asterisk
					      ~callback:(do_if_active (fun a -> a#insert_command 
									 "progress auto with *.\n"
									 "auto with *.\n")));
				    ignore (tactics_factory#add_item "_eauto"
					      ~key:GdkKeysyms._e
					      ~callback:(do_if_active (fun a -> a#insert_command 
									 "progress eauto.\n"
									 "eauto.\n"))
					   );
				    ignore (tactics_factory#add_item "_eauto with *"
					      ~key:GdkKeysyms._ampersand
					      ~callback:(do_if_active (fun a -> a#insert_command 
									 "progress eauto with *.\n" 
									 "eauto with *.\n"))
					   );
				    ignore (tactics_factory#add_item "_intuition"
					      ~key:GdkKeysyms._i
					      ~callback:(do_if_active (fun a -> a#insert_command 
									 "progress intuition.\n" 
									 "intuition.\n"))
					   );
				    ignore (tactics_factory#add_item "_omega"
					      ~key:GdkKeysyms._o
					      ~callback:(do_if_active (fun a -> a#insert_command 
									 "omega.\n" "omega.\n"))
					   );
				    ignore (tactics_factory#add_item "_simpl"
					      ~key:GdkKeysyms._s
					      ~callback:(do_if_active (fun a -> a#insert_command "progress simpl.\n" "simpl.\n" ))
					   );
				    ignore (tactics_factory#add_item "_tauto"
					      ~key:GdkKeysyms._p
					      ~callback:(do_if_active (fun a -> a#insert_command "tauto.\n" "tauto.\n" ))
					   );
				    ignore (tactics_factory#add_item "_trivial"
					      ~key:GdkKeysyms._v
					      ~callback:(do_if_active( fun a -> a#insert_command "progress trivial.\n"  "trivial.\n" ))
					   );


				    ignore (toolbar#insert_button
					      ~tooltip:"Proof Wizard"
					      ~text:"Wizard"
					      ~icon:(stock_to_widget ~size:`LARGE_TOOLBAR `DIALOG_INFO)
					      ~callback:(do_if_active (fun a -> a#tactic_wizard
									 !current.automatic_tactics
								      ))
					      ());

				    ignore (tactics_factory#add_item "<Proof _Wizard>"
					      ~key:GdkKeysyms._dollar
					      ~callback:(do_if_active (fun a -> a#tactic_wizard 
									 !current.automatic_tactics
								      ))
					   );
				    
				    ignore (tactics_factory#add_separator ());
				    let add_simple_template (factory: GMenu.menu GMenu.factory) 
					(menu_text, text) =
				      let text = 
					let l = String.length text - 1 in
					  if String.get text l = '.'
					  then text ^"\n"
					  else text ^" "
				      in
					ignore (factory#add_item menu_text
						  ~callback:
						  (fun () -> let {view = view } = get_current_view () in
							       ignore (view#buffer#insert_interactive text)))
				    in
				      List.iter 
					(fun l -> 
					   match l with 
					     | [] -> ()
					     | [s] -> add_simple_template tactics_factory ("_"^s, s) 
					     | s::_ -> 
						 let a = "_@..." in
						   a.[1] <- s.[0];
						   let f = tactics_factory#add_submenu a in 
						   let ff = new GMenu.factory f ~accel_group in
						     List.iter 
						       (fun x -> 
							  add_simple_template
							    ff 
							    ((String.sub x 0 1)^
							       "_"^
							       (String.sub x 1 (String.length x - 1)),
							     x))
						       l
					) 
					Coq_commands.tactics;
				      
				      (* Templates Menu *)
				      let templates_menu =  factory#add_submenu "Te_mplates" in
				      let templates_factory = new GMenu.factory templates_menu 
					~accel_path:"<CoqIde MenuBar>/Templates/"
					~accel_group 
					~accel_modi:!current.modifier_for_templates
				      in
				      let add_complex_template (menu_text, text, offset, len, key) =
					(* Templates/Lemma *)
					let callback () =
					  let {view = view } = get_current_view () in
					    if view#buffer#insert_interactive text then begin
						let iter = view#buffer#get_iter_at_mark `INSERT in
						  ignore (iter#nocopy#backward_chars offset);
						  view#buffer#move_mark `INSERT iter;
						  ignore (iter#nocopy#backward_chars len);
						  view#buffer#move_mark `SEL_BOUND iter;
					      end in
					  ignore (templates_factory#add_item menu_text ~callback ?key)
				      in
					add_complex_template 
					  ("_Lemma __", "Lemma new_lemma : .\nProof.\n\nSave.\n", 
					   19, 9, Some GdkKeysyms._L);
					add_complex_template 
					  ("_Theorem __", "Theorem new_theorem : .\nProof.\n\nSave.\n", 
					   19, 11, Some GdkKeysyms._T);
					add_complex_template 
					  ("_Definition __", "Definition ident := .\n",
					   6, 5, Some GdkKeysyms._D);
					add_complex_template 
					  ("_Inductive __", "Inductive ident : :=\n  | : .\n",
					   14, 5, Some GdkKeysyms._I);
					add_complex_template 
					  ("_Fixpoint __", "Fixpoint ident (_ : _) {struct _} : _ :=\n.\n",
					   29, 5, Some GdkKeysyms._F);
					add_complex_template("_Scheme __",
							     "Scheme new_scheme := Induction for _ Sort _
with _ := Induction for _ Sort _.\n",61,10, Some GdkKeysyms._S);

					(* Template for match *)
					let callback () = 
					  let w = get_current_word () in
					    try 
					      let cases = Coq.make_cases w
					      in
					      let print c = function
						| [x] -> Format.fprintf c "  | %s => _@\n" x
						| x::l -> Format.fprintf c "  | (%s%a) => _@\n" x 
						    (print_list (fun c s -> Format.fprintf c " %s" s)) l
						| [] -> assert false
					      in
					      let b = Buffer.create 1024 in
					      let fmt = Format.formatter_of_buffer b in
						Format.fprintf fmt "@[match var with@\n%aend@]@."
						  (print_list print) cases;
						let s = Buffer.contents b in
						  prerr_endline s;
						  let {view = view } = get_current_view () in
						    ignore (view#buffer#delete_selection ());
						    let m = view#buffer#create_mark 
						      (view#buffer#get_iter `INSERT)
						    in
						      if view#buffer#insert_interactive s then 
							let i = view#buffer#get_iter (`MARK m) in
							let _ = i#nocopy#forward_chars 9 in
							  view#buffer#place_cursor i;
							  view#buffer#move_mark ~where:(i#backward_chars 3)
							    `SEL_BOUND 
					    with Not_found -> !flash_info "Not an inductive type"
					in
					  ignore (templates_factory#add_item "match ..."
						    ~key:GdkKeysyms._C
						    ~callback
						 );
					  
					  (*
					    let add_simple_template (factory: GMenu.menu GMenu.factory) 
					    (menu_text, text) =
					    let text = 
					    let l = String.length text - 1 in
					    if String.get text l = '.'
					    then text ^"\n"
					    else text ^" "
					    in
					    ignore (factory#add_item menu_text
					    ~callback:
					    (fun () -> let {view = view } = get_current_view () in
					    ignore (view#buffer#insert_interactive text)))
					    in
					  *)
					  ignore (templates_factory#add_separator ());
					  (*
					    List.iter (add_simple_template templates_factory)
					    [ "_auto", "auto ";
					    "_auto with *", "auto with * ";
					    "_eauto", "eauto ";
					    "_eauto with *", "eauto with * ";
					    "_intuition", "intuition ";
					    "_omega", "omega ";
					    "_simpl", "simpl ";
					    "_tauto", "tauto ";
					    "tri_vial", "trivial ";
					    ];
					    ignore (templates_factory#add_separator ());
					  *)
					  List.iter 
					    (fun l -> 
					       match l with 
						 | [] -> ()
						 | [s] -> add_simple_template templates_factory ("_"^s, s) 
						 | s::_ -> 
						     let a = "_@..." in
						       a.[1] <- s.[0];
						       let f = templates_factory#add_submenu a in 
						       let ff = new GMenu.factory f ~accel_group in
							 List.iter 
							   (fun x -> 
							      add_simple_template 
								ff 
								((String.sub x 0 1)^
								   "_"^
								   (String.sub x 1 (String.length x - 1)),
								 x))
							   l
					    ) 
					    Coq_commands.commands;
					  
					  (* Queries Menu *)
					  let queries_menu =  factory#add_submenu "_Queries" in
					  let queries_factory = new GMenu.factory queries_menu ~accel_group
					    ~accel_path:"<CoqIde MenuBar>/Queries"
					    ~accel_modi:[]
					  in
					    
					  (* Command/Show commands *)
					  let _ = 
					    queries_factory#add_item "_SearchAbout " ~key:GdkKeysyms._F2
					      ~callback:(fun () -> let term = get_current_word () in
								     (Command_windows.command_window ())#new_command
								       ~command:"SearchAbout"
								       ~term 
								       ())
					  in
					  let _ = 
					    queries_factory#add_item "_Check " ~key:GdkKeysyms._F3
					      ~callback:(fun () -> let term = get_current_word () in
								     (Command_windows.command_window ())#new_command
								       ~command:"Check"
								       ~term 
								       ())
					  in
					  let _ = 
					    queries_factory#add_item "_Print " ~key:GdkKeysyms._F4
					      ~callback:(fun () -> let term = get_current_word () in
								     (Command_windows.command_window ())#new_command
								       ~command:"Print"
								       ~term 
								       ())
					  in
					  let _ = 
					    queries_factory#add_item "_Whelp Locate" 
					      ~callback:(fun () -> let term = get_current_word () in
								     (Command_windows.command_window ())#new_command
								       ~command:"Whelp Locate"
								       ~term 
								       ())
					  in

					  (* Externals *)
					  let externals_menu =  factory#add_submenu "_Compile" in
					  let externals_factory = new GMenu.factory externals_menu 
					    ~accel_path:"<CoqIde MenuBar>/Compile/"
					    ~accel_group 
					    ~accel_modi:[]
					  in
					    
					  (* Command/Compile Menu *)
					  let compile_f () =
					    let v = get_current_view () in
					    let av = out_some v.analyzed_view in
					      save_f ();
					      match av#filename with
						| None -> 
						    !flash_info "Active buffer has no name"
						| Some f ->
						    let s,res = run_command 
						      av#insert_message 
						      (!current.cmd_coqc ^ " " ^ f) 
						    in
						      if s = Unix.WEXITED 0 then
							!flash_info (f ^ " successfully compiled")
						      else begin
							  !flash_info (f ^ " failed to compile");
							  activate_input (notebook ())#current_page;
							  av#process_until_end_or_error;
							  av#insert_message "Compilation output:\n";
							  av#insert_message res
							end
					  in
					  let _ = 
					    externals_factory#add_item "_Compile Buffer" ~callback:compile_f 
					  in

					  (* Command/Make Menu *)
					  let make_f () =
					    let v = get_active_view () in
					    let av = out_some v.analyzed_view in
					      (*
						save_f ();
					      *)
					      av#insert_message "Command output:\n";
					      let s,res = run_command av#insert_message !current.cmd_make in
						last_make := res;
						last_make_index := 0;
						!flash_info (!current.cmd_make ^ if s = Unix.WEXITED 0 then " succeeded" else " failed")
					  in
					  let _ = externals_factory#add_item "_Make" 
					    ~key:GdkKeysyms._F6
					    ~callback:make_f 
					  in
					    

					  (* Compile/Next Error *)
					  let next_error () = 
					    try
					      let file,line,start,stop,error_msg = search_next_error () in
						load file;
						let v = get_current_view () in
						let av = out_some v.analyzed_view in
						let input_buffer = v.view#buffer in
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
						  input_buffer#apply_tag_by_name "error"
   						    ~start:starti
						    ~stop:stopi;
						  input_buffer#place_cursor starti;
						  av#set_message error_msg;
						  v.view#misc#grab_focus ()
					    with Not_found ->
					      last_make_index := 0;
					      let v = get_current_view () in
					      let av = out_some v.analyzed_view in
						av#set_message "No more errors.\n"
					  in
					  let _ = 
					    externals_factory#add_item "_Next error" 
					      ~key:GdkKeysyms._F7
					      ~callback:next_error in
					    

					  (* Command/CoqMakefile Menu*)
					  let coq_makefile_f () =
					    let v = get_active_view () in
					    let av = out_some v.analyzed_view in
					    let s,res = run_command av#insert_message !current.cmd_coqmakefile in
					      !flash_info 
						(!current.cmd_coqmakefile ^ if s = Unix.WEXITED 0 then " succeeded" else " failed")
					  in
					  let _ = externals_factory#add_item "_Make makefile" ~callback:coq_makefile_f 
					  in
					    (* Windows Menu *)
					  let configuration_menu = factory#add_submenu "_Windows" in
					  let configuration_factory = new GMenu.factory configuration_menu ~accel_path:"<CoqIde MenuBar>/Windows" ~accel_group
					  in
					  let _ = 
					    configuration_factory#add_item 
					      "Show _Query Window"
					      (*
						~key:GdkKeysyms._F12
					      *)
					      ~callback:(Command_windows.command_window ())#window#present
					  in  
					  let _ = 
					    configuration_factory#add_item 
					      "Show/Hide _Toolbar"	       
					      ~callback:(fun () ->  
							   !current.show_toolbar <- not !current.show_toolbar; 
							   !show_toolbar !current.show_toolbar) 
					  in
					  let _ = configuration_factory#add_item 
					    "Detach _Script Window"
					    ~callback:
					    (do_if_not_computing "detach script window" (sync
											   (fun () -> 
											      let nb = notebook () in
												if nb#misc#toplevel#get_oid=w#coerce#get_oid then
												  begin  
												    let nw = GWindow.window ~show:true () in
												    let parent = out_some nb#misc#parent in
												      ignore (nw#connect#destroy 
														~callback:
														(fun () -> nb#misc#reparent parent));
												      nw#add_accel_group accel_group;
												      nb#misc#reparent nw#coerce
												  end	      
											   )))
					  in
					  let _ = 
					    configuration_factory#add_item 
					      "Detach _View"
					      ~callback:
					      (do_if_not_computing "detach view"
						 (fun () -> 
						    match get_current_view () with  
						      | {view=v;analyzed_view=Some av} -> 
							  let w = GWindow.window ~show:true 
							    ~width:(!current.window_width/2)
							    ~height:(!current.window_height)
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
							    av#add_detached_view w
						      | _ -> ()
							  
						 ))
					  in
					    (* Help Menu *)

					  let help_menu = factory#add_submenu "_Help" in
					  let help_factory = new GMenu.factory help_menu  
					    ~accel_path:"<CoqIde MenuBar>/Help/"
					    ~accel_modi:[]
					    ~accel_group in
					  let _ = help_factory#add_item "Browse Coq _Manual" 
					    ~callback:
					    (fun () -> 
					       let av = out_some ((get_current_view ()).analyzed_view) in 
						 browse av#insert_message (!current.doc_url ^ "main.html")) in
					  let _ = help_factory#add_item "Browse Coq _Library" 
					    ~callback:
					    (fun () -> 
					       let av = out_some ((get_current_view ()).analyzed_view) in 
						 browse av#insert_message !current.library_url) in
					  let _ = 
					    help_factory#add_item "Help for _keyword" ~key:GdkKeysyms._F1
					      ~callback:(fun () -> 
							   let av = out_some ((get_current_view ()).analyzed_view) in 
							     av#help_for_keyword ())
					  in
					  let _ = help_factory#add_separator () in
					    (*
					      let faq_m = help_factory#add_item "_FAQ" in
					    *)
					  let about_m = help_factory#add_item "_About" in

					  (* End of menu *)

					  (* The vertical Separator between Scripts and Goals *)
					  let hb = GPack.paned `HORIZONTAL  ~border_width:5 ~packing:vbox#add () in
					  let fr_notebook = GBin.frame ~shadow_type:`IN ~packing:hb#add1 () in
					    _notebook := Some (GPack.notebook ~border_width:2 ~show_border:false ~scrollable:true 
								 ~packing:fr_notebook#add
								 ());
					    let nb = notebook () in
					    let hb2 = GPack.paned `VERTICAL ~packing:hb#add2 () in
					    let fr_a = GBin.frame ~shadow_type:`IN ~packing:hb2#add () in
					    let fr_b = GBin.frame ~shadow_type:`IN ~packing:hb2#add () in
					    let sw2 = GBin.scrolled_window 
					      ~vpolicy:`AUTOMATIC 
					      ~hpolicy:`AUTOMATIC
					      ~packing:(fr_a#add) () in
					    let sw3 = GBin.scrolled_window 
					      ~vpolicy:`AUTOMATIC 
					      ~hpolicy:`AUTOMATIC
					      ~packing:(fr_b#add) () in
					    let lower_hbox = GPack.hbox ~homogeneous:false ~packing:vbox#pack () in
					    let status_bar = GMisc.statusbar ~packing:(lower_hbox#pack ~expand:true) () 
					    in
					    let search_lbl = GMisc.label ~text:"Search:"
					      ~show:false
					      ~packing:(lower_hbox#pack ~expand:false) () 
					    in
					    let search_history = ref [] in
					    let search_input = GEdit.combo ~popdown_strings:!search_history
					      ~enable_arrow_keys:true
					      ~show:false
					      ~packing:(lower_hbox#pack ~expand:false) () 
					    in
					      search_input#disable_activate ();
					      let ready_to_wrap_search = ref false in

					      let start_of_search = ref None in
					      let start_of_found = ref None in
					      let end_of_found = ref None in
					      let search_forward = ref true in
					      let matched_word = ref None in

					      let memo_search () = 
						matched_word := Some search_input#entry#text

					      (*     if not (List.mem search_input#entry#text !search_history) then
						     (search_history := 
						     search_input#entry#text::!search_history;
						     search_input#set_popdown_strings !search_history);
						     start_of_search := None;
						     ready_to_wrap_search := false
					      *)

					      in
					      let end_search () = 
						prerr_endline "End Search";
						memo_search ();
						let v = (get_current_view ()).view in
						  v#buffer#move_mark `SEL_BOUND (v#buffer#get_iter_at_mark `INSERT);
						  v#coerce#misc#grab_focus ();
						  search_input#entry#set_text "";
						  search_lbl#misc#hide ();
						  search_input#misc#hide ()
					      in
					      let end_search_focus_out () = 
						prerr_endline "End Search(focus out)";
						memo_search ();
						let v = (get_current_view ()).view in
						  v#buffer#move_mark `SEL_BOUND (v#buffer#get_iter_at_mark `INSERT);
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
							Some ((get_current_view ()).view#buffer#create_mark 
								((get_current_view ()).view#buffer#get_iter_at_mark `INSERT));
						      start_of_found := !start_of_search;
						      end_of_found := !start_of_search;
						      matched_word := Some "";
						    end;
						  let txt = search_input#entry#text in 
						  let v = (get_current_view ()).view in
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
								     !flash_info (t^"\n"^txt);
								     t = txt)
								with 
								  | true,true -> 
								      (!flash_info "T,T";iit#backward_search txt)
								  | false,true -> !flash_info "F,T";Some (iit,npi)
								  | _,false ->
								      (iit#backward_search txt)

						     with 
						       | None -> 
							   if !ready_to_wrap_search then begin
							       ready_to_wrap_search := false;
							       !flash_info "Search wrapped";
							       v#buffer#place_cursor 
								 (if !search_forward then v#buffer#start_iter else
								      v#buffer#end_iter);
							       search_f ()
							     end else begin
								 if !search_forward then !flash_info "Search at end"
								 else !flash_info "Search at start";
								 ready_to_wrap_search := true
							       end
						       | Some (start,stop) -> 
							   prerr_endline "search: before moving marks";
							   prerr_endline ("SELBOUND="^(string_of_int (v#buffer#get_iter_at_mark `SEL_BOUND)#offset));
							   prerr_endline ("INSERT="^(string_of_int (v#buffer#get_iter_at_mark `INSERT)#offset));

							   v#buffer#move_mark `SEL_BOUND start;
							   v#buffer#move_mark `INSERT stop;
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
								   let v = (get_current_view ()).view in
								     (match !start_of_search with 
									| None -> 
									    prerr_endline "search_key_rel: Placing sel_bound";
									    v#buffer#move_mark 
									      `SEL_BOUND 
									      (v#buffer#get_iter_at_mark `INSERT)
									| Some mk -> let it = v#buffer#get_iter_at_mark 
									    (`MARK mk) in
										       prerr_endline "search_key_rel: Placing cursor";
									    v#buffer#place_cursor it;
									    start_of_search := None
								     );
								     search_input#entry#set_text ""; 
								     v#coerce#misc#grab_focus ();
								 end; 
							       false
							    ));
						  ignore (search_input#entry#connect#changed search_f);
						  
						  (*
						    ignore (search_if#connect#activate
						    ~callback:(fun b -> 
						    search_forward:= true;
						    search_input#entry#coerce#misc#grab_focus ();
						    search_f ();
						    )
						    );
						    ignore (search_ib#connect#activate
						    ~callback:(fun b ->
						    search_forward:= false;

						  (* Must restore the SEL_BOUND mark after 
						    grab_focus ! *)
						    let v = (get_current_view ()).view in
						    let old_sel = v#buffer#get_iter_at_mark `SEL_BOUND 
						    in
						    search_input#entry#coerce#misc#grab_focus ();
						    v#buffer#move_mark `SEL_BOUND old_sel;
						    search_f ();
						    ));
						  *)
						  let status_context = status_bar#new_context "Messages" in
						  let flash_context = status_bar#new_context "Flash" in
						    ignore (status_context#push "Ready");
						    status := Some status_bar;
						    push_info := (fun s -> ignore (status_context#push s));
						    pop_info := (fun () -> status_context#pop ());
						    flash_info := (fun ?(delay=5000) s -> flash_context#flash ~delay s);

						    (* Location display *)
						    let l = GMisc.label
						      ~text:"Line:     1 Char:   1" 
						      ~packing:lower_hbox#pack () in 
						      l#coerce#misc#set_name "location";
						      set_location := l#set_text;

						      (* Progress Bar *)
						      pulse := 
							(let pb = GRange.progress_bar ~pulse_step:0.2 ~packing:lower_hbox#pack ()
							 in pb#set_text "CoqIde started";pb)#pulse;
						      let tv2 = GText.view ~packing:(sw2#add) () in
							tv2#misc#set_name "GoalWindow";
							let _ = tv2#set_editable false in
							let _ = tv2#buffer in
							let tv3 = GText.view ~packing:(sw3#add) () in
							  tv2#misc#set_name "MessageWindow";
							  let _ = tv2#set_wrap_mode `CHAR in
							  let _ = tv3#set_wrap_mode `WORD in
							  let _ = tv3#set_editable false in
							  let _ = GtkBase.Widget.add_events tv2#as_widget
							    [`ENTER_NOTIFY;`POINTER_MOTION] in
							  let _ =
							    tv2#event#connect#motion_notify
							      ~callback:
							      (fun e -> 
								 let win = match tv2#get_window `WIDGET with
								   | None -> assert false
								   | Some w -> w in
								 let x,y = Gdk.Window.get_pointer_location win in
								 let b_x,b_y = tv2#window_to_buffer_coords ~tag:`WIDGET ~x ~y in
								 let it = tv2#get_iter_at_location ~x:b_x ~y:b_y in
								 let tags = it#tags in
								   List.iter 
								     (fun t ->
									ignore(GtkText.Tag.event t#as_tag tv2#as_widget e it#as_iter))
								     tags;
								   false) in
							    change_font := 
							      (fun fd -> 
								 tv2#misc#modify_font fd;
								 tv3#misc#modify_font fd;
								 Vector.iter 
								   (fun {view=view} -> view#misc#modify_font fd)
								   input_views;
							      );
							    let about (b:GText.buffer) =
							      (try 
								   let image = lib_ide_file "coq.png" in
								   let startup_image = GdkPixbuf.from_file image in
								     b#insert_pixbuf ~iter:b#start_iter 
								       ~pixbuf:startup_image;
								     b#insert ~iter:b#start_iter "\t\t";
							       with _ -> ());
							      let about_string =
								"\nCoqIDE: an Integrated Development Environment for Coq\n\
       \nMain author  : Benjamin Monate\
       \nContributors : Jean-Christophe Filliâtre\
       \n               Pierre Letouzey, Claude Marché\n\
       \nFeature wish or bug report: use Web interface\n\
       \n\thttp://coq.inria.fr/bin/coq-bugs\n\
       \nVersion information\
       \n-------------------\n"
							      in
								if Glib.Utf8.validate about_string
								then b#insert about_string;
								let coq_version = Coq.version () in
								  if Glib.Utf8.validate coq_version
								  then b#insert coq_version;
								  
							    in
							      about  tv2#buffer;
							      w#add_accel_group accel_group;
							      (* Remove default pango menu for textviews *)
							      ignore (tv2#event#connect#button_press ~callback:
									(fun ev -> GdkEvent.Button.button ev = 3));
							      ignore (tv3#event#connect#button_press ~callback:
									(fun ev -> GdkEvent.Button.button ev = 3));
							      tv2#misc#set_can_focus true;
							      tv3#misc#set_can_focus true;
							      ignore (tv2#buffer#create_mark 
									~name:"end_of_conclusion" 
									tv2#buffer#start_iter);
							      ignore (tv3#buffer#create_tag 
									~name:"error" 
									[`FOREGROUND "red"]);
							      w#show ();
							      message_view := Some tv3;
							      proof_view := Some tv2;
							      tv2#misc#modify_font !current.text_font; 
							      tv3#misc#modify_font !current.text_font;
							      ignore (about_m#connect#activate 
									~callback:(fun () -> tv2#buffer#set_text ""; about tv2#buffer));
							      (*
								ignore (faq_m#connect#activate 
								~callback:(fun () -> 
								load (lib_ide_file "FAQ")));
								
							      *)
							      resize_window := (fun () -> 
										  w#resize 
										    ~width:!current.window_width
										    ~height:!current.window_height);

							      ignore (w#misc#connect#size_allocate 
									(let old_w = ref 0 
									 and old_h = ref 0 in
									   fun {Gtk.width=w;Gtk.height=h} -> 
									     if !old_w <> w or !old_h <> h then
									       begin
										 old_h := h;
										 old_w := w;
										 hb#set_position (w/2);
										 hb2#set_position (h/2);
										 !current.window_height <- h;
										 !current.window_width <- w;
									       end
									));
							      ignore(nb#connect#switch_page
								       ~callback:
								       (fun i -> 
									  prerr_endline ("switch_page: starts " ^ string_of_int i);
									  List.iter (function f -> f i) !to_do_on_page_switch;
									  prerr_endline "switch_page: success")
								    );
							      ignore(tv2#event#connect#enter_notify
								       (fun _ -> 
									  if !current.contextual_menus_on_goal then
									    begin
									      let w = (out_some (get_active_view ()).analyzed_view) in
										!push_info "Computing advanced goal's menus";
										prerr_endline "Entering Goal Window. Computing Menus....";
										w#show_goals_full;
										prerr_endline "....Done with Goal menu";
										!pop_info();
									    end;
									  false;
								       ));
							      if List.length files >=1 then
								begin
								  List.iter (fun f -> 
									       if Sys.file_exists f then load f else 
										 if Filename.check_suffix f ".v" 
										 then load f 
										 else load (f^".v")) files;
								  activate_input 0
								end
							      else
								begin
								  let view = create_input_tab "*Unnamed Buffer*" in
								  let index = add_input_view {view = view;
											      analyzed_view = None;
											     }
								  in
								    (get_input_view index).analyzed_view <- Some (new analyzed_view index);
								    activate_input index;
								    set_tab_image index ~icon:`YES;
								    view#misc#modify_font !current.text_font
								end;

;;

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
		 (get_current_view()).view#buffer#insert (s^"\n");
	       cb_Dr#set_text "Ack"
	   | None -> ()
	);
	(* cb_Dr#clear does not work so i use : *)
	(* cb_Dr#set_text "Ack" *) 
    done
      
      
let start () = 
  let files = Coq.init () in
    ignore_break ();
    GtkMain.Rc.add_default_file (lib_ide_file ".coqide-gtk2rc");
    (try 
	 GtkMain.Rc.add_default_file (Filename.concat System.home ".coqide-gtk2rc");
     with Not_found -> ());
    ignore (GtkMain.Main.init ());
    GtkData.AccelGroup.set_default_mod_mask 
      (Some [`CONTROL;`SHIFT;`MOD1;`MOD3;`MOD4]);
    cb_ := Some (GData.clipboard Gdk.Atom.primary);
    ignore (
	     Glib.Message.set_log_handler ~domain:"Gtk" ~levels:[`ERROR;`FLAG_FATAL;
								 `WARNING;`CRITICAL]
	       (fun ~level msg -> 
		  if level land Glib.Message.log_level `WARNING <> 0
		  then Pp.warning msg
		  else failwith ("Coqide internal error: " ^ msg)));
    Command_windows.main ();
    Blaster_window.main 9;
    main files;
    if !Coq_config.with_geoproof then ignore (Thread.create check_for_geoproof_input ()); 
    while true do 
      try 
	GtkThread.main ()	
      with
	| Sys.Break -> prerr_endline "Interrupted." ; flush stderr
	| e -> 
	    Pervasives.prerr_endline ("CoqIde unexpected error:" ^ (Printexc.to_string e));
	    flush stderr;
	    crash_save 127
    done
      
      
