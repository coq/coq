(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Gobject.Data
open Ideutils

exception Stop
exception Done

module MyMap = Map.Make (struct type t = string let compare = compare end)

class blaster_window (n:int) = 
  let window = GWindow.window 
		 ~allow_grow:true ~allow_shrink:true 
		 ~width:320 ~height:200
		 ~title:"Blaster Window" ~show:false ()
  in
  let box1 = GPack.vbox ~packing:window#add () in
  let sw = GBin.scrolled_window ~packing:(box1#pack ~expand:true ~fill:true) () in

  let cols = new GTree.column_list in
  let argument = cols#add string in
  let tactic = cols#add string in
  let status = cols#add boolean in
  let nb_goals = cols#add string in
  
  let model = GTree.tree_store cols in
  let new_arg s =
    let row = model#append () in
    model#set ~row ~column:argument s;
    row
  in
  let new_tac arg s =  
    let row = model#append ~parent:arg () in
    model#set ~row ~column:tactic s;
    model#set ~row ~column:status false;
    model#set ~row ~column:nb_goals "?";
    row
  in
  let view = GTree.view ~model ~packing:sw#add () in
  let _ = view#selection#set_mode `SINGLE in
  let _ = view#set_rules_hint true in

  let col = GTree.view_column ~title:"Argument" ()
	      ~renderer:(GTree.cell_renderer_text [], ["text",argument]) in
  let _ = view#append_column col in
  let col = GTree.view_column ~title:"Tactics" ()
	      ~renderer:(GTree.cell_renderer_text [], ["text",tactic]) in
  let _ = view#append_column col in
  let col = GTree.view_column ~title:"Status" ()
	      ~renderer:(GTree.cell_renderer_toggle [], ["active",status]) in
  let _ = view#append_column col in
  let col = GTree.view_column ~title:"Delta Goal" ()
	      ~renderer:(GTree.cell_renderer_text [], ["text",nb_goals]) in
  let _ = view#append_column col in 

  let _ = GMisc.separator `HORIZONTAL ~packing:box1#pack () in
  
  let box2 = GPack.vbox ~spacing: 10 ~border_width: 10 ~packing: box1#pack () 
  in
  let button_stop = GButton.button ~label: "Stop" ~packing: box2#add () in
  let _ = button_stop#connect#clicked ~callback: window#misc#hide in

object(self)
  val window = window
  val roots = Hashtbl.create 17
  val mutable tbl = MyMap.empty 
  val blaster_lock = Mutex.create () 
  method lock = blaster_lock 
  val blaster_killed = Condition.create () 
  method blaster_killed = blaster_killed
  method window = window
  method set root name (compute:unit -> Coq.tried_tactic) (on_click:unit -> unit) = 
    let root_iter = 
      try Hashtbl.find roots root 
      with Not_found -> 
	let nr = new_arg root in
	  Hashtbl.add roots root nr;
	  nr
    in
    let nt = new_tac root_iter name in
    let old_val = try MyMap.find root tbl with Not_found -> MyMap.empty in
      tbl <- MyMap.add root (MyMap.add name (nt,compute,on_click) old_val) tbl

  method clear () = 
    model#clear ();      
    tbl <- MyMap.empty;
    Hashtbl.clear roots;
    
  method blaster () = 
    view#expand_all ();
    try MyMap.iter 
      (fun root_name l ->
	 try 
	   MyMap.iter 
	     (fun name (nt,compute,on_click) ->  
		match compute () with 
		  | Coq.Interrupted -> 
		      prerr_endline "Interrupted";
		      raise Stop
		  | Coq.Failed -> 
		      prerr_endline "Failed";
		      ignore (model#remove nt)
			(*	       model#set ~row:nt ~column:status false;
				       model#set ~row:nt ~column:nb_goals "N/A"
			*)
		  | Coq.Success n -> 
		      prerr_endline "Success";
		      model#set ~row:nt ~column:status true;
		      model#set ~row:nt ~column:nb_goals (string_of_int n);
		      if n= -1 then raise Done 
	     )
	     l
	 with Done -> ())
      tbl;
      Condition.signal blaster_killed;
      prerr_endline "End of blaster";
    with Stop ->
      Condition.signal blaster_killed;
      prerr_endline "End of blaster (stopped !)";

  initializer 
    ignore (window#event#connect#delete (fun _ -> window#misc#hide(); true));
    ignore (view#selection#connect#after#changed ~callback:
	      begin fun () ->
		prerr_endline "selection changed";
		List.iter 
		  (fun path ->let pt = GtkTree.TreePath.to_string path in
		     let it = model#get_iter path in
		     prerr_endline (string_of_bool (model#iter_is_valid it));
		     let name = model#get 
				  ~row:(if String.length pt >1 then begin
					  ignore (GtkTree.TreePath.up path);
					  model#get_iter path
					end else it
				       ) 
				  ~column:argument in
		     let tactic = model#get ~row:it ~column:tactic in
		     prerr_endline ("Got name: "^name);
		     let success = model#get ~row:it ~column:status in
		     if success then try 
		       prerr_endline "Got success";
		       let _,_,f = MyMap.find tactic (MyMap.find name tbl) in
		       f ();
		       (* window#misc#hide () *)
		     with _ -> ()
		  )
		  view#selection#get_selected_rows
	      end);

(* needs lablgtk2 update    ignore (view#connect#after#row_activated
   (fun path vcol ->
   prerr_endline "Activated";
   );
*)
end

let blaster_window = ref None

let main n = blaster_window := Some (new blaster_window n)

let present_blaster_window () = match !blaster_window with 
  | None -> failwith "No blaster window."
  | Some c -> c#window#misc#show (* present*) (); c


let blaster_window () = match !blaster_window with 
  | None -> failwith "No blaster window."
  | Some c -> c


