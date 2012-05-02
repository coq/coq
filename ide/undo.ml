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

class undoable_view (tv : source_view) =
  let undo_lock = ref true in
object(self)
  inherit GSourceView2.source_view (Gobject.unsafe_cast tv) as super
  val history = (Stack.create () : action Stack.t)
  val redo = (Queue.create () : action Queue.t)
  val nredo = (Stack.create () : action Stack.t)

  method private dump_debug =
    if false (* !debug *) then begin
      prerr_endline "==========Stack top=============";
      Stack.iter
	(fun e -> match e with
	   | Insert(s,p,l) ->
 	       Printf.eprintf "Insert of '%s' at %d (length %d)\n" s p l
	   | Delete(s,p,l) ->
	       Printf.eprintf "Delete '%s' from %d (length %d)\n" s p l)
	history;
      Printf.eprintf "Stack size %d\n" (Stack.length history);
      prerr_endline "==========Stack Bottom==========";
      prerr_endline "==========Queue start=============";
      Queue.iter
	(fun e -> match e with
	   | Insert(s,p,l) ->
 	       Printf.eprintf "Insert of '%s' at %d (length %d)\n" s p l
	   | Delete(s,p,l) ->
	       Printf.eprintf "Delete '%s' from %d (length %d)\n" s p l)
	redo;
      Printf.eprintf "Stack size %d\n" (Queue.length redo);
      prerr_endline "==========Queue End=========="

    end

  method clear_undo = Stack.clear history; Stack.clear nredo; Queue.clear redo

  method undo = if !undo_lock then begin
    undo_lock := false;
    prerr_endline "UNDO";
    try begin
      let r =
	match Stack.pop history with
	  | Insert(s,p,l) as act ->
	      let start = self#buffer#get_iter_at_char p in
	      (self#buffer#delete_interactive
		 ~start
		 ~stop:(start#forward_chars l)
		 ()) or
	      (Stack.push act history; false)
	  | Delete(s,p,l) as act ->
	      let iter = self#buffer#get_iter_at_char p in
	      (self#buffer#insert_interactive ~iter s) or
	      (Stack.push act history; false)
      in if r then begin
	let act = Stack.pop history in
	Queue.push act redo;
	Stack.push act nredo
      end;
      undo_lock := true;
      r
    end
    with Stack.Empty ->
      undo_lock := true;
      false
  end else
    (prerr_endline "UNDO DISCARDED"; true)

  method redo = prerr_endline "REDO"; true
  initializer
(* INCORRECT: is called even while undoing...
   ignore (self#buffer#connect#mark_set
	      ~callback:
	      (fun it tm -> if !undo_lock && not (Queue.is_empty redo) then begin
		 Stack.iter (fun e -> Stack.push (neg e) history) nredo;
		 Stack.clear nredo;
		 Queue.iter (fun e -> Stack.push e history) redo;
		 Queue.clear redo;
	       end)
	   );
*)
    ignore (self#buffer#connect#insert_text
	      ~callback:
	      (fun it s ->
		 if !undo_lock && not (Queue.is_empty redo) then begin
		   Stack.iter (fun e -> Stack.push (neg e) history) nredo;
		   Stack.clear nredo;
		   Queue.iter (fun e -> Stack.push e history) redo;
		   Queue.clear redo;
		 end;
(*		 let pos = it#offset in
		 if Stack.is_empty history or
		   s=" " or s="\t" or s="\n" or
					(match Stack.top history with
					   | Insert(old,opos,olen) ->
					       opos + olen <> pos
					   | _ -> true)
		 then *)
		 Stack.push (Insert(s,it#offset,Glib.Utf8.length s)) history
		 (*else begin
		   match Stack.pop history with
		     | Insert(olds,offset,len) ->
			 Stack.push
			 (Insert(olds^s,
				 offset,
				 len+(Glib.Utf8.length s)))
			 history
		     | _ -> assert false
		   end*);
		 self#dump_debug
	      ));
    ignore (self#buffer#connect#delete_range
	      ~callback:
	      (fun ~start ~stop ->
		 if !undo_lock && not (Queue.is_empty redo) then begin
		   Queue.iter (fun e -> Stack.push e history) redo;
		   Queue.clear redo;
		 end;
		 let start_offset = start#offset in
		 let stop_offset = stop#offset in
		 let s = self#buffer#get_text ~start ~stop () in
(*		 if Stack.is_empty history or (match Stack.top history with
						 | Delete(old,opos,olen) ->
						     olen=1 or opos <> start_offset
						 | _ -> true
					      )
		 then
*)		   Stack.push
		     (Delete(s,
			     start_offset,
			     stop_offset - start_offset
			    ))
		     history
	(*	 else begin
		   match Stack.pop history with
		     | Delete(olds,offset,len) ->
			 Stack.push
			 (Delete(olds^s,
				 offset,
				 len+(Glib.Utf8.length s)))
			 history
		     | _ -> assert false

		 end*);
		 self#dump_debug
	      ))
end

let undoable_view ?(source_buffer:GSourceView2.source_buffer option)  ?draw_spaces =
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
		   ((new undoable_view w) : undoable_view))))
