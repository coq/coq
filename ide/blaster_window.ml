(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

class blaster_window (n:int) = 
  let window = GWindow.window 
		 ~allow_grow:true ~allow_shrink:true 
		 ~width:320 ~height:200
		 ~title:"Blaster Window" ~show:false ()
  in
  let box1 = GPack.vbox ~packing:window#add () in
  let table = GPack.table ~rows:(n/4+1) ~columns:4 ~homogeneous:false 
		~row_spacings:3 ~col_spacings:3 ~border_width:10
		~packing:box1#add () in


  let _ = GMisc.separator `HORIZONTAL ~packing:box1#pack () in
  
  let box2 = GPack.vbox ~spacing: 10 ~border_width: 10 ~packing: box1#pack () in

  let button_stop = GButton.button ~label: "Stop" ~packing: box2#add () in
  let _ = button_stop#connect#clicked ~callback: window#misc#hide in

  let buttons = Array.create n ((GButton.button ~label:"Nothing" ()),(fun () -> Coq.Interrupted)) 
  in
  
object(self)
  val window = window
  val buttons = buttons
  method window = window
  method buttons = buttons
  method set i name (compute:unit -> Coq.tried_tactic) (on_click:unit -> unit) = 
    let button = GButton.button ~label: (name) () in
    buttons.(i) <- (button,compute);
    let x = i/4 in
    let y = i mod 4 in
    table#attach button#coerce 
      ~left:x ~top:y
      ~xpadding:0 ~ypadding:0 ~expand:`BOTH;
    ignore (button#connect#clicked ~callback:on_click)

  method blaster () = 
    for i = 0 to n-1 do 
      let b,f = buttons.(i) in
      GtkButton.Button.set_label (Obj.magic b#as_widget) 
	(GtkButton.Button.get_label (Obj.magic b#as_widget)^": ");
      match f () with 
      | Coq.Interrupted -> 
	  prerr_endline "Interrupted"
      | Coq.Failed -> 
	  prerr_endline "Failed"
      | Coq.Success n -> 
	  GtkButton.Button.set_label (Obj.magic b#as_widget) 
	  (GtkButton.Button.get_label (Obj.magic b#as_widget)^ (string_of_int n));
    done
  initializer 
    ignore (window#event#connect#delete (fun _ -> window#misc#hide(); true));
end

let blaster_window = ref None

let main n = blaster_window := Some (new blaster_window n)

let blaster_window () = match !blaster_window with 
  | None -> failwith "No blaster window."
  | Some c -> c#window#present (); c


