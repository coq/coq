(***********************************************************************)
(*                               Okey                                  *)
(*                                                                     *)
(*            Maxence Guesdon, projet Cristal, INRIA Rocquencourt      *)
(*                                                                     *)
(*  Copyright 2001 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

type modifier = Gdk.Tags.modifier

type handler = {
    cond : (unit -> bool) ;
    cback : (unit -> unit) ;
  } 

type handler_spec = int * int * Gdk.keysym
      (** mods * mask * key *)

let int_of_modifier = function
    `SHIFT -> 1
  | `LOCK -> 2
  | `CONTROL -> 4
  | `MOD1 -> 8
  | `MOD2 -> 16
  | `MOD3 -> 32
  | `MOD4 -> 64
  | `MOD5 -> 128
  | `BUTTON1 -> 256
  | `BUTTON2 -> 512
  | `BUTTON3 -> 1024
  | `BUTTON4 -> 2048
  | `BUTTON5 -> 4096

let print_modifier l =
  List.iter
    (fun m -> 
      print_string
	(((function 
	    `SHIFT -> "SHIFT"
	  | `LOCK -> "LOCK"
	  | `CONTROL -> "CONTROL"
	  | `MOD1 -> "MOD1"
	  | `MOD2 -> "MOD2"
	  | `MOD3 -> "MOD3"
	  | `MOD4 -> "MOD4"
	  | `MOD5 -> "MOD5"
	  | `BUTTON1 -> "B1"
	  | `BUTTON2 -> "B2"
	  | `BUTTON3 -> "B3"
	  | `BUTTON4 -> "B4"
	  | `BUTTON5 -> "B5")
	    m)^" ")
    )
    l;
  print_newline ()
  
let int_of_modifiers l =
  List.fold_left (fun acc -> fun m -> acc + (int_of_modifier m)) 0 l

module H = 
  struct
    type t = handler_spec * handler
    let equal (m,k) (mods, mask, key) =
      (k = key) && ((m land mask) = mods)

    let filter_with_mask mods mask key l =
      List.filter (fun a -> (fst a) <> (mods, mask, key)) l

    let find_handlers mods key l =
      List.map snd
        (List.filter
	   (fun ((m,ma,k),_) -> equal (mods,key) (m,ma,k)) 
	   l
	)

  end

let (table : (int, H.t list ref) Hashtbl.t) = Hashtbl.create 13

let key_press w ev =
  let key = GdkEvent.Key.keyval ev in
  let modifiers = GdkEvent.Key.state ev in
  try
    let (r : H.t list ref) = Hashtbl.find table w#get_oid in
    let l = H.find_handlers (int_of_modifiers modifiers) key !r in
    let b = ref true in
    List.iter
      (fun h ->
	if h.cond () then
	  (h.cback () ; b := false)
	else
	  ()
      )
      l;
    !b
  with
    Not_found ->
      true

let associate_key_press w = 
  ignore ((w#event#connect#key_press ~callback: (key_press w)) : GtkSignal.id)

let default_modifiers = ref ([] : modifier list)
let default_mask = ref ([`MOD2 ; `MOD3 ; `MOD4 ; `MOD5 ; `LOCK] : modifier list)

let set_default_modifiers l = default_modifiers := l
let set_default_mask l = default_mask := l

let remove_widget  (w : < event : GObj.event_ops ; get_oid : int ; ..>) () =
  try 
    let r = Hashtbl.find table w#get_oid in
    r := []
  with 
    Not_found ->
      ()

let add1 ?(remove=false) w
    ?(cond=(fun () -> true)) 
    ?(mods= !default_modifiers)
    ?(mask= !default_mask)
    k callback =
  let r =
    try Hashtbl.find table w#get_oid
    with Not_found -> 
      let r = ref [] in
      Hashtbl.add table w#get_oid r;
      ignore (w#connect#destroy ~callback: (remove_widget w));
      associate_key_press w;
      r
  in
  let n_mods = int_of_modifiers mods in
  let n_mask = lnot (int_of_modifiers mask) in
  let new_h = { cond = cond ; cback = callback } in
  if remove then 
    (
     let l = H.filter_with_mask n_mods n_mask k !r in
     r := ((n_mods, n_mask, k), new_h) :: l
    )
  else
    r := ((n_mods, n_mask, k), new_h) :: !r

let add w
    ?(cond=(fun () -> true)) 
    ?(mods= !default_modifiers)
    ?(mask= !default_mask)
    k callback =
  add1 w ~cond ~mods ~mask k callback

let add_list w
    ?(cond=(fun () -> true)) 
    ?(mods= !default_modifiers)
    ?(mask= !default_mask)
    k_list callback =
  List.iter (fun k -> add w ~cond ~mods ~mask k callback) k_list

let set w
    ?(cond=(fun () -> true)) 
    ?(mods= !default_modifiers)
    ?(mask= !default_mask)
    k callback =
  add1 ~remove: true w ~cond ~mods ~mask k callback

let set_list w
    ?(cond=(fun () -> true)) 
    ?(mods= !default_modifiers)
    ?(mask= !default_mask)
    k_list callback =
  List.iter (fun k -> set w ~cond ~mods ~mask k callback) k_list

