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

(** Okey interface. 

   Once the lib is compiled and installed, you can use it by referencing
   it with the [Okey] module. You must add [okey.cmo] or [okey.cmx]
   on the commande line when you link.
*)

type modifier = Gdk.Tags.modifier

(** Set the default modifier list. The first default value is [[]].*)
val set_default_modifiers : modifier list -> unit

(** Set the default modifier mask. The first default value is 
   [[`MOD2 ; `MOD3 ; `MOD4 ; `MOD5 ; `LOCK]].
   The mask defines the modifiers not taken into account
   when looking for the handler of a key press event.
*)
val set_default_mask : modifier list -> unit

(** [add widget key callback] associates the [callback] function to the event
   "key_press" with the given [key] for the given [widget].

   @param remove when true, the previous handlers for the given key and modifier
   list are not kept.
   @param cond this function is a guard: the [callback] function is not called
   if the [cond] function returns [false]. 
   The default [cond] function always returns [true].

   @param mods the list of modifiers. If not given, the default modifiers
   are used. 
   You can set the default modifiers with function {!Okey.set_default_modifiers}.

   @param mask the list of modifiers which must not be taken
   into account to trigger the given handler. [mods]
   and [mask] must not have common modifiers. If not given, the default mask
   is used. 
   You can set the default modifiers mask with function {!Okey.set_default_mask}.
*)
val add :
    < connect : < destroy : callback: (unit -> unit) -> GtkSignal.id; .. >;
      event : GObj.event_ops; get_oid : int; .. > -> 
	?cond: (unit -> bool) -> 
	  ?mods: modifier list -> 
	    ?mask: modifier list -> 
	      Gdk.keysym -> 
		(unit -> unit) -> 
		  unit

(** It calls {!Okey.add} for each given key.*)
val add_list : 
    < connect : < destroy : callback: (unit -> unit) -> GtkSignal.id; .. >;
      event : GObj.event_ops; get_oid : int; .. > -> 
	?cond: (unit -> bool) -> 
	  ?mods: modifier list -> 
	    ?mask: modifier list -> 
	      Gdk.keysym list -> 
		(unit -> unit) -> 
		  unit
	      
(** Like {!Okey.add} but the previous handlers for the
   given modifiers and key are not kept.*)
val set :
    < connect : < destroy : callback: (unit -> unit) -> GtkSignal.id; .. >;
      event : GObj.event_ops; get_oid : int; .. > -> 
	?cond: (unit -> bool) -> 
	  ?mods: modifier list -> 
	    ?mask: modifier list -> 
	      Gdk.keysym -> 
		(unit -> unit) -> 
		  unit

(** It calls {!Okey.set} for each given key.*)
val set_list : 
    < connect : < destroy : callback: (unit -> unit) -> GtkSignal.id; .. >;
      event : GObj.event_ops; get_oid : int; .. > ->
	?cond: (unit -> bool) -> 
	  ?mods: modifier list -> 
	    ?mask: modifier list -> 
	      Gdk.keysym list -> 
		(unit -> unit) -> 
		  unit

(** Remove the handlers associated to the given widget.
   This is automatically done when a widget is destroyed but
   you can do it yourself. *)
val remove_widget : 
    < connect : < destroy : callback: (unit -> unit) -> GtkSignal.id; .. >;
      event : GObj.event_ops; get_oid : int; .. > ->
	unit ->
	  unit
