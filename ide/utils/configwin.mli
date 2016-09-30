(*********************************************************************************)
(*                Cameleon                                                       *)
(*                                                                               *)
(*    Copyright (C) 2005 Institut National de Recherche en Informatique et       *)
(*    en Automatique. All rights reserved.                                       *)
(*                                                                               *)
(*    This program is free software; you can redistribute it and/or modify       *)
(*    it under the terms of the GNU Library General Public License as            *)
(*    published by the Free Software Foundation; either version 2 of the         *)
(*    License, or  any later version.                                            *)
(*                                                                               *)
(*    This program is distributed in the hope that it will be useful,            *)
(*    but WITHOUT ANY WARRANTY; without even the implied warranty of             *)
(*    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the              *)
(*    GNU Library General Public License for more details.                       *)
(*                                                                               *)
(*    You should have received a copy of the GNU Library General Public          *)
(*    License along with this program; if not, write to the Free Software        *)
(*    Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA                   *)
(*    02111-1307  USA                                                            *)
(*                                                                               *)
(*    Contact: Maxence.Guesdon@inria.fr                                          *)
(*                                                                               *)
(*********************************************************************************)

(** This module is the interface of the Configwin library. *)

(** {2 Types} *)

(** This type represents the different kinds of parameters. *)
type parameter_kind;;

(** This type represents the structure of the configuration window. *)
type configuration_structure =
  | Section of string * GtkStock.id option * parameter_kind list
       (** label of the section, icon, parameters *)
  | Section_list of string * GtkStock.id option * configuration_structure list
       (** label of the section, icon, list of the sub sections *)
;;

(** To indicate what button pushed the user when the window is closed. *)
type return_button =
    Return_apply
      (** The user clicked on Apply at least once before
	 closing the window with Cancel or the window manager. *)
  | Return_ok
      (** The user closed the window with the ok button. *)
  | Return_cancel
      (** The user closed the window with the cancel
	 button or the window manager but never clicked
	 on the apply button.*)

(** {2 Functions to create parameters} *)

(** [string label value] creates a string parameter.
   @param editable indicate if the value is editable (default is [true]).
   @param expand indicate if the entry widget must expand or not (default is [true]).
   @param help an optional help message.
   @param f the function called to apply the value (default function does nothing).
*)
val string : ?editable: bool -> ?expand: bool -> ?help: string ->
  ?f: (string -> unit) -> string -> string -> parameter_kind

(** [bool label value] creates a boolean parameter.
   @param editable indicate if the value is editable (default is [true]).
   @param help an optional help message.
   @param f the function called to apply the value (default function does nothing).
*)
val bool : ?editable: bool -> ?help: string ->
  ?f: (bool -> unit) -> string -> bool -> parameter_kind

(** [strings label value] creates a string list parameter.
   @param editable indicate if the value is editable (default is [true]).
   @param help an optional help message.
   @param f the function called to apply the value (default function does nothing).
   @param add the function returning a list of strings when the user wants to add strings
   (default returns an empty list).
   @param eq the comparison function, used not to have doubles in list. Default
   is [Pervasives.(=)]. If you want to allow doubles in the list, give a function
   always returning false.
*)
val strings : ?editable: bool -> ?help: string ->
  ?f: (string list -> unit) ->
    ?eq: (string -> string -> bool) ->
      ?add: (unit -> string list) ->
	string -> string list -> parameter_kind

(** [list label f_strings value] creates a list parameter.
   [f_strings] is a function taking a value and returning a list
   of strings to display it. The list length should be the same for
   any value, and the same as the titles list length. The [value]
   is the initial list.
   @param editable indicate if the value is editable (default is [true]).
   @param help an optional help message.
   @param f the function called to apply the value (default function does nothing).
   @param eq the comparison function, used not to have doubles in list. Default
   is [Pervasives.(=)]. If you want to allow doubles in the list, give a function
   always returning false.
   @param edit an optional function to use to edit an element of the list.
     The function returns an element, no matter if element was changed or not.
     When this function is given, a "Edit" button appears next to the list.
   @param add the function returning a list of values when the user wants to add values
   (default returns an empty list).
   @param titles an optional list of titles for the list. If the [f_strings]
   function returns a list with more than one element, then you must give
   a list of titles.
   @param color an optional function returning the optional color for a given element.
   This color is used to display the element in the list. The default function returns
   no color for any element.
*)
val list : ?editable: bool -> ?help: string ->
  ?f: ('a list -> unit) ->
    ?eq: ('a -> 'a -> bool) ->
      ?edit: ('a -> 'a) ->
	?add: (unit -> 'a list) ->
	  ?titles: string list ->
	    ?color: ('a -> string option) ->
	      string ->
		('a -> string list) ->
		  'a list ->
		    parameter_kind

(** [combo label choices value] creates a combo parameter.
   @param editable indicate if the value is editable (default is [true]).
   @param expand indicate if the entry widget must expand or not (default is [true]).
   @param help an optional help message.
   @param f the function called to apply the value (default function does nothing).
   @param new_allowed indicate if a entry not in the list of choices is accepted
   (default is [false]).
   @param blank_allowed indicate if the empty selection [""] is accepted
   (default is [false]).
*)
val combo : ?editable: bool -> ?expand: bool -> ?help: string ->
  ?f: (string -> unit) ->
    ?new_allowed: bool -> ?blank_allowed: bool ->
      string -> string list -> string -> parameter_kind

val modifiers : ?editable: bool -> ?expand: bool -> ?help: string ->
  ?allow:(Gdk.Tags.modifier list) ->
  ?f: (Gdk.Tags.modifier list -> unit) ->
    string -> Gdk.Tags.modifier list -> parameter_kind

(** [custom box f expand] creates a custom parameter, with
   the given [box], the [f] function is called when the user
   wants to apply his changes, and [expand] indicates if the box
   must expand in its father.
   @param label if a value is specified, a the box is packed into a frame.
*)
val custom : ?label: string -> GPack.box -> (unit -> unit) -> bool -> parameter_kind

(** {2 Functions creating configuration windows and boxes} *)

(** This function takes a configuration structure and creates a window
   to configure the various parameters.
   @param apply this function is called when the apply button is clicked, after
   giving new values to parameters.
*)
val edit :
  ?apply: (unit -> unit) ->
  string ->
  ?width:int ->
  ?height:int ->
  configuration_structure list ->
  return_button
