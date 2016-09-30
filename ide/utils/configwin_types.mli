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

(** This module contains the types used in Configwin. *)

(** This type represents a string or filename parameter, or
   any other type, depending on the given conversion functions. *)
type 'a string_param = {
    string_label : string; (** the label of the parameter *)
    mutable string_value : 'a; (** the current value of the parameter *)
    string_editable : bool ; (** indicates if the value can be changed *)
    string_f_apply : ('a -> unit) ; (** the function to call to apply the new value of the parameter *)
    string_help : string option ; (** optional help string *)
    string_expand : bool ; (** expand or not *)
    string_to_string : 'a -> string ;
    string_of_string : string -> 'a ;
  } ;;

(** This type represents a boolean parameter. *)
type bool_param = {
    bool_label : string; (** the label of the parameter *)
    mutable bool_value : bool; (** the current value of the parameter *)
    bool_editable : bool ; (** indicates if the value can be changed *)
    bool_f_apply : (bool -> unit) ; (** the function to call to apply the new value of the parameter *)
    bool_help : string option ; (** optional help string *)
  } ;;

(** This type represents a parameter whose value is a list of ['a]. *)
type 'a list_param = {
    list_label : string; (** the label of the parameter *)
    mutable list_value : 'a list; (** the current value of the parameter *)
    list_titles : string list option; (** the titles of columns, if they must be displayed *)
    list_f_edit : ('a -> 'a) option; (** optional edition function *)
    list_eq : ('a -> 'a -> bool) ; (** the comparison function used to get list without doubles *)
    list_strings : ('a -> string list); (** the function to get a string list from a ['a]. *)
    list_color : ('a -> string option) ; (** a function to get the optional color of an element *)
    list_editable : bool ; (** indicates if the value can be changed *)
    list_f_add : unit -> 'a list ; (** the function to call to add list *)
    list_f_apply : ('a list -> unit) ; (** the function to call to apply the new value of the parameter *)
    list_help : string option ; (** optional help string *)
  } ;;

type combo_param = {
    combo_label : string ;
    mutable combo_value : string ;
    combo_choices : string list ;
    combo_editable : bool ;
    combo_blank_allowed : bool ;
    combo_new_allowed : bool ;
    combo_f_apply : (string -> unit);
    combo_help : string option ; (** optional help string *)
    combo_expand : bool ; (** expand the entry widget or not *)
  } ;;

type custom_param = {
    custom_box : GPack.box ;
    custom_f_apply : (unit -> unit) ;
    custom_expand : bool ;
    custom_framed : string option ; (** optional label for an optional frame *)
  } ;;

type modifiers_param = {
    md_label : string ; (** the label of the parameter *)
    mutable md_value : Gdk.Tags.modifier list ;
             (** The value, as a list of modifiers and a key code *)
    md_editable : bool ; (** indicates if the value can be changed *)
    md_f_apply : Gdk.Tags.modifier list -> unit ;
             (** the function to call to apply the new value of the paramter *)
    md_help : string option ; (** optional help string *)
    md_expand : bool ; (** expand or not *)
    md_allow : Gdk.Tags.modifier list
  }


(** This type represents the different kinds of parameters. *)
type parameter_kind =
    String_param of string string_param
  | List_param of (GData.tooltips -> <box: GObj.widget ; apply : unit>)
  | Bool_param of bool_param
  | Text_param of string string_param
  | Combo_param of combo_param
  | Custom_param of custom_param
  | Modifiers_param of modifiers_param
;;

(** This type represents the structure of the configuration window. *)
type configuration_structure =
  | Section of string * GtkStock.id option * parameter_kind list (** label of the section, icon, parameters *)
  | Section_list of string * GtkStock.id option * configuration_structure list (** label of the section, list of the sub sections *)
;;

(** To indicate what button was pushed by the user when the window is closed. *)
type return_button =
    Return_apply (** The user clicked on Apply at least once before
	     closing the window with Cancel or the window manager. *)
  | Return_ok (** The user closed the window with the ok button. *)
  | Return_cancel (** The user closed the window with the cancel
		     button or the window manager but never clicked
		     on the apply button.*)
