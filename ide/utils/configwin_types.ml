(***********************************************************************)
(*                          Configwin                                  *)
(*                                                                     *)
(*            Maxence Guesdon, projet Cristal, INRIA Rocquencourt      *)
(*                                                                     *)
(*  Copyright 2001 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

(** This module contains the types used in Configwin. *)

open Uoptions

(** A module to define key options, with the {!Uoptions} module. *)
module KeyOption = struct
  let name_to_keysym = 
    ("Button1", Configwin_keys.xk_Pointer_Button1) ::
    ("Button2", Configwin_keys.xk_Pointer_Button2) ::
    ("Button3", Configwin_keys.xk_Pointer_Button3) ::
    ("Button4", Configwin_keys.xk_Pointer_Button4) ::
    ("Button5", Configwin_keys.xk_Pointer_Button5) ::
    Configwin_keys.name_to_keysym
      
  let string_to_key s =
    let mask = ref [] in
    let key = try
      let pos = String.rindex s '-' in
      for i = 0 to pos - 1 do 
        let m = match s.[i] with
          'C' -> `CONTROL
        | 'S' -> `SHIFT
        | 'L' -> `LOCK 
        | 'M' -> `MOD1
        | 'A' -> `MOD1
        | '1' -> `MOD1
        | '2' -> `MOD2
        | '3' -> `MOD3
        | '4' -> `MOD4
        | '5' -> `MOD5
        | _ -> 
	    prerr_endline s;
	    raise Not_found
        in
        mask := m :: !mask
      done;
      String.sub s (pos+1) (String.length s - pos - 1)
    with _ -> 
      s
    in
    try
      !mask, List.assoc key name_to_keysym
    with
      e -> 
	prerr_endline s;
	raise e
      
  let key_to_string (m, k) =
    let s = List.assoc k Configwin_keys.keysym_to_name in
    match m with
      [] -> s
    | _ ->
        let rec iter m s =
          match m with
            [] -> s
          | c :: m ->
              iter m ((
                      match c with
			`CONTROL -> "C"
                      | `SHIFT -> "S"
                      | `LOCK -> "L"
                      | `MOD1 -> "A"
                      | `MOD2 -> "2"
                      | `MOD3 -> "3"
                      | `MOD4 -> "4"
                      | `MOD5 -> "5"
                      | _  -> raise Not_found
                     ) ^ s)
        in
        iter m ("-" ^ s)

  let modifiers_to_string m =
    let rec iter m s =
      match m with
          [] -> s
        | c :: m ->
            iter m ((
                      match c with
			  `CONTROL -> "<ctrl>"
			| `SHIFT -> "<shft>"
			| `LOCK -> "<lock>"
			| `MOD1 -> "<alt>"
			| `MOD2 -> "<mod2>"
			| `MOD3 -> "<mod3>"
			| `MOD4 -> "<mod4>"
			| `MOD5 -> "<mod5>"
			| _  -> raise Not_found
                    ) ^ s)
    in
    iter m ""
	  
  let value_to_key v =
    match v with
      StringValue s -> string_to_key s
    | _ -> 
	prerr_endline "value_to_key";
	raise Not_found
	  
  let key_to_value k =
    StringValue (key_to_string k)
      
  let (t : (Gdk.Tags.modifier list * int) option_class) = 
    define_option_class "Key" value_to_key key_to_value
end

(** This type represents a string or filename parameter. *)
type string_param = {
    string_label : string; (** the label of the parameter *)
    mutable string_value : string; (** the current value of the parameter *)
    string_editable : bool ; (** indicates if the value can be changed *)
    string_f_apply : (string -> unit) ; (** the function to call to apply the new value of the parameter *)
    string_help : string option ; (** optional help string *)
    string_expand : bool ; (** expand or not *)
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

type color_param = {
    color_label : string; (** the label of the parameter *)
    mutable color_value : string; (** the current value of the parameter *)
    color_editable : bool ; (** indicates if the value can be changed *)
    color_f_apply : (string -> unit) ; (** the function to call to apply the new value of the parameter *)
    color_help : string option ; (** optional help string *)
    color_expand : bool ; (** expand the entry widget or not *)
  } ;;

type date_param = {
    date_label : string ; (** the label of the parameter *)
    mutable date_value : int * int * int ; (** day, month, year *)
    date_editable : bool ; (** indicates if the value can be changed *)
    date_f_string : (int * int * int) -> string ;
      (** the function used to display the current value (day, month, year) *)
    date_f_apply : ((int * int * int) -> unit) ;
      (** the function to call to apply the new value (day, month, year) of the parameter *)
    date_help : string option ; (** optional help string *)
    date_expand : bool ; (** expand the entry widget or not *)
  } ;;

type font_param = {
    font_label : string ; (** the label of the parameter *)
    mutable font_value : string ; (** the font name *)
    font_editable : bool ; (** indicates if the value can be changed *)
    font_f_apply : (string -> unit) ;
      (** the function to call to apply the new value of the parameter *)
    font_help : string option ; (** optional help string *)
    font_expand : bool ; (** expand the entry widget or not *)
  } ;;


type hotkey_param = {
    hk_label : string ; (** the label of the parameter *)
    mutable hk_value : (Gdk.Tags.modifier list * int) ; 
             (** The value, as a list of modifiers and a key code *)
    hk_editable : bool ; (** indicates if the value can be changed *)
    hk_f_apply : ((Gdk.Tags.modifier list * int) -> unit) ;
             (** the function to call to apply the new value of the paramter *)
    hk_help : string option ; (** optional help string *)
    hk_expand : bool ; (** expand or not *)
  } 

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
    String_param of string_param
  | List_param of (unit -> <box: GObj.widget ; apply : unit>)
  | Filename_param of string_param
  | Bool_param of bool_param
  | Text_param of string_param
  | Combo_param of combo_param
  | Custom_param of custom_param
  | Color_param of color_param
  | Date_param of date_param
  | Font_param of font_param
  | Hotkey_param of hotkey_param
  | Modifiers_param of modifiers_param
  | Html_param of string_param
;;

(** This type represents the structure of the configuration window. *)
type configuration_structure =
  | Section of string * parameter_kind list (** label of the section, parameters *)
  | Section_list of string * configuration_structure list (** label of the section, list of the sub sections *)
;;

(** To indicate what button was pushed by the user when the window is closed. *)
type return_button =
    Return_apply (** The user clicked on Apply at least once before
	     closing the window with Cancel or the window manager. *)
  | Return_ok (** The user closed the window with the ok button. *)
  | Return_cancel (** The user closed the window with the cancel
		     button or the window manager but never clicked
		     on the apply button.*)

(** {2 Bindings in the html editor} *)

type html_binding = {
    mutable html_key :  (Gdk.Tags.modifier list * int) ;
    mutable html_begin : string ;
    mutable html_end : string ;
  } 

module Html_binding = struct
  let value_to_hb v =
    match v with
      List [StringValue hk ; StringValue debut; StringValue fin ]
    | SmallList [StringValue hk ; StringValue debut; StringValue fin ] ->
        { html_key = KeyOption.string_to_key hk ;
	  html_begin = debut ;
	  html_end = fin ;
        }
    | _ ->
        prerr_endline "Html_binding.value_to_hb";
        raise Not_found

  let hb_to_value hb =
    SmallList [ StringValue (KeyOption.key_to_string hb.html_key) ;
                StringValue hb.html_begin ;
                StringValue hb.html_end ;
	      ]	

  let (t : html_binding option_class) =
    define_option_class "html_binding" value_to_hb hb_to_value
end
