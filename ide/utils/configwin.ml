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

type parameter_kind = Configwin_types.parameter_kind

type configuration_structure =
    Configwin_types.configuration_structure =
    Section of string * parameter_kind list
  | Section_list of string * configuration_structure list

type return_button =
    Configwin_types.return_button =
    Return_apply
  | Return_ok
  | Return_cancel

module KeyOption = Configwin_types.KeyOption

let string = Configwin_ihm.string
let text = Configwin_ihm.text
let strings = Configwin_ihm.strings
let list = Configwin_ihm.list
let bool = Configwin_ihm.bool
let filename = Configwin_ihm.filename
let filenames = Configwin_ihm.filenames
let color = Configwin_ihm.color
let font = Configwin_ihm.font
let combo = Configwin_ihm.combo
let custom = Configwin_ihm.custom
let date = Configwin_ihm.date
let hotkey = Configwin_ihm.hotkey
let html = Configwin_ihm.html

let edit 
    ?(apply=(fun () -> ()))
    title ?(width=400) ?(height=400) 
    conf_struct_list = 
  Configwin_ihm.edit ~with_apply: true ~apply title ~width ~height conf_struct_list

let get = Configwin_ihm.edit ~with_apply: false ~apply: (fun () -> ())

let simple_edit 
    ?(apply=(fun () -> ()))
    title ?width ?height 
    param_list = Configwin_ihm.simple_edit ~with_apply: true ~apply title ?width ?height param_list

let simple_get = Configwin_ihm.simple_edit 
    ~with_apply: false ~apply: (fun () -> ())

let box = Configwin_ihm.box

let tabbed_box = Configwin_ihm.tabbed_box
