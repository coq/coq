(**************************************************************************)
(*                   Cameleon                                             *)
(*                                                                        *)
(*      Copyright (C) 2002 Institut National de Recherche en Informatique et   *)
(*      en Automatique. All rights reserved.                              *)
(*                                                                        *)
(*      This program is free software; you can redistribute it and/or modify  *)
(*      it under the terms of the GNU General Public License as published by  *)
(*      the Free Software Foundation; either version 2 of the License, or  *)
(*      any later version.                                                *)
(*                                                                        *)
(*      This program is distributed in the hope that it will be useful,   *)
(*      but WITHOUT ANY WARRANTY; without even the implied warranty of    *)
(*      MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the     *)
(*      GNU General Public License for more details.                      *)
(*                                                                        *)
(*      You should have received a copy of the GNU General Public License  *)
(*      along with this program; if not, write to the Free Software       *)
(*      Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA          *)
(*      02111-1307  USA                                                   *)
(*                                                                        *)
(*      Contact: Maxence.Guesdon@inria.fr                                *)
(**************************************************************************)

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
let modifiers = Configwin_ihm.modifiers
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
