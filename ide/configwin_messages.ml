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

(** Module containing the messages of Configwin.*)

let software = "Configwin";;
let version = "1.2";;

let html_config = "Configwin bindings configurator for html parameters"

let home = Option.default "" (Glib.get_home_dir ())

let mCapture = "Capture";;
let mType_key = "Type key" ;;
let mAdd = "Add";;
let mRemove = "Remove";;
let mUp = "Up";;
let mEdit = "Edit";;
let mOk = "Ok";;
let mCancel = "Cancel";;
let mApply = "Apply";;
let mValue = "Value"
let mKey = "Key"

let shortcuts = "Shortcuts"
let html_end = "End with"
let html_begin = "Begin with"

