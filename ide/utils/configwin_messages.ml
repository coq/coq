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

(** Module containing the messages of Configwin.*)

let software = "Configwin";;
let version = "1.2";;

let html_config = "Configwin bindings configurator for html parameters"

let home =
  try Sys.getenv "HOME"
  with Not_found -> ""

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

