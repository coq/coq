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

(** The HTML editor bindings configurator. *)

module C = Configwin_ihm
open Configwin_types
open Uoptions

let simple_get = C.simple_edit 
    ~with_apply: false ~apply: (fun () -> ())

let params_hb hb =
  let p_key = C.hotkey 
      ~f: (fun k -> hb.html_key <- k) Configwin_messages.mKey
      hb.html_key
  in
  let p_begin = C.string
      ~f: (fun s -> hb.html_begin <- s)
      Configwin_messages.html_begin
      hb.html_begin
  in
  let p_end = C.string
      ~f: (fun s -> hb.html_end <- s)
      Configwin_messages.html_end
      hb.html_end
  in
  [ p_key ; p_begin ; p_end ]

let edit_hb hb =
  ignore (simple_get Configwin_messages.mEdit (params_hb hb));
  hb

let add () =
  let hb = { html_key = KeyOption.string_to_key "C-a" ;
	     html_begin = "" ;
	     html_end = "" ;
	   } 
  in
  match simple_get Configwin_messages.mAdd (params_hb hb) with
    Return_ok -> [hb]
  | _ -> []

let main () =
  ignore (GMain.Main.init ());
  let (ini, bindings) = C.html_config_file_and_option () in
  let param = C.list
      ~f: (fun l -> bindings =:= l ; Uoptions.save_with_help ini)
      ~eq: (fun hb1 hb2 -> hb1.html_key = hb2.html_key)
      ~edit: edit_hb
      ~add: add
      ~titles: [ Configwin_messages.mKey ; Configwin_messages.html_begin ;
		 Configwin_messages.html_end ]
      Configwin_messages.shortcuts
      (fun hb -> [ KeyOption.key_to_string hb.html_key ;
		   hb.html_begin ; hb.html_end ])
      !!bindings
  in
  ignore (simple_get ~width: 300 ~height: 400 
	    Configwin_messages.html_config [param])

let _ = main ()
