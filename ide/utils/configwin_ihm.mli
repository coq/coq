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

open Configwin_types

val string : ?editable: bool -> ?expand: bool -> ?help: string ->
  ?f: (string -> unit) -> string -> string -> parameter_kind
val bool : ?editable: bool -> ?help: string ->
  ?f: (bool -> unit) -> string -> bool -> parameter_kind
val strings : ?editable: bool -> ?help: string ->
  ?f: (string list -> unit) ->
    ?eq: (string -> string -> bool) ->
      ?add: (unit -> string list) ->
        string -> string list -> parameter_kind
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
val combo : ?editable: bool -> ?expand: bool -> ?help: string ->
  ?f: (string -> unit) ->
    ?new_allowed: bool -> ?blank_allowed: bool ->
      string -> string list -> string -> parameter_kind

val modifiers : ?editable: bool -> ?expand: bool -> ?help: string ->
  ?allow:(Gdk.Tags.modifier list) ->
  ?f: (Gdk.Tags.modifier list -> unit) ->
    string -> Gdk.Tags.modifier list -> parameter_kind
val custom : ?label: string -> GPack.box -> (unit -> unit) -> bool -> parameter_kind

val edit :
  ?with_apply:bool ->
  ?apply:(unit -> unit) ->
  string ->
  ?width:int ->
  ?height:int ->
  configuration_structure list ->
  return_button
