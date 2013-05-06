(*
 * Xml Light, an small Xml parser/printer with DTD support.
 * Copyright (C) 2003 Nicolas Cannasse (ncannasse@motion-twin.com)
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 *)

open Serialize

exception Not_element of xml
exception Not_pcdata of xml
exception No_attribute of string

let tag = function
	| Element (tag,_,_) -> tag
	| x -> raise (Not_element x)

let pcdata = function 
	| PCData text -> text
	| x -> raise (Not_pcdata x)

let attribs = function 
	| Element (_,attr,_) -> attr
	| x -> raise (Not_element x)

let attrib x att =
	match x with
	| Element (_,attr,_) ->
		(try
			let att = String.lowercase att in
			snd (List.find (fun (n,_) -> String.lowercase n = att) attr)
		with
			Not_found ->
				raise (No_attribute att))
	| x ->
		raise (Not_element x)

let children = function
	| Element (_,_,clist) -> clist
	| x -> raise (Not_element x)

(*let enum = function
	| Element (_,_,clist) -> List.to_enum clist
	| x -> raise (Not_element x)
*)

let iter f = function
	| Element (_,_,clist) -> List.iter f clist
	| x -> raise (Not_element x)

let map f = function
	| Element (_,_,clist) -> List.map f clist
	| x -> raise (Not_element x)

let fold f v = function
	| Element (_,_,clist) -> List.fold_left f v clist
	| x -> raise (Not_element x)

