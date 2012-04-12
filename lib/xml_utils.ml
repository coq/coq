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

open Printf
open Serialize

exception Not_element of xml
exception Not_pcdata of xml
exception No_attribute of string

let default_parser = Xml_parser.make()

let parse (p:Xml_parser.t) (source:Xml_parser.source) =
	(* local cast Xml.xml -> xml *)
	(Obj.magic Xml_parser.parse p source : xml)

let parse_in ch = parse default_parser (Xml_parser.SChannel ch)
let parse_string str = parse default_parser (Xml_parser.SString str)

let parse_file f = parse default_parser (Xml_parser.SFile f)

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

let tmp = Buffer.create 200

let buffer_pcdata text =
	let l = String.length text in
	for p = 0 to l-1 do 
		match text.[p] with
		| '>' -> Buffer.add_string tmp "&gt;"
		| '<' -> Buffer.add_string tmp "&lt;"
		| '&' ->
			if p < l-1 && text.[p+1] = '#' then
				Buffer.add_char tmp '&'
			else
				Buffer.add_string tmp "&amp;"
		| '\'' -> Buffer.add_string tmp "&apos;"
		| '"' -> Buffer.add_string tmp "&quot;"
		| c -> Buffer.add_char tmp c
	done

let print_pcdata chan text =
  let l = String.length text in
  for p = 0 to l-1 do 
    match text.[p] with
    | '>' -> Printf.fprintf chan "&gt;"
    | '<' -> Printf.fprintf chan "&lt;"
    | '&' ->
            if p < l-1 && text.[p+1] = '#' then
                    Printf.fprintf chan "&"
            else
                    Printf.fprintf chan "&amp;"
    | '\'' -> Printf.fprintf chan "&apos;"
    | '"' -> Printf.fprintf chan "&quot;"
    | c -> Printf.fprintf chan "%c" c
  done

let buffer_attr (n,v) =
	Buffer.add_char tmp ' ';
	Buffer.add_string tmp n;
	Buffer.add_string tmp "=\"";
	let l = String.length v in
	for p = 0 to l-1 do
		match v.[p] with
		| '\\' -> Buffer.add_string tmp "\\\\"
		| '"' -> Buffer.add_string tmp "\\\""
		| c -> Buffer.add_char tmp c
	done;
	Buffer.add_char tmp '"'

let rec print_attr chan (n, v) =
  Printf.fprintf chan " %s=\"" n;
  let l = String.length v in
  for p = 0 to l-1 do
          match v.[p] with
          | '\\' -> Printf.fprintf chan "\\\\"
          | '"' -> Printf.fprintf chan  "\\\""
          | c -> Printf.fprintf chan "%c" c
  done;
  Printf.fprintf chan "\""

let print_attrs chan l = List.iter (print_attr chan) l

let rec print_xml chan = function
| Element (tag, alist, []) ->
  Printf.fprintf chan "<%s%a/>" tag print_attrs alist;
| Element (tag, alist, l) ->
  Printf.fprintf chan "<%s%a>%a</%s>" tag print_attrs alist
  (fun chan -> List.iter (print_xml chan)) l tag
| PCData text ->
  print_pcdata chan text

let to_string x = 
	let pcdata = ref false in
	let rec loop = function
		| Element (tag,alist,[]) ->
			Buffer.add_char tmp '<';
			Buffer.add_string tmp tag;
			List.iter buffer_attr alist;
			Buffer.add_string tmp "/>";
			pcdata := false;
		| Element (tag,alist,l) ->
			Buffer.add_char tmp '<';
			Buffer.add_string tmp tag;
			List.iter buffer_attr alist;
			Buffer.add_char tmp '>';
			pcdata := false;
			List.iter loop l;
			Buffer.add_string tmp "</";
			Buffer.add_string tmp tag;
			Buffer.add_char tmp '>';
			pcdata := false;
		| PCData text ->
			if !pcdata then Buffer.add_char tmp ' ';
			buffer_pcdata text;
			pcdata := true;
	in
	Buffer.reset tmp;
	loop x;
	let s = Buffer.contents tmp in
	Buffer.reset tmp;
	s

let to_string_fmt x =
	let rec loop ?(newl=false) tab = function
		| Element (tag,alist,[]) ->
			Buffer.add_string tmp tab;
			Buffer.add_char tmp '<';
			Buffer.add_string tmp tag;
			List.iter buffer_attr alist;
			Buffer.add_string tmp "/>";
			if newl then Buffer.add_char tmp '\n';
		| Element (tag,alist,[PCData text]) ->
			Buffer.add_string tmp tab;
			Buffer.add_char tmp '<';
			Buffer.add_string tmp tag;
			List.iter buffer_attr alist;
			Buffer.add_string tmp ">";
			buffer_pcdata text;
			Buffer.add_string tmp "</";
			Buffer.add_string tmp tag;
			Buffer.add_char tmp '>';
			if newl then Buffer.add_char tmp '\n';
		| Element (tag,alist,l) ->
			Buffer.add_string tmp tab;
			Buffer.add_char tmp '<';
			Buffer.add_string tmp tag;
			List.iter buffer_attr alist;
			Buffer.add_string tmp ">\n";
			List.iter (loop ~newl:true (tab^"  ")) l;
			Buffer.add_string tmp tab;
			Buffer.add_string tmp "</";
			Buffer.add_string tmp tag;
			Buffer.add_char tmp '>';
			if newl then Buffer.add_char tmp '\n';
		| PCData text ->
			buffer_pcdata text;
			if newl then Buffer.add_char tmp '\n';
	in
	Buffer.reset tmp;
	loop "" x;
	let s = Buffer.contents tmp in
	Buffer.reset tmp;
	s
