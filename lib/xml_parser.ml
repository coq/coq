(*
 * Xml Light, an small Xml parser/printer with DTD support.
 * Copyright (C) 2003 Nicolas Cannasse (ncannasse@motion-twin.com)
 * Copyright (C) 2003 Jacques Garrigue
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

type xml = 
        | Element of (string * (string * string) list * xml list)
        | PCData of string

type error_pos = {
        eline : int;
        eline_start : int;
        emin : int;
        emax : int;
}

type error_msg =
        | UnterminatedComment
        | UnterminatedString
        | UnterminatedEntity
        | IdentExpected
        | CloseExpected
        | NodeExpected
        | AttributeNameExpected
        | AttributeValueExpected
        | EndOfTagExpected of string
        | EOFExpected

type error = error_msg * error_pos

exception Error of error

exception File_not_found of string

type t = {
	mutable check_eof : bool;
	mutable concat_pcdata : bool;
}

type source = 
	| SFile of string
	| SChannel of in_channel
	| SString of string
	| SLexbuf of Lexing.lexbuf

type state = {
	source : Lexing.lexbuf;
	stack : Xml_lexer.token Stack.t;
	xparser : t;
}

exception Internal_error of error_msg
exception NoMoreData

let xml_error = ref (fun _ -> assert false)
let file_not_found = ref (fun _ -> assert false)

let is_blank s =
  let len = String.length s in
  let break = ref true in
  let i = ref 0 in
  while !break && !i < len do
    let c = s.[!i] in
    (* no '\r' because we replaced them in the lexer *)
    if c = ' ' || c = '\n' || c = '\t' then incr i
    else break := false
  done;
  !i = len

let _raises e f =
	xml_error := e;
	file_not_found := f

let make () =
	{
		check_eof = true;
		concat_pcdata = true;
	}

let check_eof p v = p.check_eof <- v
let concat_pcdata p v = p.concat_pcdata <- v

let pop s =
	try
		Stack.pop s.stack
	with
		Stack.Empty ->
			Xml_lexer.token s.source

let push t s =
	Stack.push t s.stack

let canonicalize l =
  let has_elt = List.exists (function Element _ -> true | _ -> false) l in
  if has_elt then List.filter (function PCData s -> not (is_blank s) | _ -> true) l
  else l

let rec read_node s =
	match pop s with
	| Xml_lexer.PCData s -> PCData s
	| Xml_lexer.Tag (tag, attr, true) -> Element (tag, attr, [])
	| Xml_lexer.Tag (tag, attr, false) ->
          let elements = read_elems ~tag s in
          Element (tag, attr, canonicalize elements)
	| t ->
		push t s;
		raise NoMoreData
and
	read_elems ?tag s =
		let elems = ref [] in
		(try
                  while true do
                    let node = read_node s in
                    match node, !elems with
                    | PCData c , (PCData c2) :: q ->
                      elems := PCData (c2 ^ c) :: q
                    | _, l ->
                      elems := node :: l
                  done
		with
			NoMoreData -> ());
		match pop s with
		| Xml_lexer.Endtag s when Some s = tag -> List.rev !elems
		| Xml_lexer.Eof when tag = None -> List.rev !elems
		| t ->
			match tag with
			| None -> raise (Internal_error EOFExpected)
			| Some s -> raise (Internal_error (EndOfTagExpected s))

let read_xml s = read_node s

let convert = function
	| Xml_lexer.EUnterminatedComment -> UnterminatedComment
	| Xml_lexer.EUnterminatedString -> UnterminatedString
	| Xml_lexer.EIdentExpected -> IdentExpected
	| Xml_lexer.ECloseExpected -> CloseExpected
	| Xml_lexer.ENodeExpected -> NodeExpected
	| Xml_lexer.EAttributeNameExpected -> AttributeNameExpected
	| Xml_lexer.EAttributeValueExpected -> AttributeValueExpected
	| Xml_lexer.EUnterminatedEntity -> 	UnterminatedEntity

let do_parse xparser source =
	try
		Xml_lexer.init source;
		let s = { source = source; xparser = xparser; stack = Stack.create(); } in
		let x = read_xml s in
		if xparser.check_eof && pop s <> Xml_lexer.Eof then raise (Internal_error EOFExpected);
		Xml_lexer.close source;
		x
	with
		| NoMoreData ->
			Xml_lexer.close source;
			raise (!xml_error NodeExpected source)
		| Internal_error e ->
			Xml_lexer.close source;
			raise (!xml_error e source)
		| Xml_lexer.Error e ->
			Xml_lexer.close source;
			raise (!xml_error (convert e) source)

let parse p = function
	| SChannel ch -> do_parse p (Lexing.from_channel ch)
	| SString str -> do_parse p (Lexing.from_string str)
	| SLexbuf lex -> do_parse p lex
	| SFile fname ->
		let ch = (try open_in fname with Sys_error _ -> raise (!file_not_found fname)) in
		try
			let x = do_parse p (Lexing.from_channel ch) in
			close_in ch;
			x
		with
			e ->
				close_in ch;
				raise e


let error_msg = function
        | UnterminatedComment -> "Unterminated comment"
        | UnterminatedString -> "Unterminated string"
        | UnterminatedEntity -> "Unterminated entity"
        | IdentExpected -> "Ident expected"
        | CloseExpected -> "Element close expected"
        | NodeExpected -> "Xml node expected"
        | AttributeNameExpected -> "Attribute name expected"
        | AttributeValueExpected -> "Attribute value expected"
        | EndOfTagExpected tag -> sprintf "End of tag expected : '%s'" tag
        | EOFExpected -> "End of file expected"

let error (msg,pos) =
        if pos.emin = pos.emax then
                sprintf "%s line %d character %d" (error_msg msg) pos.eline (pos.emin - pos.eline_start)
        else
                sprintf "%s line %d characters %d-%d" (error_msg msg) pos.eline (pos.emin - pos.eline_start) (pos.emax - pos.eline_start)
        
let line e = e.eline

let range e = 
        e.emin - e.eline_start , e.emax - e.eline_start

let abs_range e =
        e.emin , e.emax

let pos source =
        let line, lstart, min, max = Xml_lexer.pos source in
        {
                eline = line;
                eline_start = lstart;
                emin = min;
                emax = max;
        }
