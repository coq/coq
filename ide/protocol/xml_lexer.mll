{(*
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

open Lexing

type error =
        | EUnterminatedComment
        | EUnterminatedString
        | EIdentExpected
        | ECloseExpected
        | ENodeExpected
        | EAttributeNameExpected
        | EAttributeValueExpected
        | EUnterminatedEntity

exception Error of error

type pos = int * int * int * int

type token =
        | Tag of string * (string * string) list * bool
        | PCData of string
        | Endtag of string
        | Eof

let last_pos = ref 0
and current_line = ref 0
and current_line_start = ref 0

let tmp = Buffer.create 200

let idents = Hashtbl.create 0

let _ = begin
        Hashtbl.add idents "nbsp;" " ";
        Hashtbl.add idents "gt;" ">";
        Hashtbl.add idents "lt;" "<";
        Hashtbl.add idents "amp;" "&";
        Hashtbl.add idents "apos;" "'";
        Hashtbl.add idents "quot;" "\"";
end

let init lexbuf =
        current_line := 1;
        current_line_start := lexeme_start lexbuf;
        last_pos := !current_line_start

let close lexbuf =
        Buffer.reset tmp

let pos lexbuf =
        !current_line , !current_line_start ,
        !last_pos ,
        lexeme_start lexbuf

let restore (cl,cls,lp,_) =
        current_line := cl;
        current_line_start := cls;
        last_pos := lp

let newline lexbuf =
        incr current_line;
        last_pos := lexeme_end lexbuf;
        current_line_start := !last_pos

let error lexbuf e =
        last_pos := lexeme_start lexbuf;
        raise (Error e)

[@@@ocaml.warning "-3"]       (* String.lowercase_ascii since 4.03.0 GPR#124 *)
let lowercase = String.lowercase
[@@@ocaml.warning "+3"]
}

let newline = ['\n']
let break = ['\r']
let space = [' ' '\t']
let identchar =  ['A'-'Z' 'a'-'z' '_' '0'-'9' ':' '-' '.']
let ident = ['A'-'Z' 'a'-'z' '_' ':'] identchar*
let entitychar = ['A'-'Z' 'a'-'z']
let pcchar = [^ '\r' '\n' '<' '>' '&']

rule token = parse
        | newline | (newline break) | break
                {
                        newline lexbuf;
                        PCData "\n"
                }
        | "<!--"
                {
                        last_pos := lexeme_start lexbuf;
                        comment lexbuf;
                        token lexbuf
                }
        | "<?"
                {
                        last_pos := lexeme_start lexbuf;
                        header lexbuf;
                        token lexbuf;
                }
        | '<' space* '/' space*
                {
                        last_pos := lexeme_start lexbuf;
                        let tag = ident_name lexbuf in
                        ignore_spaces lexbuf;
                        close_tag lexbuf;
                        Endtag tag
                }
        | '<' space*
                {
                        last_pos := lexeme_start lexbuf;
                        let tag = ident_name lexbuf in
                        ignore_spaces lexbuf;
                        let attribs, closed = attributes lexbuf in
                        Tag(tag, attribs, closed)
                }
        | "&#"
                {
                        last_pos := lexeme_start lexbuf;
                        Buffer.reset tmp;
                        Buffer.add_string tmp (lexeme lexbuf);
                        PCData (pcdata lexbuf)
                }
        | '&'
                {
                        last_pos := lexeme_start lexbuf;
                        Buffer.reset tmp;
                        Buffer.add_string tmp (entity lexbuf);
                        PCData (pcdata lexbuf)
                }
        | pcchar+
                {
                        last_pos := lexeme_start lexbuf;
                        Buffer.reset tmp;
                        Buffer.add_string tmp (lexeme lexbuf);
                        PCData (pcdata lexbuf)
                }
        | eof { Eof }
        | _
                { error lexbuf ENodeExpected }

and ignore_spaces = parse
        | newline | (newline break) | break
                {
                        newline lexbuf;
                        ignore_spaces lexbuf
                }
        | space +
                { ignore_spaces lexbuf }
        | ""
                { () }

and comment = parse
        | newline | (newline break) | break
                {
                        newline lexbuf;
                        comment lexbuf
                }
        | "-->"
                { () }
        | eof
                { raise (Error EUnterminatedComment) }
        | _
                { comment lexbuf }

and header = parse
        | newline | (newline break) | break
                {
                        newline lexbuf;
                        header lexbuf
                }
        | "?>"
                { () }
        | eof
                { error lexbuf ECloseExpected }
        | _
                { header lexbuf }

and pcdata = parse
        | newline | (newline break) | break
                {
                        Buffer.add_char tmp '\n';
                        newline lexbuf;
                        pcdata lexbuf
                }
        | pcchar+
                {
                        Buffer.add_string tmp (lexeme lexbuf);
                        pcdata lexbuf
                }
        | "&#"
                {
                        Buffer.add_string tmp (lexeme lexbuf);
                        pcdata lexbuf;
                }
        | '&'
                {
                        Buffer.add_string tmp (entity lexbuf);
                        pcdata lexbuf
                }
        | ""
                { Buffer.contents tmp }

and entity = parse
        | entitychar+ ';'
                {
                        let ident = lexeme lexbuf in
                        try
                                Hashtbl.find idents (lowercase ident)
                        with
                                Not_found -> "&" ^ ident
                }
        | _ | eof
                { raise (Error EUnterminatedEntity) }

and ident_name = parse
        | ident
                { lexeme lexbuf }
        | _ | eof
                { error lexbuf EIdentExpected }

and close_tag = parse
        | '>'
                { () }
        | _ | eof
                { error lexbuf ECloseExpected }

and attributes = parse
        | '>'
                { [], false }
        | "/>"
                { [], true }
        | "" (* do not read a char ! *)
                {
                        let key = attribute lexbuf in
                        let data = attribute_data lexbuf in
                        ignore_spaces lexbuf;
                        let others, closed = attributes lexbuf in
                        (key, data) :: others, closed
                }

and attribute = parse
        | ident
                { lexeme lexbuf }
        | _ | eof
                { error lexbuf EAttributeNameExpected }

and attribute_data = parse
        | space* '=' space* '"'
                {
                        Buffer.reset tmp;
                        last_pos := lexeme_end lexbuf;
                        dq_string lexbuf
                }
        | space* '=' space* '\''
                {
                        Buffer.reset tmp;
                        last_pos := lexeme_end lexbuf;
                        q_string lexbuf
                }
        | _ | eof
                { error lexbuf EAttributeValueExpected }

and dq_string = parse
        | '"'
                { Buffer.contents tmp }
        | '\\' [ '"' '\\' ]
                {
                        Buffer.add_char tmp (lexeme_char lexbuf 1);
                        dq_string lexbuf
                }
        | '&'
                {
                        Buffer.add_string tmp (entity lexbuf);
                        dq_string lexbuf
                }
        | eof
                { raise (Error EUnterminatedString) }
        | _
                {
                        Buffer.add_char tmp (lexeme_char lexbuf 0);
                        dq_string lexbuf
                }

and q_string = parse
        | '\''
                { Buffer.contents tmp }
        | '\\' [ '\'' '\\' ]
                {
                        Buffer.add_char tmp (lexeme_char lexbuf 1);
                        q_string lexbuf
                }
        | '&'
                {
                        Buffer.add_string tmp (entity lexbuf);
                        q_string lexbuf
                }
        | eof
                { raise (Error EUnterminatedString) }
        | _
                {
                        Buffer.add_char tmp (lexeme_char lexbuf 0);
                        q_string lexbuf
                }
