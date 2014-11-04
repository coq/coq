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
open Xml_datatype

type xml = Xml_datatype.xml

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
  | Empty

type error = error_msg * error_pos

exception Error of error

exception File_not_found of string

type t = {
  mutable check_eof : bool;
  mutable concat_pcdata : bool;
  source : Lexing.lexbuf;
  stack : Xml_lexer.token Stack.t;
}

type source =
  | SChannel of in_channel
  | SString of string
  | SLexbuf of Lexing.lexbuf

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

let make source =
  let source = match source with
    | SChannel chan -> Lexing.from_channel chan
    | SString s -> Lexing.from_string s
    | SLexbuf lexbuf -> lexbuf
  in
  let () = Xml_lexer.init source in
  {
    check_eof = false;
    concat_pcdata = true;
    source = source;
    stack = Stack.create ();
  }

let check_eof p v = p.check_eof <- v

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

let rec read_xml do_not_canonicalize s =
  let rec read_node s =
    match pop s with
      | Xml_lexer.PCData s -> PCData s
      | Xml_lexer.Tag (tag, attr, true) -> Element (tag, attr, [])
      | Xml_lexer.Tag (tag, attr, false) ->
        let elements = read_elems tag s in
        let elements =
          if do_not_canonicalize then elements else canonicalize elements
        in
        Element (tag, attr, elements)
      | t ->
        push t s;
        raise NoMoreData

  and read_elems tag s =
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
      | Xml_lexer.Endtag s when s = tag -> List.rev !elems
      | t -> raise (Internal_error (EndOfTagExpected tag))
  in
  match read_node s with
    | (Element _) as node ->
      node
    | PCData c ->
      if is_blank c then
        read_xml do_not_canonicalize s
      else
        raise (Xml_lexer.Error Xml_lexer.ENodeExpected)

let convert = function
  | Xml_lexer.EUnterminatedComment -> UnterminatedComment
  | Xml_lexer.EUnterminatedString -> UnterminatedString
  | Xml_lexer.EIdentExpected -> IdentExpected
  | Xml_lexer.ECloseExpected -> CloseExpected
  | Xml_lexer.ENodeExpected -> NodeExpected
  | Xml_lexer.EAttributeNameExpected -> AttributeNameExpected
  | Xml_lexer.EAttributeValueExpected -> AttributeValueExpected
  | Xml_lexer.EUnterminatedEntity ->      UnterminatedEntity

let error_of_exn xparser = function
  | NoMoreData when pop xparser = Xml_lexer.Eof -> Empty
  | NoMoreData -> NodeExpected
  | Internal_error e -> e
  | Xml_lexer.Error e -> convert e
  | e ->
    (*let e = Errors.push e in: We do not record backtrace here. *)
    raise e

let do_parse do_not_canonicalize xparser =
  try
    Xml_lexer.init xparser.source;
    let x = read_xml do_not_canonicalize xparser in
    if xparser.check_eof && pop xparser <> Xml_lexer.Eof then raise (Internal_error EOFExpected);
    Xml_lexer.close ();
    x
  with any ->
    Xml_lexer.close ();
    raise (!xml_error (error_of_exn xparser any) xparser.source)

let parse ?(do_not_canonicalize=false) p =
  do_parse do_not_canonicalize p

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
  | Empty -> "Empty"

let error (msg,pos) =
  if pos.emin = pos.emax then
    sprintf "%s line %d character %d" (error_msg msg) pos.eline
      (pos.emin - pos.eline_start)
  else
    sprintf "%s line %d characters %d-%d" (error_msg msg) pos.eline
      (pos.emin - pos.eline_start) (pos.emax - pos.eline_start)

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

let () = _raises (fun x p ->
        (* local cast : Xml.error_msg -> error_msg *)
  Error (x, pos p))
  (fun f -> File_not_found f)
