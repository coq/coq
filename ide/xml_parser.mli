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

(** Xml Light Parser

 While basic parsing functions can be used in the {!Xml} module, this module
 is providing a way to create, configure and run an Xml parser.

*)


(** An Xml node is either
        [Element (tag-name, attributes, children)] or [PCData text] *)
type xml = Xml_datatype.xml

(** Abstract type for an Xml parser. *)
type t

(** {6:exc Xml Exceptions} *)

(** Several exceptions can be raised when parsing an Xml document : {ul
        {li {!Xml.Error} is raised when an xml parsing error occurs. the
                {!Xml.error_msg} tells you which error occurred during parsing
                and the {!Xml.error_pos} can be used to retrieve the document
                location where the error occurred at.}
        {li {!Xml.File_not_found} is raised when an error occurred while
                opening a file with the {!Xml.parse_file} function.}
        }
 *)

type error_pos

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

(** Get a full error message from an Xml error. *)
val error : error -> string

(** Get the Xml error message as a string. *)
val error_msg : error_msg -> string

(** Get the line the error occurred at. *)
val line : error_pos -> int

(** Get the relative character range (in current line) the error occurred at.*)
val range : error_pos -> int * int

(** Get the absolute character range the error occurred at. *)
val abs_range : error_pos -> int * int

val pos : Lexing.lexbuf -> error_pos

(** Several kind of resources can contain Xml documents. *)
type source =
| SChannel of in_channel
| SString of string
| SLexbuf of Lexing.lexbuf

(** This function returns a new parser with default options. *)
val make : source -> t

(** When a Xml document is parsed, the parser may check that the end of the
 document is reached, so for example parsing ["<A/><B/>"] will fail instead
 of returning only the A element. You can turn on this check by setting
 [check_eof] to [true] {i (by default, check_eof is false, unlike
 in the original Xmllight)}. *)
val check_eof : t -> bool -> unit

(** Once the parser is configured, you can run the parser on a any kind
    of xml document source to parse its contents into an Xml data structure.

    When [do_not_canonicalize] is set, the XML document is given as
    is, without trying to remove blank PCDATA elements. *)
val parse : ?do_not_canonicalize:bool -> t -> xml
