(******************************************************************************)
(*                                                                            *)
(*                               PROJECT HELM                                 *)
(*                                                                            *)
(*                     A module to print Coq objects in XML                   *)
(*                                                                            *)
(*                Claudio Sacerdoti Coen <sacerdot@cs.unibo.it>               *)
(*                                 07/12/2000                                 *)
(*                                                                            *)
(* This module defines a pretty-printer and the stream of commands to the pp  *)
(*                                                                            *)
(******************************************************************************)

(*i $Id$ i*)

(* Tokens for XML cdata, empty elements and not-empty elements           *)
(* Usage:                                                                *)
(*  Str cdata                                                            *)
(*  Empty (element_name, [attrname1, value1 ; ... ; attrnamen, valuen]   *)
(*  NEmpty (element_name, [attrname1, value2 ; ... ; attrnamen, valuen], *)
(*          content                                                      *)
type token =
  | Str of string
  | Empty of string * (string * string) list
  | NEmpty of string * (string * string) list * token Stream.t

(* currified versions of the token constructors make the code more readable *)
val xml_empty : string -> (string * string) list -> token Stream.t
val xml_nempty :
  string -> (string * string) list -> token Stream.t -> token Stream.t
val xml_cdata : string -> token Stream.t

(* The pretty printer for streams of token                                  *)
(* Usage:                                                                   *)
(*  pp tokens None     pretty prints the output on stdout                   *)
(*  pp tokens (Some filename) pretty prints the output on the file filename *)
val pp : token Stream.t -> string option -> unit
