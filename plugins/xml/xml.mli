(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *   The HELM Project         /   The EU MoWGLI Project       *)
(*         *   University of Bologna                                    *)
(************************************************************************)
(*          This file is distributed under the terms of the             *)
(*           GNU Lesser General Public License Version 2.1              *)
(*                                                                      *)
(*                 Copyright (C) 2000-2004, HELM Team.                  *)
(*                       http://helm.cs.unibo.it                        *)
(************************************************************************)

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

val pp_ch : token Stream.t -> out_channel -> unit

(* The pretty printer for streams of token                                  *)
(* Usage:                                                                   *)
(*  pp tokens None     pretty prints the output on stdout                   *)
(*  pp tokens (Some filename) pretty prints the output on the file filename *)
val pp : token Stream.t -> string option -> unit
