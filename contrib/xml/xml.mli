(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *   The HELM Project         /   The EU MoWGLI Project      *)
(*         *   University of Bologna                                   *)
(***********************************************************************)

(* Copyright (C) 2000-2004, HELM Team.
 * 
 * This file is part of HELM, an Hypertextual, Electronic
 * Library of Mathematics, developed at the Computer Science
 * Department, University of Bologna, Italy.
 * 
 * HELM is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 * 
 * HELM is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with HELM; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston,
 * MA  02111-1307, USA.
 * 
 * For details, see the HELM World-Wide-Web page,
 * http://helm.unibo.it/.
 *)

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
