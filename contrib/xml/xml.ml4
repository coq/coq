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


(* the type token for XML cdata, empty elements and not-empty elements *)
(* Usage:                                                                *)
(*  Str cdata                                                            *)
(*  Empty (element_name, [attrname1, value1 ; ... ; attrnamen, valuen]   *)
(*  NEmpty (element_name, [attrname1, value2 ; ... ; attrnamen, valuen], *)
(*          content                                                      *)
type token = Str of string
           | Empty of string * (string * string) list
	   | NEmpty of string * (string * string) list * token Stream.t
;;

(* currified versions of the constructors make the code more readable *)
let xml_empty name attrs = [< 'Empty(name,attrs) >]
let xml_nempty name attrs content = [< 'NEmpty(name,attrs,content) >]
let xml_cdata str = [< 'Str str >]

(* Usage:                                                                   *)
(*  pp tokens None     pretty prints the output on stdout                   *)
(*  pp tokens (Some filename) pretty prints the output on the file filename *)
let pp strm fn =
 let channel = ref stdout in
 let rec pp_r m =
  parser
    [< 'Str a ; s >] ->
      print_spaces m ;
      fprint_string (a ^ "\n") ;
      pp_r m s
  | [< 'Empty(n,l) ; s >] ->
      print_spaces m ;
      fprint_string ("<" ^ n) ;
      List.iter (function (n,v) -> fprint_string (" " ^ n ^ "=\"" ^ v ^ "\"")) l;
      fprint_string "/>\n" ;
      pp_r m s
  | [< 'NEmpty(n,l,c) ; s >] ->
      print_spaces m ;
      fprint_string ("<" ^ n) ;
      List.iter (function (n,v) -> fprint_string (" " ^ n ^ "=\"" ^ v ^ "\"")) l;
      fprint_string ">\n" ;
      pp_r (m+1) c ;
      print_spaces m ;
      fprint_string ("</" ^ n ^ ">\n") ;
      pp_r m s
  | [< >] -> ()
 and print_spaces m =
  for i = 1 to m do fprint_string "  " done
 and fprint_string str =
  output_string !channel str
 in
  match fn with
     Some filename ->
      let filename = filename ^ ".xml" in
       channel := open_out filename ;
       pp_r 0 strm ;
       close_out !channel ;
       print_string ("\nWriting on file \"" ^ filename ^ "\" was succesful\n");
       flush stdout
   | None ->
       pp_r 0 strm
;;
