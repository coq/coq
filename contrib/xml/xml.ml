(******************************************************************************)
(*                                                                            *)
(*                               PROJECT HELM                                 *)
(*                                                                            *)
(*                     A tactic to print Coq objects in XML                   *)
(*                                                                            *)
(*                Claudio Sacerdoti Coen <sacerdot@cs.unibo.it>               *)
(*                                 18/10/2000                                 *)
(*                                                                            *)
(* This module defines a pretty-printer and the stream of commands to the pp  *)
(*                                                                            *)
(******************************************************************************)


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
       print_string ("\nWriting on file \"" ^ filename ^ "\" was succesfull\n");
       flush stdout
   | None ->
       pp_r 0 strm
;;
