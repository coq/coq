(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

{

 let chan_out = ref stdout

 let comment_depth = ref 0
 let cRcpt = ref 0
 let comments = ref true
 let print s = output_string !chan_out s

 exception Fin_fichier

}

let space = [' ' '\t' '\n' '\r']
let enddot = '.' (' ' | '\t' | '\n' | '\r' | eof)

rule action = parse
  | "Theorem" space { print "Theorem "; body lexbuf;
  	              cRcpt := 1; action lexbuf }
  | "Lemma" space   { print "Lemma ";   body lexbuf;
      	       	      cRcpt := 1; action lexbuf }
  | "Fact" space    { print "Fact ";   body lexbuf;
      	       	      cRcpt := 1; action lexbuf }
  | "Remark" space  { print "Remark ";  body lexbuf;
      	       	      cRcpt := 1; action lexbuf }
  | "Goal" space    { print "Goal ";    body lexbuf;
      	       	      cRcpt := 1; action lexbuf }
  | "Correctness" space { print "Correctness "; body_pgm lexbuf;
      	       	          cRcpt := 1; action lexbuf }
  | "Definition" space  { print "Definition "; body_def lexbuf;
			  cRcpt := 1; action lexbuf }
  | "Hint" space        { skip_until_point lexbuf ; action lexbuf }
  | "Hints" space        { skip_until_point lexbuf ; action lexbuf }
  | "Transparent" space { skip_until_point lexbuf ; action lexbuf }
  | "Immediate"	space   { skip_until_point lexbuf ; action lexbuf }
  | "Syntax" space      { skip_until_point lexbuf ; action lexbuf }
  | "(*"      { (if !comments then print "(*");
		comment_depth := 1;
      	        comment lexbuf;
		cRcpt := 0; action lexbuf }
  | [' ' '\t']* '\n'      { if !cRcpt < 2 then print "\n";
      	       	       	    cRcpt := !cRcpt+1; action lexbuf}
  | eof       { (raise Fin_fichier : unit)}
  | _         { print (Lexing.lexeme lexbuf); cRcpt := 0; action lexbuf }

and comment = parse
  | "(*"  { (if !comments then print "(*");
      	    comment_depth := succ !comment_depth; comment lexbuf }
  | "*)"  { (if !comments then print "*)");
      	    comment_depth := pred !comment_depth;
            if !comment_depth > 0 then comment lexbuf }
  | "*)" [' ''\t']*'\n' { (if !comments then print (Lexing.lexeme lexbuf));
      			  comment_depth := pred !comment_depth;
			  if !comment_depth > 0 then comment lexbuf }
  | eof   { raise Fin_fichier }
  | _     { (if !comments then print (Lexing.lexeme lexbuf));
	    comment lexbuf }

and skip_comment = parse
  | "(*"  { comment_depth := succ !comment_depth; skip_comment lexbuf }
  | "*)"  { comment_depth := pred !comment_depth;
            if !comment_depth > 0 then skip_comment lexbuf }
  | eof   { raise Fin_fichier }
  | _     { skip_comment lexbuf }

and body_def = parse
  | [^'.']* ":=" { print (Lexing.lexeme lexbuf); () }
  | _            { print (Lexing.lexeme lexbuf); body lexbuf }

and body = parse
  | enddot { print ".\n"; skip_proof lexbuf }
  | ":="   { print ".\n"; skip_proof lexbuf }
  | "(*"   { print "(*"; comment_depth := 1;
      	     comment lexbuf; body lexbuf }
  | eof    { raise Fin_fichier }
  | _      { print (Lexing.lexeme lexbuf); body lexbuf }

and body_pgm = parse
  | enddot { print ".\n"; skip_proof lexbuf }
  | "(*"   { print "(*"; comment_depth := 1;
      	     comment lexbuf; body_pgm lexbuf }
  | eof    { raise Fin_fichier }
  | _      { print (Lexing.lexeme lexbuf); body_pgm lexbuf }

and skip_until_point = parse
  | '.' '\n' { () }
  | enddot   { end_of_line lexbuf }
  | "(*"     { comment_depth := 1;
      	       skip_comment lexbuf; skip_until_point lexbuf }
  | eof      { raise Fin_fichier }
  | _        { skip_until_point lexbuf }

and end_of_line = parse
  | [' ' '\t' ]*	{ end_of_line lexbuf }
  | '\n'		{ () }
  | eof   	     	{ raise Fin_fichier }
  | _	  		{ print (Lexing.lexeme lexbuf) }

and skip_proof = parse
  | "Save."	{ end_of_line lexbuf }
  | "Save" space
                { skip_until_point lexbuf }
  | "Qed."  	{ end_of_line lexbuf }
  | "Qed" space
                { skip_until_point lexbuf }
  | "Defined."  { end_of_line lexbuf }
  | "Defined" space
                { skip_until_point lexbuf }
  | "Abort." 	{ end_of_line lexbuf }
  | "Abort" space
                { skip_until_point lexbuf }
  | "Proof" space   { skip_until_point lexbuf }
  | "Proof" [' ' '\t']* '.'  { skip_proof lexbuf }
  | "(*"    { comment_depth := 1;
      	      skip_comment lexbuf; skip_proof lexbuf }
  | eof     { raise Fin_fichier }
  | _       { skip_proof lexbuf }
