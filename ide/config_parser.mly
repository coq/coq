/************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2011     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************/

/* $Id$ */

%{

  open Parsing
  open Util

%}

%token <string> IDENT STRING
%token EQUAL EOF

%type <(string list) Util.Stringmap.t> prefs
%start prefs

%%

prefs:
  pref_list EOF { $1 }
;

pref_list:
   pref_list pref { let (k,d) = $2 in Stringmap.add k d $1 }
 | /* epsilon */  { Stringmap.empty }
;

pref:
  IDENT EQUAL string_list { ($1, List.rev $3) }
;

string_list:
   string_list STRING { $2 :: $1 }
 | /* epsilon */      { [] }
;

