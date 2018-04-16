/************************************************************************/
/*         *   The Coq Proof Assistant / The Coq Development Team       */
/*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       */
/* <O___,, *       (see CREDITS file for the list of authors)           */
/*   \VV/  **************************************************************/
/*    //   *    This file is distributed under the terms of the         */
/*         *     GNU Lesser General Public License Version 2.1          */
/*         *     (see LICENSE file for the text of the license)         */
/************************************************************************/
grammar TacticNotations;

// Terminals are not visited, so we add non-terminals for each terminal that
// needs rendering (in particular whitespace (kept in output) vs. WHITESPACE
// (discarded)).

top: blocks EOF;
blocks: block ((whitespace)? block)*;
block: atomic | meta | hole | repeat | curlies;
repeat: LGROUP (ATOM)? WHITESPACE blocks (WHITESPACE)? RBRACE;
curlies: LBRACE (whitespace)? blocks (whitespace)? RBRACE;
whitespace: WHITESPACE;
meta: METACHAR;
atomic: ATOM (SUB)?;
hole: ID (SUB)?;

LGROUP: '{' [+*?];
LBRACE: '{';
RBRACE: '}';
METACHAR: '%' [|(){}];
ATOM: '@' | '_' | ~[@_{} ]+;
ID: '@' ('_'? [a-zA-Z0-9])+;
SUB: '_' '_' [a-zA-Z0-9]+;
WHITESPACE: ' '+;
