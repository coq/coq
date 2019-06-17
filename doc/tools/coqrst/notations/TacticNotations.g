/************************************************************************/
/*         *   The Coq Proof Assistant / The Coq Development Team       */
/*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       */
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

// The distinction between nopipeblock and block is needed because we only want
// to require escaping within alternative blocks, so that e.g. `first [ x | y ]`
// can be written without escaping the `|`.

top: blocks EOF;
blocks: block ((whitespace)? block)*;

block: pipe | nopipeblock;
nopipeblock: atomic | escaped | hole | alternative | repeat | curlies;

alternative: LALT (WHITESPACE)? altblocks (WHITESPACE)? RBRACE;
altblocks: altblock ((WHITESPACE)? altsep (WHITESPACE)? altblock)+;
altblock: nopipeblock ((whitespace)? nopipeblock)*;

repeat: LGROUP (ATOM | PIPE)? WHITESPACE blocks (WHITESPACE)? RBRACE;
curlies: LBRACE (whitespace)? blocks (whitespace)? RBRACE;

pipe: PIPE;
altsep: PIPE;
whitespace: WHITESPACE;
escaped: ESCAPED;
atomic: ATOM (SUB)?;
hole: ID (SUB)?;


LALT: '{|';
LGROUP: '{+' | '{*' | '{?';
LBRACE: '{';
RBRACE: '}';
ESCAPED: '%{' | '%}' | '%|';
PIPE: '|';
ATOM: '@' | '_' | ~[@_{}| ]+;
ID: '@' ('_'? [a-zA-Z0-9])+;
SUB: '_' '_' [a-zA-Z0-9]+;
WHITESPACE: ' '+;
