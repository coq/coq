(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)
(******************************************************************************)
(*                                                                            *)
(*                               PROJECT HELM                                 *)
(*                                                                            *)
(*                     A module to print Coq objects in XML                   *)
(*                                                                            *)
(*                Claudio Sacerdoti Coen <sacerdot@cs.unibo.it>               *)
(*                                 06/12/2000                                 *)
(*                                                                            *)
(* This module adds to the vernacular interpreter the functions that fullfill *)
(* the new commands defined in Xml.v                                          *)
(*                                                                            *)
(******************************************************************************)
(*i camlp4deps: "parsing/grammar.cma" i*)

(* $Id$ *)

open Util;;
open Vernacinterp;;

open Extend;;
open Genarg;;
open Pp;;
open Pcoq;;

(* File name *)

VERNAC ARGUMENT EXTEND filename
| [ "File" string(fn) ] -> [ Some fn ]
| [ ] -> [ None ]
END

(* Print XML and Show XML *)

VERNAC COMMAND EXTEND Xml
| [ "Print" "XML" filename(fn) global(qid) ] -> [ Xmlcommand.print_ref qid fn ]

| [ "Show" "XML" filename(fn) "Proof" ] -> [ Xmlcommand.show fn ]
END
