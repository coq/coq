(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
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
