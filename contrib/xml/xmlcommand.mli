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
(*                                 07/12/2000                                 *)
(*                                                                            *)
(* This module defines a pretty-printer and the stream of commands to the pp  *)
(*                                                                            *)
(******************************************************************************)

(*i $Id$ i*)

(* print id dest                                                          *)
(*  where id   is the identifier (name) of a definition/theorem or of an  *)
(*             inductive definition                                       *)
(*  and   dest is either None (for stdout) or (Some filename)             *)
(* pretty prints via Xml.pp the object whose identifier is id on dest     *)
(* Note: it is printed only (and directly) the most cooked available      *)
(*       form of the definition (all the parameters are                   *)
(*       lambda-abstracted, but the object can still refer to variables)  *)
val print : Libnames.reference -> string option -> unit

(* show dest                                                  *)
(*  where dest is either None (for stdout) or (Some filename) *)
(* pretty prints via Xml.pp the proof in progress on dest     *)
val show : string option -> unit

(*CSC: untested, no more working or semantics unclear
(* print All () prints what is the structure of the current environment of *)
(* Coq. No terms are printed. Useful only for debugging                    *)
val printAll : unit -> unit

(* printLibrary identifier directory_name *)
(*  where identifier     is the qualified name of a library d                 *)
(*  and   directory_name is the directory in which to root all the xml files *)
(* prints all the xml files and directories corresponding to the subsections *)
(* and terms of the library d                                                 *)
(* Note: the terms are printed in their uncooked form plus the informations  *)
(* on the parameters of their most cooked form                               *)
val printLibrary : Libnames.qualid Util.located -> string option -> unit

(* printSection identifier directory_name *)
(*  where identifier     is the name of a closed section d                   *)
(*  and   directory_name is the directory in which to root all the xml files *)
(* prints all the xml files and directories corresponding to the subsections *)
(* and terms of the closed section d                                         *)
(* Note: the terms are printed in their uncooked form plus the informations  *)
(* on the parameters of their most cooked form                               *)
val printSection : Names.identifier -> string option -> unit
*)
