(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* Certification of Imperative Programs / Jean-Christophe Filli�tre *)

(* $Id$ *)

open Ptype
open Past


(* Here we separate local and global variables, we check the use of
 * references and arrays w.r.t the local and global environments, etc.
 * These functions directly raise UserError exceptions on bad programs.
 *)

val db_type_v : Names.identifier list -> 'a ml_type_v -> 'a ml_type_v

val db_prog : program -> program

