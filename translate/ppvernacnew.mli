(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)
 
(* $Id$ *)

open Pp
open Genarg
open Vernacexpr
open Names
open Nameops
open Nametab
open Util
open Extend
open Ppconstr
open Pptactic
open Rawterm
open Coqast
open Pcoq
open Ast
open Libnames
open Ppextend
open Topconstr

val sep_end : std_ppcmds

val pr_vernac : vernac_expr -> std_ppcmds
