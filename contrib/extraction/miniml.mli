(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*s Target language for extraction: a core ML called MiniML. *)

open Pp
open Identifier
open Names
open Term

(*s ML type expressions. *)

type ml_type = 
  | Tvar  of identifier
  | Tapp  of ml_type list
  | Tarr  of ml_type * ml_type
  | Tglob of global_reference
  | Tprop
  | Tarity
      
(*s ML inductive types. *)

type ml_ind = 
  identifier list * global_reference * (global_reference * ml_type list) list

(*s ML terms. *)

type ml_ast = 
  | MLrel   of int
  | MLapp   of ml_ast * ml_ast list
  | MLlam   of identifier * ml_ast
  | MLletin of identifier * ml_ast * ml_ast
  | MLglob  of global_reference
  | MLcons  of global_reference * ml_ast list
  | MLcase  of ml_ast * (global_reference * identifier list * ml_ast) array
  | MLfix   of int * identifier array * ml_ast array
  | MLexn   of identifier
  | MLprop
  | MLarity
  | MLcast  of ml_ast * ml_type
  | MLmagic of ml_ast

(*s ML declarations. *)

type ml_decl = 
  | Dtype   of ml_ind list * bool (* cofix *)
  | Dabbrev of global_reference * identifier list * ml_type
  | Dglob   of global_reference * ml_ast

(*s Pretty-printing of MiniML in a given concrete syntax is parameterized
    by a function [pp_global] that pretty-prints global references. 
    The resulting pretty-printer is a module of type [Mlpp] providing
    functions to print types, terms and declarations. *)

module type Mlpp_param = sig
  val cofix_warning : bool
  val rename_global : global_reference -> identifier
  val pp_type_global : global_reference -> std_ppcmds
  val pp_global : global_reference -> std_ppcmds
end

module type Mlpp = sig
  val pp_type : ml_type -> std_ppcmds
  val pp_ast : ml_ast -> std_ppcmds
  val pp_decl : ml_decl -> std_ppcmds
end

