(***********************************************************************
    v      *   The Coq Proof Assistant  /  The Coq Development Team     
   <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud 
     \VV/  *************************************************************
      //   *      This file is distributed under the terms of the       
           *       GNU Lesser General Public License Version 2.1        
  ***********************************************************************)

(** Coq interface to the Whelp query engine developed at
   the University of Bologna *)

open Names
open Term
open Topconstr
open Environ

type whelp_request =
  | Locate of string
  | Elim of inductive
  | Constr of string * constr

val whelp : whelp_request -> unit
