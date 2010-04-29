(***********************************************************************
    v      *   The Coq Proof Assistant  /  The Coq Development Team     
   <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud 
     \VV/  *************************************************************
      //   *      This file is distributed under the terms of the       
           *       GNU Lesser General Public License Version 2.1        
  ***********************************************************************)

open Univ
open Declarations
open Environ

val check_subtypes : env -> module_type_body -> module_type_body -> constraints


