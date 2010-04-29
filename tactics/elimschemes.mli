(***********************************************************************
    v      *   The Coq Proof Assistant  /  The Coq Development Team     
   <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud 
     \VV/  *************************************************************
      //   *      This file is distributed under the terms of the       
           *       GNU Lesser General Public License Version 2.1        
  ***********************************************************************)

(** {% $ %}Id: elimschemes.mli 12584 2009-12-13 21:04:34Z herbelin {% $ %} *)

open Ind_tables

(** Induction/recursion schemes *)

val rect_scheme_kind_from_prop : individual scheme_kind
val ind_scheme_kind_from_prop : individual scheme_kind
val rec_scheme_kind_from_prop : individual scheme_kind
val rect_dep_scheme_kind_from_type : individual scheme_kind
val ind_dep_scheme_kind_from_type : individual scheme_kind
val rec_dep_scheme_kind_from_type : individual scheme_kind


(** Case analysis schemes *)

val case_scheme_kind_from_type : individual scheme_kind
val case_scheme_kind_from_prop : individual scheme_kind
val case_dep_scheme_kind_from_type : individual scheme_kind
val case_dep_scheme_kind_from_type_in_prop : individual scheme_kind
val case_dep_scheme_kind_from_prop : individual scheme_kind
val case_dep_scheme_kind_from_prop_in_prop : individual scheme_kind
