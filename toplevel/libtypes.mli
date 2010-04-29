(***********************************************************************
    v      *   The Coq Proof Assistant  /  The Coq Development Team     
   <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud 
     \VV/  *************************************************************
      //   *      This file is distributed under the terms of the       
           *       GNU Lesser General Public License Version 2.1        
  ***********************************************************************)

(** {% $ %}Id:{% $ %} *)

open Term

(** Persistent library of all declared object, indexed by their types 
    (uses Dnets) *)

(** results are the reference of the object, together with a context
(constr+evar) and a substitution under this context *)
type result = Libnames.global_reference * (constr*existential_key) * Termops.subst

(** this is the reduction function used in the indexing process *)
val reduce : types -> types

(** The different types of search available. 
    See term_dnet.mli for more explanations *)
val search_pattern : types -> result list
val search_concl : types -> result list
val search_head_concl : types -> result list
val search_eq_concl : constr -> types -> result list
