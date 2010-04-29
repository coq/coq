(***********************************************************************
    v      *   The Coq Proof Assistant  /  The Coq Development Team     
   <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud 
     \VV/  *************************************************************
      //   *      This file is distributed under the terms of the       
           *       GNU Lesser General Public License Version 2.1        
  ***********************************************************************)

open Names
open Term

(** {6 Signatures of ordered named declarations } *)

type named_context = named_declaration list
type section_context = named_context

val empty_named_context : named_context
val add_named_decl : named_declaration -> named_context -> named_context
val vars_of_named_context : named_context -> identifier list

val lookup_named : identifier -> named_context -> named_declaration

(** number of declarations *)
val named_context_length : named_context -> int

(** {6 Recurrence on [named_context]: older declarations processed first } *)
val fold_named_context :
  (named_declaration -> 'a -> 'a) -> named_context -> init:'a -> 'a

(** newer declarations first *)
val fold_named_context_reverse :
  ('a -> named_declaration -> 'a) -> init:'a -> named_context -> 'a

(** {6 Section-related auxiliary functions } *)
val instance_from_named_context : named_context -> constr array

(** {6 ... } *)
(** Signatures of ordered optionally named variables, intended to be
   accessed by de Bruijn indices *)

val push_named_to_rel_context : named_context -> rel_context -> rel_context

(** {6 Recurrence on [rel_context]: older declarations processed first } *)
val fold_rel_context :
  (rel_declaration -> 'a -> 'a) -> rel_context -> init:'a -> 'a

(** newer declarations first *)
val fold_rel_context_reverse :
  ('a -> rel_declaration -> 'a) -> init:'a -> rel_context -> 'a

(** {6 Map function of [rel_context] } *)
val map_rel_context : (constr -> constr) -> rel_context -> rel_context

(** {6 Map function of [named_context] } *)
val map_named_context : (constr -> constr) -> named_context -> named_context

(** {6 Map function of [rel_context] } *)
val iter_rel_context : (constr -> unit) -> rel_context -> unit

(** {6 Map function of [named_context] } *)
val iter_named_context : (constr -> unit) -> named_context -> unit
