(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names

(** {6 Local } *)
(** A {e declaration} has the form [(name,body,type)]. It is either an
    {e assumption} if [body=None] or a {e definition} if
    [body=Some actualbody]. It is referred by {e name} if [na] is an
    identifier or by {e relative index} if [na] is not an identifier
    (in the latter case, [na] is of type [name] but just for printing
    purpose) *)

type named_declaration = Id.t * Constr.t option * Constr.t
type rel_declaration = Name.t * Constr.t option * Constr.t

val map_named_declaration :
  (Constr.t -> Constr.t) -> named_declaration -> named_declaration
val map_rel_declaration :
  (Constr.t -> Constr.t) -> rel_declaration -> rel_declaration

val fold_named_declaration :
  (Constr.t -> 'a -> 'a) -> named_declaration -> 'a -> 'a
val fold_rel_declaration :
  (Constr.t -> 'a -> 'a) -> rel_declaration -> 'a -> 'a

val exists_named_declaration :
  (Constr.t -> bool) -> named_declaration -> bool
val exists_rel_declaration :
  (Constr.t -> bool) -> rel_declaration -> bool

val for_all_named_declaration :
  (Constr.t -> bool) -> named_declaration -> bool
val for_all_rel_declaration :
  (Constr.t -> bool) -> rel_declaration -> bool

val eq_named_declaration :
  named_declaration -> named_declaration -> bool

val eq_rel_declaration :
    rel_declaration -> rel_declaration -> bool

(** {6 Contexts of declarations referred to by de Bruijn indices } *)

(** In [rel_context], more recent declaration is on top *)
type rel_context = rel_declaration list

val empty_rel_context : rel_context
val add_rel_decl : rel_declaration -> rel_context -> rel_context

val lookup_rel : int -> rel_context -> rel_declaration
(** Size of the [rel_context] including LetIns *)
val rel_context_length : rel_context -> int
(** Size of the [rel_context] without LetIns *)
val rel_context_nhyps : rel_context -> int
