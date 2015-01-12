(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names

(** TODO: cleanup *)

(** {6 Declarations} *)
(** A {e declaration} has the form [(name,body,type)]. It is either an
    {e assumption} if [body=None] or a {e definition} if
    [body=Some actualbody]. It is referred by {e name} if [na] is an
    identifier or by {e relative index} if [na] is not an identifier
    (in the latter case, [na] is of type [name] but just for printing
    purpose) *)

type named_declaration = Id.t * Constr.t option * Constr.t
type named_list_declaration = Id.t list * Constr.t option * Constr.t
type rel_declaration = Name.t * Constr.t option * Constr.t

val map_named_declaration :
  (Constr.t -> Constr.t) -> named_declaration -> named_declaration
val map_named_list_declaration :
  (Constr.t -> Constr.t) -> named_list_declaration -> named_list_declaration
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

(** {6 Signatures of ordered named declarations } *)

type named_context = named_declaration list
type section_context = named_context
type named_list_context = named_list_declaration list
type rel_context = rel_declaration list
(** In [rel_context], more recent declaration is on top *)

val empty_named_context : named_context
val add_named_decl : named_declaration -> named_context -> named_context
val vars_of_named_context : named_context -> Id.Set.t

val lookup_named : Id.t -> named_context -> named_declaration

(** number of declarations *)
val named_context_length : named_context -> int

(** named context equality *)
val named_context_equal : named_context -> named_context -> bool

(** {6 Recurrence on [named_context]: older declarations processed first } *)
val fold_named_context :
  (named_declaration -> 'a -> 'a) -> named_context -> init:'a -> 'a

val fold_named_list_context :
  (named_list_declaration -> 'a -> 'a) -> named_list_context -> init:'a -> 'a

(** newer declarations first *)
val fold_named_context_reverse :
  ('a -> named_declaration -> 'a) -> init:'a -> named_context -> 'a

(** {6 Section-related auxiliary functions } *)
val instance_from_named_context : named_context -> Constr.t list

(** {6 ... } *)
(** Signatures of ordered optionally named variables, intended to be
   accessed by de Bruijn indices *)

(** {6 Recurrence on [rel_context]: older declarations processed first } *)
val fold_rel_context :
  (rel_declaration -> 'a -> 'a) -> rel_context -> init:'a -> 'a

(** newer declarations first *)
val fold_rel_context_reverse :
  ('a -> rel_declaration -> 'a) -> init:'a -> rel_context -> 'a

(** {6 Map function of [rel_context] } *)
val map_rel_context : (Constr.t -> Constr.t) -> rel_context -> rel_context

(** {6 Map function of [named_context] } *)
val map_named_context : (Constr.t -> Constr.t) -> named_context -> named_context

(** {6 Map function of [rel_context] } *)
val iter_rel_context : (Constr.t -> unit) -> rel_context -> unit

(** {6 Map function of [named_context] } *)
val iter_named_context : (Constr.t -> unit) -> named_context -> unit

(** {6 Contexts of declarations referred to by de Bruijn indices } *)

val empty_rel_context : rel_context
val add_rel_decl : rel_declaration -> rel_context -> rel_context

val lookup_rel : int -> rel_context -> rel_declaration
(** Size of the [rel_context] including LetIns *)
val rel_context_length : rel_context -> int
(** Size of the [rel_context] without LetIns *)
val rel_context_nhyps : rel_context -> int
(** Indicates whether a LetIn or a Lambda, starting from oldest declaration *)
val rel_context_tags : rel_context -> bool list
