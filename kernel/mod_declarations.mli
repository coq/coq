(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Mod_subst
open Declarations

type 'a generic_module_body
type module_body = mod_body generic_module_body

(** For a module, there are five possible situations:
    - [Declare Module M : T] then [mod_expr = Abstract; mod_type_alg = Some T]
    - [Module M := E] then [mod_expr = Algebraic E; mod_type_alg = None]
    - [Module M : T := E] then [mod_expr = Algebraic E; mod_type_alg = Some T]
    - [Module M. ... End M] then [mod_expr = FullStruct; mod_type_alg = None]
    - [Module M : T. ... End M] then [mod_expr = Struct; mod_type_alg = Some T]
    And of course, all these situations may be functors or not. *)

type module_type_body = mod_type generic_module_body

(** A [module_type_body] is just a [module_body] with no implementation and
    also an empty [mod_retroknowledge]. Its [mod_type_alg] contains
    the algebraic definition of this module type, or [None]
    if it has been built interactively. *)

type structure_field_body =
  (module_body, module_type_body) Declarations.structure_field_body

type structure_body =
  (module_body, module_type_body) Declarations.structure_body

(** A module signature is a structure, with possibly functors on top of it *)

type module_signature = (module_type_body,structure_body) functorize

type module_implementation =
  | Abstract (** no accessible implementation *)
  | Algebraic of module_expression (** non-interactive algebraic expression *)
  | Struct of structure_body (** interactive body living in the parameter context of [mod_type] *)
  | FullStruct (** special case of [Struct] : the body is exactly [mod_type] *)

(** Extra invariants :

    - No [MEwith] inside a [mod_expr] implementation : the 'with' syntax
      is only supported for module types

    - A module application is atomic, for instance ((M N) P) :
      * the head of [MEapply] can only be another [MEapply] or a [MEident]
      * the argument of [MEapply] is now directly forced to be a [ModPath.t].
*)

(** {6 Accessors} *)

val mod_expr : module_body -> module_implementation
val mod_type : 'a generic_module_body -> module_signature
val mod_type_alg : 'a generic_module_body -> module_expression option
val mod_delta : 'a generic_module_body -> delta_resolver
val mod_retroknowledge : module_body -> Retroknowledge.action list

val mod_global_delta : 'a generic_module_body -> delta_resolver option
(** [None] if the argument is a functor, [mod_delta] otherwise *)

(** {6 Builders} *)

val make_module_body : module_signature -> Mod_subst.delta_resolver -> Retroknowledge.action list -> module_body
val make_module_type : module_signature -> Mod_subst.delta_resolver -> module_type_body

val strengthen_module_body : src:ModPath.t ->
  module_signature -> delta_resolver -> module_body -> module_body

val strengthen_module_type :
  structure_body -> delta_resolver -> module_type_body -> module_type_body

val replace_module_body : structure_body -> delta_resolver -> module_body -> module_body

val module_type_of_module : module_body -> module_type_body
val module_body_of_type : module_type_body -> module_body

val functorize_module : (Names.MBId.t * module_type_body) list -> module_body -> module_body

(** {6 Setters} *)

(* This is internal code used by the kernel, you should not mess with this. *)

val set_implementation : module_implementation -> module_body -> module_body
val set_algebraic_type : module_type_body -> module_expression -> module_type_body
val set_retroknowledge : module_body -> Retroknowledge.action list -> module_body

(** {6 Substitution} *)

type subst_kind
val subst_dom : subst_kind
val subst_codom : subst_kind
val subst_dom_codom : subst_kind
val subst_shallow_dom_codom : Mod_subst.substitution -> subst_kind

val subst_signature : subst_kind -> substitution ->
  ModPath.t -> module_signature -> module_signature

val subst_structure : subst_kind -> substitution ->
  ModPath.t -> structure_body -> structure_body

val subst_module : subst_kind -> substitution ->
  ModPath.t -> module_body -> module_body

val subst_modtype : subst_kind -> substitution ->
  ModPath.t -> module_type_body -> module_type_body

(** {6 Hashconsing} *)

val hcons_generic_module_body : 'a generic_module_body -> 'a generic_module_body
val hcons_module_body : module_body -> module_body
val hcons_module_type : module_type_body -> module_type_body

(** {6 Cleaning a module expression from bounded parts }

     For instance:
       functor(X:T)->struct module M:=X end)
     becomes:
       functor(X:T)->struct module M:=<content of T> end)
*)

val clean_structure : Names.MBIset.t -> structure_body -> structure_body
