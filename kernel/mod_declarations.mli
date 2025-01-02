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
open Declarations

type structure_field_body =
  (module_body, module_type_body) Declarations.structure_field_body

and structure_body =
  (module_body, module_type_body) Declarations.structure_body

(** A module signature is a structure, with possibly functors on top of it *)

and module_signature = (module_type_body,structure_body) functorize

and module_implementation =
  | Abstract (** no accessible implementation *)
  | Algebraic of module_expression (** non-interactive algebraic expression *)
  | Struct of structure_body (** interactive body living in the parameter context of [mod_type] *)
  | FullStruct (** special case of [Struct] : the body is exactly [mod_type] *)

and 'a generic_module_body =
  { mod_mp : ModPath.t; (** absolute path of the module *)
    mod_expr : ('a, module_implementation) when_mod_body; (** implementation *)
    mod_type : module_signature; (** expanded type *)
    mod_type_alg : module_expression option; (** algebraic type *)
    mod_delta : Mod_subst.delta_resolver; (**
      quotiented set of equivalent constants and inductive names *)
    mod_retroknowledge : ('a, Retroknowledge.action list) when_mod_body }

(** For a module, there are five possible situations:
    - [Declare Module M : T] then [mod_expr = Abstract; mod_type_alg = Some T]
    - [Module M := E] then [mod_expr = Algebraic E; mod_type_alg = None]
    - [Module M : T := E] then [mod_expr = Algebraic E; mod_type_alg = Some T]
    - [Module M. ... End M] then [mod_expr = FullStruct; mod_type_alg = None]
    - [Module M : T. ... End M] then [mod_expr = Struct; mod_type_alg = Some T]
    And of course, all these situations may be functors or not. *)

and module_body = mod_body generic_module_body

(** A [module_type_body] is just a [module_body] with no implementation and
    also an empty [mod_retroknowledge]. Its [mod_type_alg] contains
    the algebraic definition of this module type, or [None]
    if it has been built interactively. *)

and module_type_body = mod_type generic_module_body

type 'a module_retroknowledge = ('a, Retroknowledge.action list) when_mod_body

(** Extra invariants :

    - No [MEwith] inside a [mod_expr] implementation : the 'with' syntax
      is only supported for module types

    - A module application is atomic, for instance ((M N) P) :
      * the head of [MEapply] can only be another [MEapply] or a [MEident]
      * the argument of [MEapply] is now directly forced to be a [ModPath.t].
*)


(** {6 Accessors} *)

val mod_expr : module_body -> module_implementation

(** {6 Hashconsing} *)

val hcons_generic_module_body : 'a generic_module_body -> 'a generic_module_body
val hcons_module_body : module_body -> module_body
val hcons_module_type : module_type_body -> module_type_body
