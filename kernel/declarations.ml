(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Constr

(** This module defines the internal representation of global
   declarations. This includes global constants/axioms, mutual
   inductive definitions, modules and module types *)

type set_predicativity = ImpredicativeSet | PredicativeSet

type engagement = set_predicativity

(** {6 Representation of constants (Definition/Axiom) } *)

(** Non-universe polymorphic mode polymorphism (Coq 8.2+): inductives
    and constants hiding inductives are implicitely polymorphic when
    applied to parameters, on the universes appearing in the whnf of
    their parameters and their conclusion, in a template style.
    
    In truely universe polymorphic mode, we always use RegularArity.
*)

type template_arity = {
  template_param_levels : Univ.Level.t option list;
  template_level : Univ.Universe.t;
}

type ('a, 'b) declaration_arity = 
  | RegularArity of 'a
  | TemplateArity of 'b

(** Inlining level of parameters at functor applications.
    None means no inlining *)

type inline = int option

(** A constant can have no body (axiom/parameter), or a
    transparent body, or an opaque one *)

(* Global declarations (i.e. constants) can be either: *)
type 'a constant_def =
  | Undef of inline                       (** a global assumption *)
  | Def of 'a                             (** or a transparent global definition *)
  | OpaqueDef of Opaqueproof.opaque       (** or an opaque global definition *)
  | Primitive of CPrimitives.t            (** or a primitive operation *)

type constant_universes =
  | Monomorphic_const of Univ.ContextSet.t
  | Polymorphic_const of Univ.AUContext.t

(** The [typing_flags] are instructions to the type-checker which
    modify its behaviour. The typing flags used in the type-checking
    of a constant are tracked in their {!constant_body} so that they
    can be displayed to the user. *)
type typing_flags = {
  check_guarded : bool;
  (** If [false] then fixed points and co-fixed points are assumed to
      be total. *)

  check_universes : bool;
  (** If [false] universe constraints are not checked *)

  conv_oracle : Conv_oracle.oracle;
  (** Unfolding strategies for conversion *)

  share_reduction : bool;
  (** Use by-need reduction algorithm *)

  enable_VM : bool;
  (** If [false], all VM conversions fall back to interpreted ones *)

  enable_native_compiler : bool;
  (** If [false], all native conversions fall back to VM ones *)

  indices_matter: bool;
  (** The universe of an inductive type must be above that of its indices. *)
}

(* some contraints are in constant_constraints, some other may be in
 * the OpaqueDef *)
type constant_body = {
    const_hyps : Constr.named_context; (** New: younger hyp at top *)
    const_body : Constr.t Mod_subst.substituted constant_def;
    const_type : types;
    const_body_code : Cemitcodes.to_patch_substituted option;
    const_universes : constant_universes;
    const_private_poly_univs : Univ.ContextSet.t option;
    const_inline_code : bool;
    const_typing_flags : typing_flags; (** The typing options which
                                           were used for
                                           type-checking. *)
}

(** {6 Representation of mutual inductive types in the kernel } *)

type recarg =
  | Norec
  | Mrec of inductive
  | Imbr of inductive

type wf_paths = recarg Rtree.t

(**
{v
   Inductive I1 (params) : U1 := c11 : T11 | ... | c1p1 : T1p1
   ...
   with      In (params) : Un := cn1 : Tn1 | ... | cnpn : Tnpn
v}
*)

(** Record information:
    If the type is not a record, then NotRecord
    If the type is a non-primitive record, then FakeRecord
    If it is a primitive record, for every type in the block, we get:
    - The identifier for the binder name of the record in primitive projections.
    - The constants associated to each projection.
    - The projection types (under parameters).

    The kernel does not exploit the difference between [NotRecord] and
    [FakeRecord]. It is mostly used by extraction, and should be extruded from
    the kernel at some point.
*)

type record_info =
| NotRecord
| FakeRecord
| PrimRecord of (Id.t * Label.t array * types array) array

type regular_inductive_arity = {
  mind_user_arity : types;
  mind_sort : Sorts.t;
}

type inductive_arity = (regular_inductive_arity, template_arity) declaration_arity

type one_inductive_body = {
(** {8 Primitive datas } *)

    mind_typename : Id.t; (** Name of the type: [Ii] *)

    mind_arity_ctxt : Constr.rel_context; (** Arity context of [Ii] with parameters: [forall params, Ui] *)

    mind_arity : inductive_arity; (** Arity sort and original user arity *)

    mind_consnames : Id.t array; (** Names of the constructors: [cij] *)

    mind_user_lc : types array;
 (** Types of the constructors with parameters:  [forall params, Tij],
     where the Ik are replaced by de Bruijn index in the
     context I1:forall params, U1 ..  In:forall params, Un *)

(** {8 Derived datas } *)

    mind_nrealargs : int; (** Number of expected real arguments of the type (no let, no params) *)

    mind_nrealdecls : int; (** Length of realargs context (with let, no params) *)

    mind_kelim : Sorts.family list; (** List of allowed elimination sorts *)

    mind_nf_lc : types array; (** Head normalized constructor types so that their conclusion exposes the inductive type *)

    mind_consnrealargs : int array;
 (** Number of expected proper arguments of the constructors (w/o params) *)

    mind_consnrealdecls : int array;
 (** Length of the signature of the constructors (with let, w/o params) *)

    mind_recargs : wf_paths; (** Signature of recursive arguments in the constructors *)

(** {8 Datas for bytecode compilation } *)

    mind_nb_constant : int; (** number of constant constructor *)

    mind_nb_args : int; (** number of no constant constructor *)

    mind_reloc_tbl :  Vmvalues.reloc_table;
  }

type abstract_inductive_universes =
  | Monomorphic_ind of Univ.ContextSet.t
  | Polymorphic_ind of Univ.AUContext.t
  | Cumulative_ind of Univ.ACumulativityInfo.t

type recursivity_kind =
  | Finite (** = inductive *)
  | CoFinite (** = coinductive *)
  | BiFinite (** = non-recursive, like in "Record" definitions *)

type mutual_inductive_body = {

    mind_packets : one_inductive_body array;  (** The component of the mutual inductive block *)

    mind_record : record_info; (** The record information *)

    mind_finite : recursivity_kind;  (** Whether the type is inductive or coinductive *)

    mind_ntypes : int;  (** Number of types in the block *)

    mind_hyps : Constr.named_context;  (** Section hypotheses on which the block depends *)

    mind_nparams : int;  (** Number of expected parameters including non-uniform ones (i.e. length of mind_params_ctxt w/o let-in) *)

    mind_nparams_rec : int;  (** Number of recursively uniform (i.e. ordinary) parameters *)

    mind_params_ctxt : Constr.rel_context;  (** The context of parameters (includes let-in declaration) *)

    mind_universes : abstract_inductive_universes; (** Information about monomorphic/polymorphic/cumulative inductives and their universes *)

    mind_private : bool option; (** allow pattern-matching: Some true ok, Some false blocked *)

    mind_typing_flags : typing_flags; (** typing flags at the time of the inductive creation *)
}

(** {6 Module declarations } *)

(** Functor expressions are forced to be on top of other expressions *)

type ('ty,'a) functorize =
  | NoFunctor of 'a
  | MoreFunctor of MBId.t * 'ty * ('ty,'a) functorize

(** The fully-algebraic module expressions : names, applications, 'with ...'.
    They correspond to the user entries of non-interactive modules.
    They will be later expanded into module structures in [Mod_typing],
    and won't play any role into the kernel after that : they are kept
    only for short module printing and for extraction. *)

type with_declaration =
  | WithMod of Id.t list * ModPath.t
  | WithDef of Id.t list * (constr * Univ.AUContext.t option)

type module_alg_expr =
  | MEident of ModPath.t
  | MEapply of module_alg_expr * ModPath.t
  | MEwith of module_alg_expr * with_declaration

(** A component of a module structure *)

type structure_field_body =
  | SFBconst of constant_body
  | SFBmind of mutual_inductive_body
  | SFBmodule of module_body
  | SFBmodtype of module_type_body

(** A module structure is a list of labeled components.

    Note : we may encounter now (at most) twice the same label in
    a [structure_body], once for a module ([SFBmodule] or [SFBmodtype])
    and once for an object ([SFBconst] or [SFBmind]) *)

and structure_body = (Label.t * structure_field_body) list

(** A module signature is a structure, with possibly functors on top of it *)

and module_signature = (module_type_body,structure_body) functorize

(** A module expression is an algebraic expression, possibly functorized. *)

and module_expression = (module_type_body,module_alg_expr) functorize

and module_implementation =
  | Abstract (** no accessible implementation *)
  | Algebraic of module_expression (** non-interactive algebraic expression *)
  | Struct of module_signature (** interactive body *)
  | FullStruct (** special case of [Struct] : the body is exactly [mod_type] *)

and 'a generic_module_body =
  { mod_mp : ModPath.t; (** absolute path of the module *)
    mod_expr : 'a; (** implementation *)
    mod_type : module_signature; (** expanded type *)
    mod_type_alg : module_expression option; (** algebraic type *)
    mod_constraints : Univ.ContextSet.t; (**
      set of all universes constraints in the module  *)
    mod_delta : Mod_subst.delta_resolver; (**
      quotiented set of equivalent constants and inductive names *)
    mod_retroknowledge : 'a module_retroknowledge }

(** For a module, there are five possible situations:
    - [Declare Module M : T] then [mod_expr = Abstract; mod_type_alg = Some T]
    - [Module M := E] then [mod_expr = Algebraic E; mod_type_alg = None]
    - [Module M : T := E] then [mod_expr = Algebraic E; mod_type_alg = Some T]
    - [Module M. ... End M] then [mod_expr = FullStruct; mod_type_alg = None]
    - [Module M : T. ... End M] then [mod_expr = Struct; mod_type_alg = Some T]
    And of course, all these situations may be functors or not. *)

and module_body = module_implementation generic_module_body

(** A [module_type_body] is just a [module_body] with no implementation and
    also an empty [mod_retroknowledge]. Its [mod_type_alg] contains
    the algebraic definition of this module type, or [None]
    if it has been built interactively. *)

and module_type_body = unit generic_module_body

and _ module_retroknowledge =
| ModBodyRK :
  Retroknowledge.action list -> module_implementation module_retroknowledge
| ModTypeRK : unit module_retroknowledge

(** Extra invariants :

    - No [MEwith] inside a [mod_expr] implementation : the 'with' syntax
      is only supported for module types

    - A module application is atomic, for instance ((M N) P) :
      * the head of [MEapply] can only be another [MEapply] or a [MEident]
      * the argument of [MEapply] is now directly forced to be a [ModPath.t].
*)
