(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
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

(** {6 Representation of constants (Definition/Axiom) } *)

(** Non-universe polymorphic mode polymorphism (Coq 8.2+): inductives
    and constants hiding inductives are implicitly polymorphic when
    applied to parameters, on the universes appearing in the whnf of
    their parameters and their conclusion, in a template style.

    In truly universe polymorphic mode, we always use RegularArity.
*)

type template_arity = {
  template_level : Sorts.t;
}

type template_universes = {
  template_param_levels : Univ.Level.t option list;
  template_context : Univ.ContextSet.t;
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
type ('a, 'opaque) constant_def =
  | Undef of inline                       (** a global assumption *)
  | Def of 'a                             (** or a transparent global definition *)
  | OpaqueDef of 'opaque                  (** or an opaque global definition *)
  | Primitive of CPrimitives.t (** or a primitive operation *)

type universes =
  | Monomorphic
  | Polymorphic of Univ.AbstractContext.t

(** The [typing_flags] are instructions to the type-checker which
    modify its behaviour. The typing flags used in the type-checking
    of a constant are tracked in their {!constant_body} so that they
    can be displayed to the user. *)
type typing_flags = {
  check_guarded : bool;
  (** If [false] then fixed points and co-fixed points are assumed to
      be total. *)

  check_positive : bool;
  (** If [false] then inductive types are assumed positive and co-inductive
      types are assumed productive. *)

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

  impredicative_set: bool;
  (** Predicativity of the [Set] universe. *)

  sprop_allowed: bool;
  (** If [false], error when encountering [SProp]. *)

  cumulative_sprop : bool;
  (** SProp <= Type *)

  allow_uip: bool;
  (** Allow definitional UIP (breaks termination) *)

}

(** {6 Representation of definitions/assumptions in the kernel } *)

(* some contraints are in constant_constraints, some other may be in
 * the OpaqueDef *)
type 'opaque pconstant_body = {
    const_hyps : Constr.named_context; (** younger hyp at top *)
    const_univ_hyps : Univ.Instance.t;
    const_body : (Constr.t, 'opaque) constant_def;
    const_type : types;
    const_relevance : Sorts.relevance;
    const_body_code : Vmemitcodes.body_code option;
    const_universes : universes;
    const_inline_code : bool;
    const_typing_flags : typing_flags; (** The typing options which
                                           were used for
                                           type-checking. *)
}

type constant_body = Opaqueproof.opaque pconstant_body

(** {6 Representation of mutual inductive types in the kernel } *)
type nested_type =
| NestedInd of inductive
| NestedPrimitive of Constant.t

type recarg =
| Norec
| Mrec of inductive
| Nested of nested_type

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
| PrimRecord of (Id.t * Label.t array * Sorts.relevance array * types array) array

type regular_inductive_arity = {
  mind_user_arity : types;
  mind_sort : Sorts.t;
}

type inductive_arity = (regular_inductive_arity, template_arity) declaration_arity

(** {7 Datas specific to a single type of a block of mutually inductive type } *)
type one_inductive_body = {
(** {8 Primitive datas } *)

    mind_typename : Id.t; (** Name of the type: [Ii] *)

    mind_arity_ctxt : Constr.rel_context;
 (** Arity context of [Ii]. It includes the context of parameters,
     that is, it has the form [paramdecls, realdecls_i] such that [Ui]
     (see above) is [forall realdecls_i, si] for some sort [si] and
     such that [Ii] has thus type [forall paramdecls, forall
     realdecls_i, si]. The context itself is represented internally as
     a list in reverse order
     [[realdecl_i{r_i};...;realdecl_i1;paramdecl_m;...;paramdecl_1]]. *)

    mind_arity : inductive_arity; (** Arity sort and original user arity *)

    mind_consnames : Id.t array; (** Names of the constructors: [cij] *)

    mind_user_lc : types array;
 (** Types of the constructors with parameters: [forall params, Tij],
     where the recursive occurrences of the inductive types in [Tij]
     (i.e. in the type of the j-th constructor of the i-th types of
     the block a shown above) have the form [Ind ((mind,0),u)], ...,
     [Ind ((mind,n-1),u)] for [u] the canonical abstract instance
     associated to [mind_universes] and [mind] the name to which the
     inductive block is bound in the environment. *)

(** {8 Derived datas } *)

    mind_nrealargs : int; (** Number of expected real arguments of the type (no let, no params) *)

    mind_nrealdecls : int; (** Length of realargs context (with let, no params) *)

    mind_kelim : Sorts.family; (** Highest allowed elimination sort *)

    mind_nf_lc : (rel_context * types) array;
 (** Head normalized constructor types so that their conclusion
     exposes the inductive type. It includes the parameters, i.e. each
     component of the array has the form [(decls_ij, Ii params realargs_ij)]
     where [decls_ij] is the concatenation of the context of parameters
     (possibly with let-ins) and of the arguments of the constructor
     (possibly with let-ins). This context is internally represented
     as a list [[cstrdecl_ij{q_ij};...;cstrdecl_ij1;paramdecl_m;...;paramdecl_1]]
     such that the constructor in fine has type [forall paramdecls,
     forall cstrdecls_ij, Ii params realargs_ij]] with [params] referring to
     the assumptions of [paramdecls] and [realargs_ij] being the
     "indices" specific to the constructor. *)

    mind_consnrealargs : int array;
 (** Number of expected proper arguments of the constructors (w/o params) *)

    mind_consnrealdecls : int array;
 (** Length of the signature of the constructors (with let, w/o params) *)

    mind_recargs : wf_paths; (** Signature of recursive arguments in the constructors *)

    mind_relevance : Sorts.relevance;

(** {8 Datas for bytecode compilation } *)

    mind_nb_constant : int; (** number of constant constructor *)

    mind_nb_args : int; (** number of no constant constructor *)

    mind_reloc_tbl :  Vmvalues.reloc_table;
  }

type recursivity_kind =
  | Finite (** = inductive *)
  | CoFinite (** = coinductive *)
  | BiFinite (** = non-recursive, like in "Record" definitions *)

(** {7 Datas associated to a full block of mutually inductive types } *)

type mutual_inductive_body = {

    mind_packets : one_inductive_body array;  (** The component of the mutual inductive block *)

    mind_record : record_info; (** The record information *)

    mind_finite : recursivity_kind;  (** Whether the type is inductive or coinductive *)

    mind_ntypes : int;  (** Number of types in the block *)

    mind_hyps : Constr.named_context;  (** Section hypotheses on which the block depends *)

    mind_univ_hyps : Univ.Instance.t; (** Section polymorphic universes. *)

    mind_nparams : int;  (** Number of expected parameters including non-uniform ones (i.e. length of mind_params_ctxt w/o let-in) *)

    mind_nparams_rec : int;  (** Number of recursively uniform (i.e. ordinary) parameters *)

    mind_params_ctxt : Constr.rel_context;  (** The context of parameters (includes let-in declaration) *)

    mind_universes : universes; (** Information about monomorphic/polymorphic/cumulative inductives and their universes *)

    mind_template : template_universes option;

    mind_variance : Univ.Variance.t array option; (** Variance info, [None] when non-cumulative. *)

    mind_sec_variance : Univ.Variance.t array option;
    (** Variance info for section polymorphic universes. [None]
       outside sections. The final variance once all sections are
       discharged is [mind_sec_variance ++ mind_variance]. *)

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

type 'uconstr with_declaration =
  | WithMod of Id.t list * ModPath.t
  | WithDef of Id.t list * 'uconstr

type 'uconstr module_alg_expr =
  | MEident of ModPath.t
  | MEapply of 'uconstr module_alg_expr * ModPath.t
  | MEwith of 'uconstr module_alg_expr * 'uconstr with_declaration

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

and module_expression = (module_type_body, (constr * Univ.AbstractContext.t option) module_alg_expr) functorize

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
