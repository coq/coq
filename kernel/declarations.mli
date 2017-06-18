(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Term

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
  template_param_levels : Univ.universe_level option list;
  template_level : Univ.universe;
}

type ('a, 'b) declaration_arity = 
  | RegularArity of 'a
  | TemplateArity of 'b

type constant_type = (types, Context.Rel.t * template_arity) declaration_arity

(** Inlining level of parameters at functor applications.
    None means no inlining *)

type inline = int option

(** A constant can have no body (axiom/parameter), or a
    transparent body, or an opaque one *)

(** Projections are a particular kind of constant: 
    always transparent. *)

type projection_body = {
  proj_ind : mutual_inductive;
  proj_npars : int;
  proj_arg : int;
  proj_type : types; (* Type under params *)
  proj_eta : constr * types; (* Eta-expanded term and type *)
  proj_body : constr; (* For compatibility with VMs only, the match version *)
}

(* Global declarations (i.e. constants) can be either: *)
type constant_def =
  | Undef of inline                       (** a global assumption *)
  | Def of constr Mod_subst.substituted   (** or a transparent global definition *)
  | OpaqueDef of Opaqueproof.opaque       (** or an opaque global definition *)

type constant_universes = Univ.universe_context

(** The [typing_flags] are instructions to the type-checker which
    modify its behaviour. The typing flags used in the type-checking
    of a constant are tracked in their {!constant_body} so that they
    can be displayed to the user. *)
type typing_flags = {
  check_guarded : bool; (** If [false] then fixed points and co-fixed
                            points are assumed to be total. *)
  check_universes : bool; (** If [false] universe constraints are not checked *)
}

(* some contraints are in constant_constraints, some other may be in
 * the OpaqueDef *)
type constant_body = {
    const_hyps : Context.Named.t; (** New: younger hyp at top *)
    const_body : constant_def;
    const_type : constant_type;
    const_body_code : Cemitcodes.to_patch_substituted option;
    const_polymorphic : bool; (** Is it polymorphic or not *)
    const_universes : constant_universes;
    const_proj : projection_body option;
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
    If the record is not primitive, then None
    Otherwise, we get:
    - The identifier for the binder name of the record in primitive projections.
    - The constants associated to each projection.
    - The checked projection bodies. *)

type record_body = (Id.t * constant array * projection_body array) option

type regular_inductive_arity = {
  mind_user_arity : types;
  mind_sort : sorts;
}

type inductive_arity = (regular_inductive_arity, template_arity) declaration_arity

type one_inductive_body = {
(** {8 Primitive datas } *)

    mind_typename : Id.t; (** Name of the type: [Ii] *)

    mind_arity_ctxt : Context.Rel.t; (** Arity context of [Ii] with parameters: [forall params, Ui] *)

    mind_arity : inductive_arity; (** Arity sort and original user arity *)

    mind_consnames : Id.t array; (** Names of the constructors: [cij] *)

    mind_user_lc : types array;
 (** Types of the constructors with parameters:  [forall params, Tij],
     where the Ik are replaced by de Bruijn index in the
     context I1:forall params, U1 ..  In:forall params, Un *)

(** {8 Derived datas } *)

    mind_nrealargs : int; (** Number of expected real arguments of the type (no let, no params) *)

    mind_nrealdecls : int; (** Length of realargs context (with let, no params) *)

    mind_kelim : sorts_family list; (** List of allowed elimination sorts *)

    mind_nf_lc : types array; (** Head normalized constructor types so that their conclusion exposes the inductive type *)

    mind_consnrealargs : int array;
 (** Number of expected proper arguments of the constructors (w/o params) *)

    mind_consnrealdecls : int array;
 (** Length of the signature of the constructors (with let, w/o params) *)

    mind_recargs : wf_paths; (** Signature of recursive arguments in the constructors *)

(** {8 Datas for bytecode compilation } *)

    mind_nb_constant : int; (** number of constant constructor *)

    mind_nb_args : int; (** number of no constant constructor *)

    mind_reloc_tbl :  Cbytecodes.reloc_table;
  }

type mutual_inductive_body = {

    mind_packets : one_inductive_body array;  (** The component of the mutual inductive block *)

    mind_record : record_body option; (** The record information *)

    mind_finite : Decl_kinds.recursivity_kind;  (** Whether the type is inductive or coinductive *)

    mind_ntypes : int;  (** Number of types in the block *)

    mind_hyps : Context.Named.t;  (** Section hypotheses on which the block depends *)

    mind_nparams : int;  (** Number of expected parameters including non-uniform ones (i.e. length of mind_params_ctxt w/o let-in) *)

    mind_nparams_rec : int;  (** Number of recursively uniform (i.e. ordinary) parameters *)

    mind_params_ctxt : Context.Rel.t;  (** The context of parameters (includes let-in declaration) *)

    mind_polymorphic : bool; (** Is it polymorphic or not *)

    mind_universes : Univ.universe_context; (** Local universe variables and constraints *)

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
  | WithMod of Id.t list * module_path
  | WithDef of Id.t list * constr Univ.in_universe_context

type module_alg_expr =
  | MEident of module_path
  | MEapply of module_alg_expr * module_path
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

and module_body =
  { mod_mp : module_path; (** absolute path of the module *)
    mod_expr : module_implementation; (** implementation *)
    mod_type : module_signature; (** expanded type *)
    mod_type_alg : module_expression option; (** algebraic type *)
    mod_constraints : Univ.ContextSet.t; (**
      set of all universes constraints in the module  *)
    mod_delta : Mod_subst.delta_resolver; (**
      quotiented set of equivalent constants and inductive names *)
    mod_retroknowledge : Retroknowledge.action list }

(** For a module, there are five possible situations:
    - [Declare Module M : T] then [mod_expr = Abstract; mod_type_alg = Some T]
    - [Module M := E] then [mod_expr = Algebraic E; mod_type_alg = None]
    - [Module M : T := E] then [mod_expr = Algebraic E; mod_type_alg = Some T]
    - [Module M. ... End M] then [mod_expr = FullStruct; mod_type_alg = None]
    - [Module M : T. ... End M] then [mod_expr = Struct; mod_type_alg = Some T]
    And of course, all these situations may be functors or not. *)

(** A [module_type_body] is just a [module_body] with no
    implementation ([mod_expr] always [Abstract]) and also
    an empty [mod_retroknowledge]. Its [mod_type_alg] contains
    the algebraic definition of this module type, or [None]
    if it has been built interactively. *)

and module_type_body = module_body

(** Extra invariants :

    - No [MEwith] inside a [mod_expr] implementation : the 'with' syntax
      is only supported for module types

    - A module application is atomic, for instance ((M N) P) :
      * the head of [MEapply] can only be another [MEapply] or a [MEident]
      * the argument of [MEapply] is now directly forced to be a [module_path].
*)
