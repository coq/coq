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
open Constr

(** This module defines the internal representation of global
   declarations. This includes global constants/axioms, mutual
   inductive definitions, modules and module types *)

(** {6 Representation of constants (Definition/Axiom) } *)

(** Template polymorphism: provides universe polymorphism and sort
    polymorphism (restricted to above prop qualities), with implicit instances
    and inferring the universes from the types of parameters instead.

    The data other than [mind_template] in the inductive bodies is
    instantiated to the default universes (e.g. [mind_user_arity],
    [mind_sort], the constructor data, etc).
*)

type template_universes = {
  (** For each LocalAssum parameter (in regular order, not rel_context order),
      tell whether it binds a quality or a universe level
      (read from the sort, NB it is possible to bind a qvar next to a constant universe)
      (the binders are DeBruijn levels as with universe polymorphism,
      but may be instantiated with algebraics) *)
  template_param_arguments : Sorts.t option list;
  (** Inductive sort with abstracted universes. *)
  template_concl : Sorts.t;
  template_context : UVars.AbstractContext.t;
  (** Template_defaults qualities are all QType.
      Also the universes are all levels so we can use Instance. *)
  template_defaults : UVars.Instance.t;
}

(** Inlining level of parameters at functor applications.
    None means no inlining *)

type inline = int option

(** A constant can have no body (axiom/parameter), or a
    transparent body, or an opaque one *)

(* Global declarations (i.e. constants) can be either: *)
type ('a, 'opaque, 'rules) constant_def =
  | Undef of inline                       (** a global assumption *)
  | Def of 'a                             (** or a transparent global definition *)
  | OpaqueDef of 'opaque                  (** or an opaque global definition *)
  | Primitive of CPrimitives.t (** or a primitive operation *)
  | Symbol of 'rules                      (** or a symbol *)

type universes =
  | Monomorphic
  | Polymorphic of UVars.AbstractContext.t

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

  allow_uip: bool;
  (** Allow definitional UIP (breaks termination) *)

}

(** {6 Representation of definitions/assumptions in the kernel } *)

(* some contraints are in constant_constraints, some other may be in
 * the OpaqueDef *)
type ('opaque, 'bytecode) pconstant_body = {
    const_hyps : Constr.named_context; (** younger hyp at top *)
    const_univ_hyps : UVars.Instance.t;
    const_body : (Constr.t, 'opaque, bool) constant_def;
                    (** [bool] is for [unfold_fix] in symbols *)
    const_type : types;
    const_relevance : Sorts.relevance;
    const_body_code : 'bytecode;
    const_universes : universes;
    const_inline_code : bool;
    const_typing_flags : typing_flags; (** The typing options which
                                           were used for
                                           type-checking. *)
}

type constant_body = (Opaqueproof.opaque, Vmlibrary.indirect_code option) pconstant_body

(** {6 Representation of mutual inductive types in the kernel } *)

type recarg_type =
| RecArgInd of inductive
| RecArgPrim of Constant.t

type recarg =
| Norec
| Mrec of recarg_type

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

type squash_info =
  | AlwaysSquashed
  | SometimesSquashed of Sorts.Quality.Set.t
  (** A sort polymorphic inductive [I@{...|...|...} : ... -> Type@{ s|...}]
      is squashed at a given instantiation if any quality in the list is not smaller than [s].

      NB: if [s] is a variable SometimesSquashed contains SProp
      ie non ground instantiations are squashed. *)

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

    mind_sort : Sorts.t; (** Arity sort *)

    mind_user_arity : types;
    (** Original user arity, convertible to [mkArity (mind_arity_ctxt, mind_sort)].
        As such it contains the parameters.
        (not necessarily a syntactic arity, eg [relation A] instead of [A -> A -> Prop]) *)

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

    mind_squashed : squash_info option;
    (** Is elimination restricted to the inductive's sort? *)

    mind_nf_lc : (rel_context * types) array;
 (** Head normalized constructor types so that their conclusion
     exposes the inductive type. It includes the parameters, i.e. each
     component of the array has the form [(decls_ij, Ii params realargs_ij)]
     where [decls_ij] is the concatenation of the context of parameters
     (possibly with let-ins) and of the arguments of the constructor
     (possibly with let-ins). This context is internally represented
     as a list [[cstrdecl_ij{q_ij};...;cstrdecl_ij1;paramdecl_m;...;paramdecl_1]]
     such that the constructor in fine has type [forall paramdecls,
     forall cstrdecls_ij, Ii params realargs_ij] with [params] referring to
     the assumptions of [paramdecls] and [realargs_ij] being the
     "indices" specific to the constructor. *)

    mind_consnrealargs : int array;
 (** Number of expected proper arguments of the constructors (w/o params) *)

    mind_consnrealdecls : int array;
 (** Length of the signature of the constructors (with let, w/o params) *)

    mind_recargs : wf_paths; (** Signature of recursive arguments in the constructors *)

    mind_relevance : Sorts.relevance;
    (* XXX this is redundant with mind_sort, is it actually worth keeping? *)

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

    mind_finite : recursivity_kind;  (** Whether the type is inductive, coinductive or non-recursive *)

    mind_ntypes : int;  (** Number of types in the block *)

    mind_hyps : Constr.named_context;  (** Section hypotheses on which the block depends *)

    mind_univ_hyps : UVars.Instance.t; (** Section polymorphic universes. *)

    mind_nparams : int;  (** Number of expected parameters including non-uniform ones (i.e. length of mind_params_ctxt w/o let-in) *)

    mind_nparams_rec : int;  (** Number of recursively uniform (i.e. ordinary) parameters *)

    mind_params_ctxt : Constr.rel_context;  (** The context of parameters (includes let-in declaration) *)

    mind_universes : universes; (** Information about monomorphic/polymorphic/cumulative inductives and their universes *)

    mind_template : template_universes option;

    mind_variance : UVars.Variance.t array option; (** Variance info, [None] when non-cumulative. *)

    mind_sec_variance : UVars.Variance.t array option;
    (** Variance info for section polymorphic universes. [None]
       outside sections. The final variance once all sections are
       discharged is [mind_sec_variance ++ mind_variance]. *)

    mind_private : bool option; (** allow pattern-matching: Some true ok, Some false blocked *)

    mind_typing_flags : typing_flags; (** typing flags at the time of the inductive creation *)
}

type mind_specif = mutual_inductive_body * one_inductive_body

(** {6 Rewrite rules } *)

type quality_pattern = Sorts.Quality.pattern =
  | PQVar of int option | PQConstant of Sorts.Quality.constant

type instance_mask = UVars.Instance.mask

type sort_pattern = Sorts.pattern =
  | PSProp | PSSProp | PSSet | PSType of int option | PSQSort of int option * int option

(** Patterns are internally represented as pairs of a head-pattern and a list of eliminations
    Eliminations correspond to elements of the stack in a reduction machine,
    they represent a pattern with a hole, to be filled with the head-pattern
*)
type 'arg head_pattern =
  | PHRel     of int
  | PHSort    of sort_pattern
  | PHSymbol  of Constant.t * instance_mask
  | PHInd     of inductive * instance_mask
  | PHConstr  of constructor * instance_mask
  | PHInt     of Uint63.t
  | PHFloat   of Float64.t
  | PHString  of Pstring.t
  | PHLambda  of 'arg array * 'arg
  | PHProd    of 'arg array * 'arg

type pattern_elimination =
  | PEApp     of pattern_argument array
  | PECase    of inductive * instance_mask * pattern_argument * pattern_argument array
  | PEProj    of Projection.Repr.t

and head_elimination = pattern_argument head_pattern * pattern_elimination list

and pattern_argument =
  | EHole of int
  | EHoleIgnored
  | ERigid of head_elimination

type rewrite_rule = {
  nvars : int * int * int;
  lhs_pat : instance_mask * pattern_elimination list;
  rhs : constr;
}

(** {6 Representation of rewrite rules in the kernel } *)

(** [(c, { lhs_pat = (u, elims); rhs })] in this list stands for [(PHSymbol (c,u), elims) ==> rhs] *)
type rewrite_rules_body = {
  rewrules_rules : (Constant.t * rewrite_rule) list;
}

(** {6 Module declarations } *)

type mod_body = [ `ModBody ]
type mod_type = [ `ModType ]

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

type 'uconstr functor_alg_expr =
| MENoFunctor of 'uconstr module_alg_expr
| MEMoreFunctor of 'uconstr functor_alg_expr

(** A module expression is an algebraic expression, possibly functorized. *)

type module_expression = (constr * UVars.AbstractContext.t option) functor_alg_expr

(** A component of a module structure *)

type ('mod_body, 'mod_type) structure_field_body =
  | SFBconst of constant_body
  | SFBmind of mutual_inductive_body
  | SFBrules of rewrite_rules_body
  | SFBmodule of 'mod_body
  | SFBmodtype of 'mod_type

(** A module structure is a list of labeled components.

    Note : we may encounter now (at most) twice the same label in
    a [structure_body], once for a module ([SFBmodule] or [SFBmodtype])
    and once for an object ([SFBconst] or [SFBmind]) *)

and ('mod_body, 'mod_type) structure_body = (Label.t * ('mod_body, 'mod_type) structure_field_body) list
