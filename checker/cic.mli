(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Type definitions for the Calculus of Inductive Constructions *)

(** We regroup here the type definitions for structures of the Coq kernel
    that are present in .vo files. Here is everything the Checker needs
    to know about these structures for verifying a .vo. Note that this
    isn't an exact copy of the kernel code :

    - there isn't any abstraction here (see e.g. [constr] or [lazy_constr])
    - some types are left undefined when they aren't used by the Checker
    - some types have less constructors when the final constructors aren't
      supposed to appear in .vo (see [REVERTcast] and [Direct]).

    The following types are also described in a reified manner in values.ml,
    for validating the layout of structures after de-marshalling. So:

    IF YOU ADAPT THIS FILE, YOU SHOULD MODIFY values.ml ACCORDINGLY !
*)

open Names

(*************************************************************************)
(** {4 From term.ml} *)

(** {6 The sorts of CCI. } *)

type contents = Pos | Null

type sorts =
  | Prop of contents       (** Prop and Set *)
  | Type of Univ.universe  (** Type *)

(** {6 The sorts family of CCI. } *)

type sorts_family = InProp | InSet | InType

(** {6 Useful types } *)

(** {6 Existential variables } *)
type existential_key = int

(** {6 Existential variables } *)
type metavariable = int

(** {6 Case annotation } *)
type case_style = LetStyle | IfStyle | LetPatternStyle | MatchStyle
  | RegularStyle (** infer printing form from number of constructor *)
type case_printing =
  { ind_nargs : int; (** length of the arity of the inductive type *)
    style     : case_style }

(** the integer is the number of real args, needed for reduction *)
type case_info =
  { ci_ind        : inductive;
    ci_npar       : int;
    ci_cstr_ndecls : int array; (** number of real args of each constructor *)
    ci_pp_info    : case_printing (** not interpreted by the kernel *)
  }

(** This defines the strategy to use for verifiying a Cast. *)
type cast_kind = VMcast | NATIVEcast | DEFAULTcast (* | REVERTcast *)

(** {6 The type of constructions } *)

(** [constr array] is an instance matching definitional [named_context] in
    the same order (i.e. last argument first) *)
type 'constr pexistential = existential_key * 'constr array
type 'constr prec_declaration =
    Name.t array * 'constr array * 'constr array
type 'constr pfixpoint =
    (int array * int) * 'constr prec_declaration
type 'constr pcofixpoint =
    int * 'constr prec_declaration

type constr =
  | Rel       of int
  | Var       of Id.t (** Shouldn't occur in a .vo *)
  | Meta      of metavariable (** Shouldn't occur in a .vo *)
  | Evar      of constr pexistential (** Shouldn't occur in a .vo *)
  | Sort      of sorts
  | Cast      of constr * cast_kind * constr
  | Prod      of Name.t * constr * constr
  | Lambda    of Name.t * constr * constr
  | LetIn     of Name.t * constr * constr * constr
  | App       of constr * constr array
  | Const     of constant
  | Ind       of inductive
  | Construct of constructor
  | Case      of case_info * constr * constr * constr array
  | Fix       of constr pfixpoint
  | CoFix     of constr pcofixpoint

type existential = constr pexistential
type rec_declaration = constr prec_declaration
type fixpoint = constr pfixpoint
type cofixpoint = constr pcofixpoint

(** {6 Type of assumptions and contexts}  *)

type rel_declaration = Name.t * constr option * constr
type rel_context = rel_declaration list

(** The declarations below in .vo should be outside sections,
    so we expect there a value compatible with an empty list *)
type section_context = unit


(*************************************************************************)
(** {4 From mod_susbt.ml and lazyconstr.ml} *)

(** {6 Substitutions} *)

type delta_hint =
  | Inline of int * constr option
  | Equiv of kernel_name

type delta_resolver = module_path MPmap.t * delta_hint KNmap.t

type 'a umap_t = 'a MPmap.t * 'a MBImap.t
type substitution = (module_path * delta_resolver) umap_t

(** {6 Delayed constr} *)

type 'a lazy_subst =
  | LSval of 'a
  | LSlazy of substitution list * 'a

type constr_substituted = constr lazy_subst ref

(** Nota : in coqtop, the [lazy_constr] type also have a [Direct]
    constructor, but it shouldn't occur inside a .vo, so we ignore it *)

type lazy_constr =
  | Indirect of substitution list * DirPath.t * int
(* | Direct of constr_substituted *)


(*************************************************************************)
(** {4 From declarations.mli} *)

(** Some types unused in the checker, hence left undefined *)

(** Bytecode *)
type reloc_table
type to_patch_substituted
(** Native code *)
type native_name
(** Retroknowledge *)
type action

(** Engagements *)

type engagement = ImpredicativeSet

(** {6 Representation of constants (Definition/Axiom) } *)

type polymorphic_arity = {
  poly_param_levels : Univ.universe option list;
  poly_level : Univ.universe;
}

type constant_type =
  | NonPolymorphicType of constr
  | PolymorphicArity of rel_context * polymorphic_arity

(** Inlining level of parameters at functor applications.
    This is ignored by the checker. *)

type inline = int option

(** A constant can have no body (axiom/parameter), or a
    transparent body, or an opaque one *)

type constant_def =
  | Undef of inline
  | Def of constr_substituted
  | OpaqueDef of lazy_constr Future.computation

type constant_body = {
    const_hyps : section_context; (** New: younger hyp at top *)
    const_body : constant_def;
    const_type : constant_type;
    const_body_code : to_patch_substituted;
    const_constraints : Univ.constraints Future.computation;
    const_native_name : native_name ref;
    const_inline_code : bool }

(** {6 Representation of mutual inductive types } *)

type recarg =
  | Norec
  | Mrec of inductive
  | Imbr of inductive

type wf_paths = recarg Rtree.t

type monomorphic_inductive_arity = {
  mind_user_arity : constr;
  mind_sort : sorts;
}

type inductive_arity =
| Monomorphic of monomorphic_inductive_arity
| Polymorphic of polymorphic_arity

type one_inductive_body = {
(** {8 Primitive datas } *)

    mind_typename : Id.t; (** Name of the type: [Ii] *)

    mind_arity_ctxt : rel_context; (** Arity context of [Ii] with parameters: [forall params, Ui] *)

    mind_arity : inductive_arity; (** Arity sort and original user arity if monomorphic *)

    mind_consnames : Id.t array; (** Names of the constructors: [cij] *)

    mind_user_lc : constr array;
 (** Types of the constructors with parameters:  [forall params, Tij],
     where the Ik are replaced by de Bruijn index in the
     context I1:forall params, U1 ..  In:forall params, Un *)

(** {8 Derived datas } *)

    mind_nrealargs : int; (** Number of expected real arguments of the type (no let, no params) *)

    mind_nrealargs_ctxt : int; (** Length of realargs context (with let, no params) *)

    mind_kelim : sorts_family list; (** List of allowed elimination sorts *)

    mind_nf_lc : constr array; (** Head normalized constructor types so that their conclusion is atomic *)

    mind_consnrealdecls : int array;
 (** Length of the signature of the constructors (with let, w/o params)
    (not used in the kernel) *)

    mind_recargs : wf_paths; (** Signature of recursive arguments in the constructors *)

(** {8 Datas for bytecode compilation } *)

    mind_nb_constant : int; (** number of constant constructor *)

    mind_nb_args : int; (** number of no constant constructor *)

    mind_reloc_tbl : reloc_table;
  }

type mutual_inductive_body = {

    mind_packets : one_inductive_body array;  (** The component of the mutual inductive block *)

    mind_record : bool;  (** Whether the inductive type has been declared as a record *)

    mind_finite : bool;  (** Whether the type is inductive or coinductive *)

    mind_ntypes : int;  (** Number of types in the block *)

    mind_hyps : section_context;  (** Section hypotheses on which the block depends *)

    mind_nparams : int;  (** Number of expected parameters *)

    mind_nparams_rec : int;  (** Number of recursively uniform (i.e. ordinary) parameters *)

    mind_params_ctxt : rel_context;  (** The context of parameters (includes let-in declaration) *)

    mind_constraints : Univ.constraints;  (** Universes constraints enforced by the inductive declaration *)

(** {8 Data for native compilation } *)

    mind_native_name : native_name ref; (** status of the code (linked or not, and where) *)
  }

(** {6 Modules: signature component specifications, module types, and
  module declarations } *)

type structure_field_body =
  | SFBconst of constant_body
  | SFBmind of mutual_inductive_body
  | SFBmodule of module_body
  | SFBmodtype of module_type_body

and structure_body = (label * structure_field_body) list

and struct_expr_body =
  | SEBident of module_path
  | SEBfunctor of MBId.t * module_type_body * struct_expr_body
  | SEBapply of struct_expr_body * struct_expr_body * Univ.constraints
  | SEBstruct of structure_body
  | SEBwith of struct_expr_body * with_declaration_body

and with_declaration_body =
    With_module_body of Id.t list * module_path
  | With_definition_body of  Id.t list * constant_body
and module_body =
    {  (** absolute path of the module *)
      mod_mp : module_path;
      (** Implementation *)
      mod_expr : struct_expr_body option;
      (** Signature *)
      mod_type : struct_expr_body;
      (** algebraic structure expression is kept
	 if it's relevant for extraction  *)
      mod_type_alg : struct_expr_body option;
      (** set of all constraint in the module  *)
      mod_constraints : Univ.constraints;
      (** quotiented set of equivalent constant and inductive name  *)
      mod_delta : delta_resolver;
      mod_retroknowledge : action list}

and module_type_body =
    {
      (** Path of the module type *)
      typ_mp : module_path;
      typ_expr : struct_expr_body;
      (** algebraic structure expression is kept
	 if it's relevant for extraction  *)
      typ_expr_alg : struct_expr_body option ;
      typ_constraints : Univ.constraints;
      (** quotiented set of equivalent constant and inductive name  *)
      typ_delta : delta_resolver}


(*************************************************************************)
(** {4 From safe_typing.ml} *)

type nativecode_symb_array

type compilation_unit_name = DirPath.t

type library_info = compilation_unit_name * Digest.t

type library_deps = library_info array

type compiled_library = {
  comp_name : compilation_unit_name;
  comp_mod : module_body;
  comp_deps : library_deps;
  comp_enga : engagement option;
  comp_natsymbs : nativecode_symb_array
}


(*************************************************************************)
(** {4 From library.ml} *)

type library_objects

type library_disk = {
  md_name : compilation_unit_name;
  md_compiled : compiled_library;
  md_objects : library_objects;
  md_deps : library_deps;
  md_imports : compilation_unit_name array }

type opaque_table = constr array

(** A .vo file is currently made of :

    1) a magic number
    2) a marshalled [library_disk] structure
    3) a marshalled [Digest.t] string
    4) a marshalled [opaque_table]
    5) a marshalled [Digest.t] string
*)
