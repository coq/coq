(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
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
  { ind_tags : bool list; (* tell whether letin or lambda in the arity of the inductive type *)
    cstr_tags : bool list array; (* whether each pattern var of each constructor is a let-in (true) or not (false) *)
    style     : case_style }

(** the integer is the number of real args, needed for reduction *)
type case_info =
  { ci_ind        : inductive;
    ci_npar       : int;
    ci_cstr_ndecls : int array; (* number of pattern vars of each constructor (with let's)*)
    ci_cstr_nargs : int array; (* number of pattern vars of each constructor (w/o let's) *)
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
type 'a puniverses = 'a Univ.puniverses
type pconstant = constant puniverses
type pinductive = inductive puniverses
type pconstructor = constructor puniverses

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
  | Const     of pconstant
  | Ind       of pinductive
  | Construct of pconstructor
  | Case      of case_info * constr * constr * constr array
  | Fix       of constr pfixpoint
  | CoFix     of constr pcofixpoint
  | Proj      of constant * constr

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

type 'a substituted = {
  mutable subst_value : 'a;
  mutable subst_subst : substitution list;
}

type constr_substituted = constr substituted

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


type template_arity = {
  template_param_levels : Univ.universe_level option list;
  template_level : Univ.universe;
}

type ('a, 'b) declaration_arity = 
  | RegularArity of 'a
  | TemplateArity of 'b

type constant_type = (constr, rel_context * template_arity) declaration_arity

(** Inlining level of parameters at functor applications.
    This is ignored by the checker. *)

type inline = int option

(** A constant can have no body (axiom/parameter), or a
    transparent body, or an opaque one *)

(** Projections are a particular kind of constant: 
    always transparent. *)

type projection_body = {
  proj_ind : mutual_inductive;
  proj_npars : int;
  proj_arg : int;
  proj_type : constr; (* Type under params *)
  proj_eta : constr * constr; (* Eta-expanded term and type *)
  proj_body : constr; (* For compatibility, the match version *)
}

type constant_def =
  | Undef of inline
  | Def of constr_substituted
  | OpaqueDef of lazy_constr

type constant_universes = Univ.universe_context

type constant_body = {
    const_hyps : section_context; (** New: younger hyp at top *)
    const_body : constant_def;
    const_type : constant_type;
    const_body_code : to_patch_substituted;
    const_polymorphic : bool; (** Is it polymorphic or not *)
    const_universes : constant_universes;
    const_proj : projection_body option;
    const_inline_code : bool }

(** {6 Representation of mutual inductive types } *)

type recarg =
  | Norec
  | Mrec of inductive
  | Imbr of inductive

type wf_paths = recarg Rtree.t

type record_body = (Id.t * constant array * projection_body array) option
    (* The body is empty for non-primitive records, otherwise we get its
       binder name in projections and list of projections if it is primitive. *)

type regular_inductive_arity = {
  mind_user_arity : constr;
  mind_sort : sorts;
}

type recursivity_kind =
  | Finite (** = inductive *)
  | CoFinite (** = coinductive *)
  | BiFinite (** = non-recursive, like in "Record" definitions *)

type inductive_arity = (regular_inductive_arity, template_arity) declaration_arity

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

    mind_nrealdecls : int; (** Length of realargs context (with let, no params) *)

    mind_kelim : sorts_family list; (** List of allowed elimination sorts *)

    mind_nf_lc : constr array; (** Head normalized constructor types so that their conclusion is atomic *)

    mind_consnrealargs : int array;
 (** Length of the signature of the constructors (w/o let, w/o params)
    (not used in the kernel) *)

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

    mind_record : record_body option; (** Whether the inductive type has been declared as a record. *)

    mind_finite : recursivity_kind;  (** Whether the type is inductive or coinductive *)

    mind_ntypes : int;  (** Number of types in the block *)

    mind_hyps : section_context;  (** Section hypotheses on which the block depends *)

    mind_nparams : int;  (** Number of expected parameters *)

    mind_nparams_rec : int;  (** Number of recursively uniform (i.e. ordinary) parameters *)

    mind_params_ctxt : rel_context;  (** The context of parameters (includes let-in declaration) *)

    mind_polymorphic : bool; (** Is it polymorphic or not *)

    mind_universes : Univ.universe_context; (** Local universe variables and constraints *)

    mind_private : bool option; (** allow pattern-matching: Some true ok, Some false blocked *)

(** {8 Data for native compilation } *)

    mind_native_name : native_name ref; (** status of the code (linked or not, and where) *)
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
  | WithDef of Id.t list * constr

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
  | Abstract (** no accessible implementation (keep this constructor first!) *)
  | Algebraic of module_expression (** non-interactive algebraic expression *)
  | Struct of module_signature (** interactive body *)
  | FullStruct (** special case of [Struct] : the body is exactly [mod_type] *)

and module_body =
  { mod_mp : module_path; (** absolute path of the module *)
    mod_expr : module_implementation; (** implementation *)
    mod_type : module_signature; (** expanded type *)
    (** algebraic type, kept if it's relevant for extraction *)
    mod_type_alg : module_expression option;
    (** set of all constraints in the module  *)
    mod_constraints : Univ.constraints;
    (** quotiented set of equivalent constants and inductive names *)
    mod_delta : delta_resolver;
    mod_retroknowledge : action list }

(** A [module_type_body] is just a [module_body] with no
    implementation ([mod_expr] always [Abstract]) and also
    an empty [mod_retroknowledge] *)

and module_type_body = module_body

(*************************************************************************)
(** {4 From safe_typing.ml} *)

type nativecode_symb_array

type compilation_unit_name = DirPath.t

type vodigest =
  | Dvo of Digest.t              (* The digest of the seg_lib part *)
  | Dviovo of Digest.t * Digest.t (* The digest of the seg_lib+seg_univ part *)

type library_info = compilation_unit_name * vodigest

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

type opaque_table = constr Future.computation array
type univ_table =
  (Univ.universe_context_set Future.computation array * Univ.universe_context_set * bool) option

(** A .vo file is currently made of :

    1) a magic number (4 bytes, cf output_binary_int)
    2) a marshalled [library_disk] structure
    3) a [Digest.t] string (16 bytes)
    4) a marshalled [univ_table] (* Some if vo was obtained from vi *)
    5) a [Digest.t] string (16 bytes)
    6) a marshalled [None] discharge_table (* Some in vi files *)
    7) a [Digest.t] string (16 bytes)
    8) a marshalled [None] todo_table (* Some in vi files *)
    9) a [Digest.t] string (16 bytes)
   10) a marshalled [opaque_table]
   11) a [Digest.t] string (16 bytes)
*)
