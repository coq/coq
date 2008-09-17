open Util
open Names
open Term

(* Bytecode *)
type values
type reloc_table
type to_patch_substituted
(*Retroknowledge *)
type action
type retroknowledge

(* Engagements *)

type engagement = ImpredicativeSet

(* Constants *)

type polymorphic_arity = {
  poly_param_levels : Univ.universe option list;
  poly_level : Univ.universe;
}

type constant_type =
  | NonPolymorphicType of constr
  | PolymorphicArity of rel_context * polymorphic_arity

type constr_substituted 
val force_constr : constr_substituted -> constr
val from_val : constr -> constr_substituted

type constant_body = {
    const_hyps : section_context; (* New: younger hyp at top *)
    const_body : constr_substituted option;
    const_type : constant_type;
    const_body_code : to_patch_substituted;
    const_constraints : Univ.constraints;
    const_opaque : bool; 
    const_inline : bool}

(* Mutual inductives *)

type recarg = 
  | Norec 
  | Mrec of int 
  | Imbr of inductive

type wf_paths = recarg Rtree.t

val mk_norec : wf_paths
val mk_paths : recarg -> wf_paths list array -> wf_paths
val dest_subterms : wf_paths -> wf_paths list array

type monomorphic_inductive_arity = {
  mind_user_arity : constr;
  mind_sort : sorts;
}

type inductive_arity = 
| Monomorphic of monomorphic_inductive_arity
| Polymorphic of polymorphic_arity

type one_inductive_body = {

(* Primitive datas *)

 (* Name of the type: [Ii] *)
    mind_typename : identifier;

 (* Arity context of [Ii] with parameters: [forall params, Ui] *)
    mind_arity_ctxt : rel_context;

 (* Arity sort, original user arity, and allowed elim sorts, if monomorphic *)
    mind_arity : inductive_arity;

 (* Names of the constructors: [cij] *)
    mind_consnames : identifier array;

 (* Types of the constructors with parameters: [forall params, Tij],
    where the Ik are replaced by de Bruijn index in the context
    I1:forall params, U1 ..  In:forall params, Un *)
    mind_user_lc : constr array;

(* Derived datas *)

 (* Number of expected real arguments of the type (no let, no params) *)
    mind_nrealargs : int;

 (* List of allowed elimination sorts *)
    mind_kelim : sorts_family list;

 (* Head normalized constructor types so that their conclusion is atomic *)
    mind_nf_lc : constr array;

 (* Length of the signature of the constructors (with let, w/o params) *)
    mind_consnrealdecls : int array;

 (* Signature of recursive arguments in the constructors *)
    mind_recargs : wf_paths;

(* Datas for bytecode compilation *)

 (* number of constant constructor *)
    mind_nb_constant : int;

 (* number of no constant constructor *)
    mind_nb_args : int;

    mind_reloc_tbl :  reloc_table; 
  }

type mutual_inductive_body = {

  (* The component of the mutual inductive block *)
    mind_packets : one_inductive_body array;

  (* Whether the inductive type has been declared as a record *)
    mind_record : bool;

  (* Whether the type is inductive or coinductive *)
    mind_finite : bool;

  (* Number of types in the block *)
    mind_ntypes : int;

  (* Section hypotheses on which the block depends *)
    mind_hyps : section_context;

  (* Number of expected parameters *)
    mind_nparams : int;

  (* Number of recursively uniform (i.e. ordinary) parameters *)
    mind_nparams_rec : int;

  (* The context of parameters (includes let-in declaration) *)
    mind_params_ctxt : rel_context;

  (* Universes constraints enforced by the inductive declaration *)
    mind_constraints : Univ.constraints;

  (* Source of the inductive block when aliased in a module *)
    mind_equiv : kernel_name option
  }

(* Modules *)

type substitution

type structure_field_body = 
  | SFBconst of constant_body
  | SFBmind of mutual_inductive_body
  | SFBmodule of module_body
  | SFBalias of module_path * struct_expr_body option 
      * Univ.constraints option
  | SFBmodtype of module_type_body

and structure_body = (label * structure_field_body) list

and struct_expr_body =
  | SEBident of module_path
  | SEBfunctor of mod_bound_id * module_type_body * struct_expr_body 
  | SEBstruct of mod_self_id * structure_body
  | SEBapply of struct_expr_body * struct_expr_body
      * Univ.constraints
  | SEBwith of struct_expr_body * with_declaration_body

and with_declaration_body =
    With_module_body of identifier list * module_path *
      struct_expr_body option * Univ.constraints
  | With_definition_body of  identifier list * constant_body
        
and module_body = 
    { mod_expr : struct_expr_body option;
      mod_type : struct_expr_body option;
      mod_constraints : Univ.constraints;
      mod_alias : substitution;
      mod_retroknowledge : action list}

and module_type_body = 
    { typ_expr : struct_expr_body;
      typ_strength : module_path option;
      typ_alias : substitution}

(* Substitutions *)

val fold_subst :
  (mod_self_id -> module_path -> 'a -> 'a) ->
  (mod_bound_id -> module_path -> 'a -> 'a) ->
  (module_path -> module_path -> 'a -> 'a) ->
  substitution -> 'a -> 'a

type 'a subst_fun = substitution -> 'a -> 'a

val empty_subst : substitution
val add_msid : mod_self_id -> module_path -> substitution -> substitution
val add_mbid : mod_bound_id -> module_path -> substitution -> substitution
val add_mp   : module_path -> module_path -> substitution -> substitution
val map_msid : mod_self_id -> module_path -> substitution
val map_mbid : mod_bound_id -> module_path -> substitution
val map_mp   : module_path -> module_path -> substitution

val subst_const_body : constant_body subst_fun
val subst_mind : mutual_inductive_body subst_fun
val subst_modtype : substitution -> module_type_body -> module_type_body
val subst_struct_expr :  substitution -> struct_expr_body -> struct_expr_body
val subst_structure : substitution -> structure_body -> structure_body
val subst_signature_msid :
  mod_self_id -> module_path -> structure_body -> structure_body

val join : substitution -> substitution -> substitution
val join_alias : substitution -> substitution -> substitution
val update_subst_alias : substitution -> substitution -> substitution
val update_subst : substitution -> substitution -> substitution
val subst_key : substitution -> substitution -> substitution
