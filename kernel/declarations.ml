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

(** Projections are a particular kind of constant: 
    always transparent. *)

type projection_body = {
  proj_ind : MutInd.t;
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

type constant_universes =
  | Monomorphic_const of Univ.ContextSet.t
  | Polymorphic_const of Univ.AUContext.t

(** The [typing_flags] are instructions to the type-checker which
    modify its behaviour. The typing flags used in the type-checking
    of a constant are tracked in their {!constant_body} so that they
    can be displayed to the user. *)
type typing_flags = {
  check_guarded : bool; (** If [false] then fixed points and co-fixed
                            points are assumed to be total. *)
  check_universes : bool; (** If [false] universe constraints are not checked *)
  conv_oracle : Conv_oracle.oracle; (** Unfolding strategies for conversion *)
}

(* some contraints are in constant_constraints, some other may be in
 * the OpaqueDef *)
type constant_body = {
    const_hyps : Context.Named.t; (** New: younger hyp at top *)
    const_body : constant_def;
    const_type : types;
    const_body_code : Cemitcodes.to_patch_substituted option;
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

type record_body = (Id.t * Constant.t array * projection_body array) option

type regular_inductive_arity = {
  mind_user_arity : types;
  mind_sort : Sorts.t;
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

    mind_reloc_tbl :  Cbytecodes.reloc_table;
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

    mind_record : record_body option; (** The record information *)

    mind_finite : recursivity_kind;  (** Whether the type is inductive or coinductive *)

    mind_ntypes : int;  (** Number of types in the block *)

    mind_hyps : Context.Named.t;  (** Section hypotheses on which the block depends *)

    mind_nparams : int;  (** Number of expected parameters including non-uniform ones (i.e. length of mind_params_ctxt w/o let-in) *)

    mind_nparams_rec : int;  (** Number of recursively uniform (i.e. ordinary) parameters *)

    mind_params_ctxt : Context.Rel.t;  (** The context of parameters (includes let-in declaration) *)

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

open Mod_subst
open Util

module RelDecl = Context.Rel.Declaration

(** Operations concernings types in [Declarations] :
    [constant_body], [mutual_inductive_body], [module_body] ... *)

let safe_flags oracle = {
  check_guarded = true;
  check_universes = true;
  conv_oracle = oracle;
}

(** {6 Arities } *)

let subst_decl_arity f g sub ar =
  match ar with
  | RegularArity x ->
    let x' = f sub x in
      if x' == x then ar
      else RegularArity x'
  | TemplateArity x ->
    let x' = g sub x in
      if x' == x then ar
      else TemplateArity x'

let map_decl_arity f g = function
  | RegularArity a -> RegularArity (f a)
  | TemplateArity a -> TemplateArity (g a)

let hcons_template_arity ar =
  { template_param_levels = ar.template_param_levels;
      (* List.smartmap (Option.smartmap Univ.hcons_univ_level) ar.template_param_levels; *)
    template_level = Univ.hcons_univ ar.template_level }

(** {6 Constants } *)

let constant_is_polymorphic cb =
  match cb.const_universes with
  | Monomorphic_const _ -> false
  | Polymorphic_const _ -> true

let constant_has_body cb = match cb.const_body with
  | Undef _ -> false
  | Def _ | OpaqueDef _ -> true

let constant_polymorphic_context cb =
  match cb.const_universes with
  | Monomorphic_const _ -> Univ.AUContext.empty
  | Polymorphic_const ctx -> ctx

let is_opaque cb = match cb.const_body with
  | OpaqueDef _ -> true
  | Undef _ | Def _ -> false

(** {7 Constant substitutions } *)

let subst_rel_declaration sub =
  RelDecl.map_constr (subst_mps sub)

let subst_rel_context sub = List.smartmap (subst_rel_declaration sub)

let subst_const_type sub arity =
  if is_empty_subst sub then arity
  else subst_mps sub arity

(** No need here to check for physical equality after substitution,
    at least for Def due to the delayed substitution [subst_constr_subst]. *)
let subst_const_def sub def = match def with
  | Undef _ -> def
  | Def c -> Def (subst_constr sub c)
  | OpaqueDef o -> OpaqueDef (Opaqueproof.subst_opaque sub o)

let subst_const_proj sub pb =
  { pb with proj_ind = subst_mind sub pb.proj_ind;
    proj_type = subst_mps sub pb.proj_type;
    proj_body = subst_const_type sub pb.proj_body }

let subst_const_body sub cb =
  assert (List.is_empty cb.const_hyps); (* we're outside sections *)
  if is_empty_subst sub then cb
  else
    let body' = subst_const_def sub cb.const_body in
    let type' = subst_const_type sub cb.const_type in
    let proj' = Option.smartmap (subst_const_proj sub) cb.const_proj in
    if body' == cb.const_body && type' == cb.const_type
      && proj' == cb.const_proj then cb
    else
      { const_hyps = [];
        const_body = body';
        const_type = type';
        const_proj = proj';
        const_body_code =
          Option.map (Cemitcodes.subst_to_patch_subst sub) cb.const_body_code;
        const_universes = cb.const_universes;
        const_inline_code = cb.const_inline_code;
        const_typing_flags = cb.const_typing_flags }

(** {7 Hash-consing of constants } *)

(** This hash-consing is currently quite partial : we only
    share internal fields (e.g. constr), and not the records
    themselves. But would it really bring substantial gains ? *)

let hcons_rel_decl =
  RelDecl.map_name Names.Name.hcons %> RelDecl.map_value Constr.hcons %> RelDecl.map_type Constr.hcons

let hcons_rel_context l = List.smartmap hcons_rel_decl l

let hcons_const_def = function
  | Undef inl -> Undef inl
  | Def l_constr ->
    let constr = force_constr l_constr in
    Def (from_val (Constr.hcons constr))
  | OpaqueDef _ as x -> x (* hashconsed when turned indirect *)

let hcons_const_universes cbu =
  match cbu with
  | Monomorphic_const ctx ->
    Monomorphic_const (Univ.hcons_universe_context_set ctx)
  | Polymorphic_const ctx ->
    Polymorphic_const (Univ.hcons_abstract_universe_context ctx)

let hcons_const_body cb =
  { cb with
    const_body = hcons_const_def cb.const_body;
    const_type = Constr.hcons cb.const_type;
    const_universes = hcons_const_universes cb.const_universes }

(** {6 Inductive types } *)

let eq_recarg r1 r2 = match r1, r2 with
| Norec, Norec -> true
| Mrec i1, Mrec i2 -> Names.eq_ind i1 i2
| Imbr i1, Imbr i2 -> Names.eq_ind i1 i2
| _ -> false

let subst_recarg sub r = match r with
  | Norec -> r
  | Mrec (kn,i) ->
    let kn' = subst_mind sub kn in
    if kn==kn' then r else Mrec (kn',i)
  | Imbr (kn,i) ->
    let kn' = subst_mind sub kn in
    if kn==kn' then r else Imbr (kn',i)

let mk_norec = Rtree.mk_node Norec [||]

let mk_paths r recargs =
  Rtree.mk_node r
    (Array.map (fun l -> Rtree.mk_node Norec (Array.of_list l)) recargs)

let dest_recarg p = fst (Rtree.dest_node p)

(* dest_subterms returns the sizes of each argument of each constructor of
   an inductive object of size [p]. This should never be done for Norec,
   because the number of sons does not correspond to the number of
   constructors.
 *)
let dest_subterms p =
  let (ra,cstrs) = Rtree.dest_node p in
  assert (match ra with Norec -> false | _ -> true);
  Array.map (fun t -> Array.to_list (snd (Rtree.dest_node t))) cstrs

let recarg_length p j =
  let (_,cstrs) = Rtree.dest_node p in
  Array.length (snd (Rtree.dest_node cstrs.(j-1)))

let subst_wf_paths sub p = Rtree.smartmap (subst_recarg sub) p

(** {7 Substitution of inductive declarations } *)

let subst_regular_ind_arity sub s =
  let uar' = subst_mps sub s.mind_user_arity in
    if uar' == s.mind_user_arity then s
    else { mind_user_arity = uar'; mind_sort = s.mind_sort }

let subst_template_ind_arity sub s = s

(* FIXME records *)
let subst_ind_arity =
  subst_decl_arity subst_regular_ind_arity subst_template_ind_arity

let subst_mind_packet sub mbp =
  { mind_consnames = mbp.mind_consnames;
    mind_consnrealdecls = mbp.mind_consnrealdecls;
    mind_consnrealargs = mbp.mind_consnrealargs;
    mind_typename = mbp.mind_typename;
    mind_nf_lc = Array.smartmap (subst_mps sub) mbp.mind_nf_lc;
    mind_arity_ctxt = subst_rel_context sub mbp.mind_arity_ctxt;
    mind_arity = subst_ind_arity sub mbp.mind_arity;
    mind_user_lc = Array.smartmap (subst_mps sub) mbp.mind_user_lc;
    mind_nrealargs = mbp.mind_nrealargs;
    mind_nrealdecls = mbp.mind_nrealdecls;
    mind_kelim = mbp.mind_kelim;
    mind_recargs = subst_wf_paths sub mbp.mind_recargs (*wf_paths*);
    mind_nb_constant = mbp.mind_nb_constant;
    mind_nb_args = mbp.mind_nb_args;
    mind_reloc_tbl = mbp.mind_reloc_tbl }

let subst_mind_record sub (id, ps, pb as r) =
  let ps' = Array.smartmap (subst_constant sub) ps in
  let pb' = Array.smartmap (subst_const_proj sub) pb in
    if ps' == ps && pb' == pb then r
    else (id, ps', pb')

let subst_mind_body sub mib =
  { mind_record = Option.smartmap (Option.smartmap (subst_mind_record sub)) mib.mind_record ;
    mind_finite = mib.mind_finite ;
    mind_ntypes = mib.mind_ntypes ;
    mind_hyps = (match mib.mind_hyps with [] -> [] | _ -> assert false);
    mind_nparams = mib.mind_nparams;
    mind_nparams_rec = mib.mind_nparams_rec;
    mind_params_ctxt =
      Context.Rel.map (subst_mps sub) mib.mind_params_ctxt;
    mind_packets = Array.smartmap (subst_mind_packet sub) mib.mind_packets ;
    mind_universes = mib.mind_universes;
    mind_private = mib.mind_private;
    mind_typing_flags = mib.mind_typing_flags;
  }

let inductive_polymorphic_context mib =
  match mib.mind_universes with
  | Monomorphic_ind _ -> Univ.AUContext.empty
  | Polymorphic_ind ctx -> ctx
  | Cumulative_ind cumi -> Univ.ACumulativityInfo.univ_context cumi

let inductive_is_polymorphic mib =
  match mib.mind_universes with
  | Monomorphic_ind _ -> false
  | Polymorphic_ind ctx -> true
  | Cumulative_ind cumi -> true

let inductive_is_cumulative mib =
  match mib.mind_universes with
  | Monomorphic_ind _ -> false
  | Polymorphic_ind ctx -> false
  | Cumulative_ind cumi -> true

(** {6 Hash-consing of inductive declarations } *)

let hcons_regular_ind_arity a =
  { mind_user_arity = Constr.hcons a.mind_user_arity;
    mind_sort = Sorts.hcons a.mind_sort }

(** Just as for constants, this hash-consing is quite partial *)

let hcons_ind_arity =
  map_decl_arity hcons_regular_ind_arity hcons_template_arity

(** Substitution of inductive declarations *)

let hcons_mind_packet oib =
  let user = Array.smartmap Constr.hcons oib.mind_user_lc in
  let nf = Array.smartmap Constr.hcons oib.mind_nf_lc in
  (* Special optim : merge [mind_user_lc] and [mind_nf_lc] if possible *)
  let nf = if Array.equal (==) user nf then user else nf in
  { oib with
    mind_typename = Names.Id.hcons oib.mind_typename;
    mind_arity_ctxt = hcons_rel_context oib.mind_arity_ctxt;
    mind_arity = hcons_ind_arity oib.mind_arity;
    mind_consnames = Array.smartmap Names.Id.hcons oib.mind_consnames;
    mind_user_lc = user;
    mind_nf_lc = nf }

let hcons_mind_universes miu =
  match miu with
  | Monomorphic_ind ctx -> Monomorphic_ind (Univ.hcons_universe_context_set ctx)
  | Polymorphic_ind ctx -> Polymorphic_ind (Univ.hcons_abstract_universe_context ctx)
  | Cumulative_ind cui -> Cumulative_ind (Univ.hcons_abstract_cumulativity_info cui)

let hcons_mind mib =
  { mib with
    mind_packets = Array.smartmap hcons_mind_packet mib.mind_packets;
    mind_params_ctxt = hcons_rel_context mib.mind_params_ctxt;
    mind_universes = hcons_mind_universes mib.mind_universes }

(** Hashconsing of modules *)

let hcons_functorize hty he hself f = match f with
| NoFunctor e ->
  let e' = he e in
  if e == e' then f else NoFunctor e'
| MoreFunctor (mid, ty, nf) ->
  (** FIXME *)
  let mid' = mid in
  let ty' = hty ty in
  let nf' = hself nf in
  if mid == mid' && ty == ty' && nf == nf' then f
  else MoreFunctor (mid, ty', nf')

let hcons_module_alg_expr me = me

let rec hcons_structure_field_body sb = match sb with
| SFBconst cb ->
  let cb' = hcons_const_body cb in
  if cb == cb' then sb else SFBconst cb'
| SFBmind mib ->
  let mib' = hcons_mind mib in
  if mib == mib' then sb else SFBmind mib'
| SFBmodule mb ->
  let mb' = hcons_module_body mb in
  if mb == mb' then sb else SFBmodule mb'
| SFBmodtype mb ->
  let mb' = hcons_module_type mb in
  if mb == mb' then sb else SFBmodtype mb'

and hcons_structure_body sb =
  (** FIXME *)
  let map (l, sfb as fb) =
    let l' = Names.Label.hcons l in
    let sfb' = hcons_structure_field_body sfb in
    if l == l' && sfb == sfb' then fb else (l', sfb')
  in
  List.smartmap map sb

and hcons_module_signature ms =
  hcons_functorize hcons_module_type hcons_structure_body hcons_module_signature ms

and hcons_module_expression me =
  hcons_functorize hcons_module_type hcons_module_alg_expr hcons_module_expression me

and hcons_module_implementation mip = match mip with
| Abstract -> Abstract
| Algebraic me ->
  let me' = hcons_module_expression me in
  if me == me' then mip else Algebraic me'
| Struct ms ->
  let ms' = hcons_module_signature ms in
  if ms == ms' then mip else Struct ms
| FullStruct -> FullStruct

and hcons_generic_module_body :
  'a. ('a -> 'a) -> 'a generic_module_body -> 'a generic_module_body =
  fun hcons_impl mb ->
  let mp' = mb.mod_mp in
  let expr' = hcons_impl mb.mod_expr in
  let type' = hcons_module_signature mb.mod_type in
  let type_alg' = mb.mod_type_alg in
  let constraints' = Univ.hcons_universe_context_set mb.mod_constraints in
  let delta' = mb.mod_delta in
  let retroknowledge' = mb.mod_retroknowledge in

  if
    mb.mod_mp == mp' &&
    mb.mod_expr == expr' &&
    mb.mod_type == type' &&
    mb.mod_type_alg == type_alg' &&
    mb.mod_constraints == constraints' &&
    mb.mod_delta == delta' &&
    mb.mod_retroknowledge == retroknowledge'
  then mb
  else {
    mod_mp = mp';
    mod_expr = expr';
    mod_type = type';
    mod_type_alg = type_alg';
    mod_constraints = constraints';
    mod_delta = delta';
    mod_retroknowledge = retroknowledge';
  }

and hcons_module_body mb =
  hcons_generic_module_body hcons_module_implementation mb

and hcons_module_type mb =
  hcons_generic_module_body (fun () -> ()) mb
