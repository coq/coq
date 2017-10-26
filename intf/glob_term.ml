(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Untyped intermediate terms *)

(** [glob_constr] comes after [constr_expr] and before [constr].

   Resolution of names, insertion of implicit arguments placeholder,
   and notations are done, but coercions, inference of implicit
   arguments and pattern-matching compilation are not. *)

open Names
open Globnames
open Decl_kinds
open Misctypes

type existential_name = Id.t

(**  The kind of patterns that occurs in "match ... with ... end"

     locs here refers to the ident's location, not whole pat *)
type 'a cases_pattern_r =
  | PatVar  of Name.t
  | PatCstr of constructor * 'a cases_pattern_g list * Name.t
      (** [PatCstr(p,C,l,x)] = "|'C' 'l' as 'x'" *)
and 'a cases_pattern_g = ('a cases_pattern_r, 'a) DAst.t

type cases_pattern = [ `any ] cases_pattern_g

(** Representation of an internalized (or in other words globalized) term. *)
type 'a glob_constr_r =
  | GRef of global_reference * glob_level list option
      (** An identifier that represents a reference to an object defined
          either in the (global) environment or in the (local) context. *)
  | GVar of Id.t
      (** An identifier that cannot be regarded as "GRef".
          Bound variables are typically represented this way. *)
  | GEvar   of existential_name * (Id.t * 'a glob_constr_g) list
  | GPatVar of Evar_kinds.matching_var_kind (** Used for patterns only *)
  | GApp    of 'a glob_constr_g * 'a glob_constr_g list
  | GLambda of Name.t * binding_kind *  'a glob_constr_g * 'a glob_constr_g
  | GProd   of Name.t * binding_kind * 'a glob_constr_g * 'a glob_constr_g
  | GLetIn  of Name.t * 'a glob_constr_g * 'a glob_constr_g option * 'a glob_constr_g
  | GCases  of case_style * 'a glob_constr_g option * 'a tomatch_tuples_g * 'a cases_clauses_g
      (** [GCases(style,r,tur,cc)] = "match 'tur' return 'r' with 'cc'" (in [MatchStyle]) *)
  | GLetTuple of Name.t list * (Name.t * 'a glob_constr_g option) * 'a glob_constr_g * 'a glob_constr_g
  | GIf   of 'a glob_constr_g * (Name.t * 'a glob_constr_g option) * 'a glob_constr_g * 'a glob_constr_g
  | GRec  of 'a fix_kind_g * Id.t array * 'a glob_decl_g list array *
             'a glob_constr_g array * 'a glob_constr_g array
  | GSort of glob_sort
  | GHole of Evar_kinds.t * intro_pattern_naming_expr * Genarg.glob_generic_argument option
  | GCast of 'a glob_constr_g * 'a glob_constr_g cast_type
and 'a glob_constr_g = ('a glob_constr_r, 'a) DAst.t

and 'a glob_decl_g = Name.t * binding_kind * 'a glob_constr_g option * 'a glob_constr_g

and 'a fix_recursion_order_g =
  | GStructRec
  | GWfRec of 'a glob_constr_g
  | GMeasureRec of 'a glob_constr_g * 'a glob_constr_g option

and 'a fix_kind_g =
  | GFix of ((int option * 'a fix_recursion_order_g) array * int)
  | GCoFix of int

and 'a predicate_pattern_g =
    Name.t * (inductive * Name.t list) Loc.located option
      (** [(na,id)] = "as 'na' in 'id'" where if [id] is [Some(l,I,k,args)]. *)

and 'a tomatch_tuple_g = ('a glob_constr_g * 'a predicate_pattern_g)

and 'a tomatch_tuples_g = 'a tomatch_tuple_g list

and 'a cases_clause_g = (Id.t list * 'a cases_pattern_g list * 'a glob_constr_g) Loc.located
(** [(p,il,cl,t)] = "|'cl' => 't'". Precondition: the free variables
    of [t] are members of [il]. *)
and 'a cases_clauses_g = 'a cases_clause_g list

type glob_constr = [ `any ] glob_constr_g
type tomatch_tuple = [ `any ] tomatch_tuple_g
type tomatch_tuples = [ `any ] tomatch_tuples_g
type cases_clause = [ `any ] cases_clause_g
type cases_clauses = [ `any ] cases_clauses_g
type glob_decl = [ `any ] glob_decl_g
type fix_kind = [ `any ] fix_kind_g
type predicate_pattern = [ `any ] predicate_pattern_g
type fix_recursion_order = [ `any ] fix_recursion_order_g

type any_glob_constr = AnyGlobConstr : 'r glob_constr_g -> any_glob_constr

type 'a extended_glob_local_binder_r =
  | GLocalAssum   of Name.t * binding_kind * 'a glob_constr_g
  | GLocalDef     of Name.t * binding_kind * 'a glob_constr_g * 'a glob_constr_g option
  | GLocalPattern of ('a cases_pattern_g * Id.t list) * Id.t * binding_kind * 'a glob_constr_g
and 'a extended_glob_local_binder_g = ('a extended_glob_local_binder_r, 'a) DAst.t

type extended_glob_local_binder = [ `any ] extended_glob_local_binder_g

(** A globalised term together with a closure representing the value
    of its free variables. Intended for use when these variables are taken
    from the Ltac environment. *)
type closure = {
  idents:Id.t Id.Map.t;
  typed: Pattern.constr_under_binders Id.Map.t ;
  untyped:closed_glob_constr Id.Map.t }
and closed_glob_constr = {
  closure: closure;
  term: glob_constr }

(** Ltac variable maps *)
type var_map = Pattern.constr_under_binders Id.Map.t
type uconstr_var_map = closed_glob_constr Id.Map.t
type unbound_ltac_var_map = Geninterp.Val.t Id.Map.t

type ltac_var_map = {
  ltac_constrs : var_map;
  (** Ltac variables bound to constrs *)
  ltac_uconstrs : uconstr_var_map;
  (** Ltac variables bound to untyped constrs *)
  ltac_idents: Id.t Id.Map.t;
  (** Ltac variables bound to identifiers *)
  ltac_genargs : unbound_ltac_var_map;
  (** Ltac variables bound to other kinds of arguments *)
}
