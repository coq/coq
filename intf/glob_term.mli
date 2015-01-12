(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
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
type cases_pattern =
  | PatVar of Loc.t * Name.t
  | PatCstr of Loc.t * constructor * cases_pattern list * Name.t
      (** [PatCstr(p,C,l,x)] = "|'C' 'l' as 'x'" *)

type glob_constr =
  | GRef of (Loc.t * global_reference * glob_level list option)
  | GVar of (Loc.t * Id.t)
  | GEvar of Loc.t * existential_name * (Id.t * glob_constr) list
  | GPatVar of Loc.t * (bool * patvar) (** Used for patterns only *)
  | GApp of Loc.t * glob_constr * glob_constr list
  | GLambda of Loc.t * Name.t * binding_kind *  glob_constr * glob_constr
  | GProd of Loc.t * Name.t * binding_kind * glob_constr * glob_constr
  | GLetIn of Loc.t * Name.t * glob_constr * glob_constr
  | GCases of Loc.t * case_style * glob_constr option * tomatch_tuples * cases_clauses
      (** [GCases(l,style,r,tur,cc)] = "match 'tur' return 'r' with 'cc'" (in
	  [MatchStyle]) *)
  | GLetTuple of Loc.t * Name.t list * (Name.t * glob_constr option) *
      glob_constr * glob_constr
  | GIf of Loc.t * glob_constr * (Name.t * glob_constr option) * glob_constr * glob_constr
  | GRec of Loc.t * fix_kind * Id.t array * glob_decl list array *
      glob_constr array * glob_constr array
  | GSort of Loc.t * glob_sort
  | GHole of (Loc.t * Evar_kinds.t * intro_pattern_naming_expr * Genarg.glob_generic_argument option)
  | GCast of Loc.t * glob_constr * glob_constr cast_type

and glob_decl = Name.t * binding_kind * glob_constr option * glob_constr

and fix_recursion_order =
  | GStructRec
  | GWfRec of glob_constr
  | GMeasureRec of glob_constr * glob_constr option

and fix_kind =
  | GFix of ((int option * fix_recursion_order) array * int)
  | GCoFix of int

and predicate_pattern =
    Name.t * (Loc.t * inductive * Name.t list) option
      (** [(na,id)] = "as 'na' in 'id'" where if [id] is [Some(l,I,k,args)]. *)

and tomatch_tuple = (glob_constr * predicate_pattern)

and tomatch_tuples = tomatch_tuple list

and cases_clause = (Loc.t * Id.t list * cases_pattern list * glob_constr)
(** [(p,il,cl,t)] = "|'cl' => 't'". Precondition: the free variables
    of [t] are members of [il]. *)
and cases_clauses = cases_clause list

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
