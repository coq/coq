(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Untyped intermediate terms *)

(** [glob_constr] comes after [constr_expr] and before [constr].

   Resolution of names, insertion of implicit arguments placeholder,
   and notations are done, but coercions, inference of implicit
   arguments and pattern-matching compilation are not. *)

open Pp
open Names
open Sign
open Term
open Libnames
open Decl_kinds
open Misctypes

(**  The kind of patterns that occurs in "match ... with ... end"

     locs here refers to the ident's location, not whole pat *)
type cases_pattern =
  | PatVar of loc * name
  | PatCstr of loc * constructor * cases_pattern list * name
      (** [PatCstr(p,C,l,x)] = "|'C' 'l' as 'x'" *)

type glob_constr =
  | GRef of (loc * global_reference)
  | GVar of (loc * identifier)
  | GEvar of loc * existential_key * glob_constr list option
  | GPatVar of loc * (bool * patvar) (** Used for patterns only *)
  | GApp of loc * glob_constr * glob_constr list
  | GLambda of loc * name * binding_kind *  glob_constr * glob_constr
  | GProd of loc * name * binding_kind * glob_constr * glob_constr
  | GLetIn of loc * name * glob_constr * glob_constr
  | GCases of loc * case_style * glob_constr option * tomatch_tuples * cases_clauses
      (** [GCases(l,style,r,tur,cc)] = "match 'tur' return 'r' with 'cc'" (in
	  [MatchStyle]) *)

  | GLetTuple of loc * name list * (name * glob_constr option) *
      glob_constr * glob_constr
  | GIf of loc * glob_constr * (name * glob_constr option) * glob_constr * glob_constr
  | GRec of loc * fix_kind * identifier array * glob_decl list array *
      glob_constr array * glob_constr array
  | GSort of loc * glob_sort
  | GHole of (loc * Evar_kinds.t)
  | GCast of loc * glob_constr * glob_constr cast_type

and glob_decl = name * binding_kind * glob_constr option * glob_constr

and fix_recursion_order = GStructRec | GWfRec of glob_constr | GMeasureRec of glob_constr * glob_constr option

and fix_kind =
  | GFix of ((int option * fix_recursion_order) array * int)
  | GCoFix of int

and predicate_pattern =
    name * (loc * inductive * name list) option
      (** [(na,id)] = "as 'na' in 'id'" where if [id] is [Some(l,I,k,args)]. *)

and tomatch_tuple = (glob_constr * predicate_pattern)

and tomatch_tuples = tomatch_tuple list

and cases_clause = (loc * identifier list * cases_pattern list * glob_constr)
(** [(p,il,cl,t)] = "|'cl' as 'il' => 't'" *)

and cases_clauses = cases_clause list
