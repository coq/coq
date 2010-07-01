(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(**Untyped intermediate terms, after constr_expr and before constr

   Resolution of names, insertion of implicit arguments placeholder,
   and notations are done, but coercions, inference of implicit
   arguments and pattern-matching compilation are not. *)

open Util
open Names
open Sign
open Term
open Libnames
open Nametab

(**  The kind of patterns that occurs in "match ... with ... end"

     locs here refers to the ident's location, not whole pat the last
     argument of PatCstr is a possible alias ident for the pattern *)
type cases_pattern =
  | PatVar of loc * name
  | PatCstr of loc * constructor * cases_pattern list * name

val cases_pattern_loc : cases_pattern -> loc

type patvar = identifier

type rawsort = RProp of Term.contents | RType of Univ.universe option

type binder_kind = BProd | BLambda | BLetIn

type binding_kind = Lib.binding_kind = Explicit | Implicit

type quantified_hypothesis = AnonHyp of int | NamedHyp of identifier

type 'a explicit_bindings = (loc * quantified_hypothesis * 'a) list

type 'a bindings =
  | ImplicitBindings of 'a list
  | ExplicitBindings of 'a explicit_bindings
  | NoBindings

type 'a with_bindings = 'a * 'a bindings

type 'a cast_type =
  | CastConv of cast_kind * 'a
  | CastCoerce (** Cast to a base type (eg, an underlying inductive type) *)

type rawconstr =
  | RRef of (loc * global_reference)
  | RVar of (loc * identifier)
  | REvar of loc * existential_key * rawconstr list option
  | RPatVar of loc * (bool * patvar) (** Used for patterns only *)
  | RApp of loc * rawconstr * rawconstr list
  | RLambda of loc * name * binding_kind *  rawconstr * rawconstr
  | RProd of loc * name * binding_kind * rawconstr * rawconstr
  | RLetIn of loc * name * rawconstr * rawconstr
  | RCases of loc * case_style * rawconstr option * tomatch_tuples * cases_clauses
  | RLetTuple of loc * name list * (name * rawconstr option) *
      rawconstr * rawconstr
  | RIf of loc * rawconstr * (name * rawconstr option) * rawconstr * rawconstr
  | RRec of loc * fix_kind * identifier array * rawdecl list array *
      rawconstr array * rawconstr array
  | RSort of loc * rawsort
  | RHole of (loc * Evd.hole_kind)
  | RCast of loc * rawconstr * rawconstr cast_type
  | RDynamic of loc * Dyn.t
  | RNativeInt of loc * Native.Uint31.t
  | RNativeArr of loc * rawconstr * rawconstr array

and rawdecl = name * binding_kind * rawconstr option * rawconstr

and fix_recursion_order = RStructRec | RWfRec of rawconstr | RMeasureRec of rawconstr * rawconstr option

and fix_kind =
  | RFix of ((int option * fix_recursion_order) array * int)
  | RCoFix of int

and predicate_pattern =
    name * (loc * inductive * int * name list) option

and tomatch_tuple = (rawconstr * predicate_pattern)

and tomatch_tuples = tomatch_tuple list

and cases_clause = (loc * identifier list * cases_pattern list * rawconstr)

and cases_clauses = cases_clause list

val cases_predicate_names : tomatch_tuples -> name list

val map_rawconstr : (rawconstr -> rawconstr) -> rawconstr -> rawconstr

(* Ensure traversal from left to right *)
val map_rawconstr_left_to_right :
  (rawconstr -> rawconstr) -> rawconstr -> rawconstr

(*
val map_rawconstr_with_binders_loc : loc ->
  (identifier -> 'a -> identifier * 'a) ->
  ('a -> rawconstr -> rawconstr) -> 'a -> rawconstr -> rawconstr
*)

val occur_rawconstr : identifier -> rawconstr -> bool
val free_rawvars : rawconstr -> identifier list
val loc_of_rawconstr : rawconstr -> loc

(** Conversion from rawconstr to cases pattern, if possible
    
    Take the current alias as parameter, 
    @raise Not_found if translation is impossible *)

val cases_pattern_of_rawconstr : name -> rawconstr -> cases_pattern

val rawconstr_of_closed_cases_pattern : cases_pattern -> name * rawconstr

(** {6 Reduction expressions} *)

type 'a raw_red_flag = {
  rBeta : bool;
  rIota : bool;
  rZeta : bool;
  rDelta : bool; (** true = delta all but rConst; false = delta only on rConst*)
  rConst : 'a list
}

val all_flags : 'a raw_red_flag

type 'a or_var = ArgArg of 'a | ArgVar of identifier located

type occurrences_expr = bool * int or_var list

val all_occurrences_expr_but : int or_var list -> occurrences_expr
val no_occurrences_expr_but : int or_var list -> occurrences_expr
val all_occurrences_expr : occurrences_expr
val no_occurrences_expr : occurrences_expr

type 'a with_occurrences = occurrences_expr * 'a

type ('a,'b,'c) red_expr_gen =
  | Red of bool
  | Hnf
  | Simpl of 'c with_occurrences option
  | Cbv of 'b raw_red_flag
  | Lazy of 'b raw_red_flag
  | Unfold of 'b with_occurrences list
  | Fold of 'a list
  | Pattern of 'a with_occurrences list
  | ExtraRedExpr of string
  | CbvVm

type ('a,'b,'c) may_eval =
  | ConstrTerm of 'a
  | ConstrEval of ('a,'b,'c) red_expr_gen * 'a
  | ConstrContext of (loc * identifier) * 'a
  | ConstrTypeOf of 'a
