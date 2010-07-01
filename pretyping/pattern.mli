(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** This module defines the type of pattern used for pattern-matching
    terms in tatics *)

open Pp
open Names
open Sign
open Term
open Environ
open Libnames
open Nametab
open Rawterm
open Mod_subst

(** {5 Maps of pattern variables} *)

(** Type [constr_under_binders] is for representing the term resulting
    of a matching. Matching can return terms defined in a some context
    of named binders; in the context, variable names are ordered by
    (<) and referred to by index in the term Thanks to the canonical
    ordering, a matching problem like

    [match ... with [(fun x y => ?p,fun y x => ?p)] => [forall x y => p]]

    will be accepted. Thanks to the reference by index, a matching
    problem like

    [match ... with [(fun x => ?p)] => [forall x => p]]

    will work even if [x] is also the name of an existing goal
    variable.

    Note: we do not keep types in the signature. Besides simplicity,
    the main reason is that it would force to close the signature over
    binders that occur only in the types of effective binders but not
    in the term itself (e.g. for a term [f x] with [f:A -> True] and
    [x:A]).

    On the opposite side, by not keeping the types, we loose
    opportunity to propagate type informations which otherwise would
    not be inferable, as e.g. when matching [forall x, x = 0] with
    pattern [forall x, ?h = 0] and using the solution "x|-h:=x" in
    expression [forall x, h = x] where nothing tells how the type of x
    could be inferred. We also loose the ability of typing ltac
    variables before calling the right-hand-side of ltac matching clauses. *)

type constr_under_binders = identifier list * constr

(** Types of substitutions with or w/o bound variables *)

type patvar_map = (patvar * constr) list
type extended_patvar_map = (patvar * constr_under_binders) list

(** {5 Patterns} *)

type constr_pattern =
  | PRef of global_reference
  | PVar of identifier
  | PEvar of existential_key * constr_pattern array
  | PRel of int
  | PApp of constr_pattern * constr_pattern array
  | PSoApp of patvar * constr_pattern list
  | PLambda of name * constr_pattern * constr_pattern
  | PProd of name * constr_pattern * constr_pattern
  | PLetIn of name * constr_pattern * constr_pattern
  | PSort of rawsort
  | PMeta of patvar option
  | PIf of constr_pattern * constr_pattern * constr_pattern
  | PCase of (case_style * int array * inductive option * (int * int) option)
      * constr_pattern * constr_pattern * constr_pattern array
  | PFix of fixpoint
  | PCoFix of cofixpoint
  | PNativeInt of Native.Uint31.t
  | PNativeArr of constr_pattern * constr_pattern array 

(** {5 Functions on patterns} *)

val occur_meta_pattern : constr_pattern -> bool

val subst_pattern : substitution -> constr_pattern -> constr_pattern

exception BoundPattern

(** [head_pattern_bound t] extracts the head variable/constant of the
   type [t] or raises [BoundPattern] (even if a sort); it raises an anomaly
   if [t] is an abstraction, an interger, an array *)

val head_pattern_bound : constr_pattern -> global_reference

(** [head_of_constr_reference c] assumes [r] denotes a reference and
   returns its label; raises an anomaly otherwise *)

val head_of_constr_reference : Term.constr -> global_reference

(** [pattern_of_constr c] translates a term [c] with metavariables into
   a pattern; currently, no destructor (Cases, Fix, Cofix) and no
   existential variable are allowed in [c] *)

val pattern_of_constr : Evd.evar_map -> constr -> named_context * constr_pattern

(** [pattern_of_rawconstr l c] translates a term [c] with metavariables into
   a pattern; variables bound in [l] are replaced by the pattern to which they
    are bound *)

val pattern_of_rawconstr : rawconstr ->
      patvar list * constr_pattern

val instantiate_pattern :
  Evd.evar_map -> (identifier * (identifier list * constr)) list ->
  constr_pattern -> constr_pattern

val lift_pattern : int -> constr_pattern -> constr_pattern
