(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Globnames
open Term
open Misctypes

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

type constr_under_binders = Id.t list * constr

(** Types of substitutions with or w/o bound variables *)

type patvar_map = constr Id.Map.t
type extended_patvar_map = constr_under_binders Id.Map.t

(** {5 Patterns} *)

type case_info_pattern =
    { cip_style : case_style;
      cip_ind : inductive option;
      cip_ind_tags : bool list option; (** indicates LetIn/Lambda in arity *)
      cip_extensible : bool (** does this match end with _ => _ ? *) }

type constr_pattern =
  | PRef of global_reference
  | PVar of Id.t
  | PEvar of existential_key * constr_pattern array
  | PRel of int
  | PApp of constr_pattern * constr_pattern array
  | PSoApp of patvar * constr_pattern list
  | PProj of projection * constr_pattern
  | PLambda of Name.t * constr_pattern * constr_pattern
  | PProd of Name.t * constr_pattern * constr_pattern
  | PLetIn of Name.t * constr_pattern * constr_pattern
  | PSort of glob_sort
  | PMeta of patvar option
  | PIf of constr_pattern * constr_pattern * constr_pattern
  | PCase of case_info_pattern * constr_pattern * constr_pattern *
      (int * bool list * constr_pattern) list (** index of constructor, nb of args *)
  | PFix of fixpoint
  | PCoFix of cofixpoint

(** Nota : in a [PCase], the array of branches might be shorter than
    expected, denoting the use of a final "_ => _" branch *)
