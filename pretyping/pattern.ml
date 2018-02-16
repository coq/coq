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

(** {5 Patterns} *)

(** Cases pattern variables *)
type patvar = Id.t

type case_info_pattern =
    { cip_style : Constr.case_style;
      cip_ind : inductive option;
      cip_ind_tags : bool list option; (** indicates LetIn/Lambda in arity *)
      cip_extensible : bool (** does this match end with _ => _ ? *) }

type constr_pattern =
  | PRef of GlobRef.t
  | PVar of Id.t
  | PEvar of Evar.t * constr_pattern array
  | PRel of int
  | PApp of constr_pattern * constr_pattern array
  | PSoApp of patvar * constr_pattern list
  | PProj of Projection.t * constr_pattern
  | PLambda of Name.t * constr_pattern * constr_pattern
  | PProd of Name.t * constr_pattern * constr_pattern
  | PLetIn of Name.t * constr_pattern * constr_pattern option * constr_pattern
  | PSort of Glob_term.glob_sort
  | PMeta of patvar option
  | PIf of constr_pattern * constr_pattern * constr_pattern
  | PCase of case_info_pattern * constr_pattern * constr_pattern *
      (int * bool list * constr_pattern) list (** index of constructor, nb of args *)
  | PFix of (int array * int) * (Name.t array * constr_pattern array * constr_pattern array)
  | PCoFix of int * (Name.t array * constr_pattern array * constr_pattern array)
  | PInt of Uint63.t

(** Nota : in a [PCase], the array of branches might be shorter than
    expected, denoting the use of a final "_ => _" branch *)
