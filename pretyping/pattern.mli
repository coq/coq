(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
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
      cip_extensible : bool (** does this match end with _ => _ ? *) }

type 'i uninstantiated_pattern =
  | PGenarg : Genarg.glob_generic_argument -> [ `uninstantiated ] uninstantiated_pattern

type 'i constr_pattern_r =
  | PRef of GlobRef.t
  | PVar of Id.t
  | PEvar of (Evar.t * 'i constr_pattern_r list)
  | PRel of int
  | PApp of 'i constr_pattern_r * 'i constr_pattern_r array
  | PSoApp of patvar * 'i constr_pattern_r list
  | PProj of Projection.t * 'i constr_pattern_r
  | PLambda of Name.t * 'i constr_pattern_r * 'i constr_pattern_r
  | PProd of Name.t * 'i constr_pattern_r * 'i constr_pattern_r
  | PLetIn of Name.t * 'i constr_pattern_r * 'i constr_pattern_r option * 'i constr_pattern_r
  | PSort of Sorts.family
  | PMeta of patvar option
  | PIf of 'i constr_pattern_r * 'i constr_pattern_r * 'i constr_pattern_r
  | PCase of case_info_pattern * (Name.t array * 'i constr_pattern_r) option * 'i constr_pattern_r *
      (int * Name.t array * 'i constr_pattern_r) list (** index of constructor, nb of args *)
  | PFix of (int array * int) * (Name.t array * 'i constr_pattern_r array * 'i constr_pattern_r array)
  | PCoFix of int * (Name.t array * 'i constr_pattern_r array * 'i constr_pattern_r array)
  | PInt of Uint63.t
  | PFloat of Float64.t
  | PString of Pstring.t
  | PArray of 'i constr_pattern_r array * 'i constr_pattern_r * 'i constr_pattern_r
  | PUninstantiated of 'i uninstantiated_pattern

type constr_pattern = [ `any ] constr_pattern_r

(** Nota : in a [PCase], the array of branches might be shorter than
    expected, denoting the use of a final "_ => _" branch *)

type _ pattern_kind =
  | Any
  | Uninstantiated : [`uninstantiated] pattern_kind
