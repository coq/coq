(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type t = {
  univ_poly : bool;
  collapse_sort_variables : bool;
  cumulative : bool;
  solve_term_variables : bool;
}

let make ~univ_poly ~collapse_sort_variables ~cumulative =
  if cumulative && not univ_poly then
    CErrors.user_err Pp.(str "Cannot have cumulative but not universe polymorphic constructions");
  if not collapse_sort_variables && not univ_poly then
    CErrors.user_err Pp.(str "Sort metavariables must be collapsed to Type in universe monomorphic constructions");
  { collapse_sort_variables; univ_poly; cumulative; solve_term_variables = false }

let default = { collapse_sort_variables = true; univ_poly = false; cumulative = false; solve_term_variables = false }
let of_univ_poly b = { default with univ_poly = b }

let collapse_sort_variables x = x.collapse_sort_variables
let univ_poly x = x.univ_poly
let cumulative x = x.cumulative

let set_solve_term_variables x = { x with solve_term_variables = true }
let solve_term_variables x = x.solve_term_variables

let pr f =
  let open Pp in
  str "{ univ_poly = " ++ bool f.univ_poly ++ spc () ++
  str "; cumulative = " ++ bool f.cumulative ++ spc () ++
  str "; collapse_sort_variables = " ++ bool f.collapse_sort_variables ++ spc () ++
  str "}"

(* Used to have distinguished default behaviors when treating assumptions/axioms, definitions or inductives *)
type construction_kind =
  Assumption | Definition | Inductive
