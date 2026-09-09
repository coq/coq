(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

let universe_polymorphism_option_name = ["Universe"; "Polymorphism"]

let { Goptions.get = is_universe_polymorphism } =
  Goptions.declare_bool_option_and_ref ~key:universe_polymorphism_option_name ~value:false ()

let { Goptions.get = is_polymorphic_inductive_cumulativity } =
  Goptions.declare_bool_option_and_ref ~key:["Polymorphic"; "Inductive"; "Cumulativity"] ~value:true ()

let { Goptions.get = is_polymorphic_definitions_cumulativity } =
  Goptions.declare_bool_option_and_ref ~key:["Polymorphic"; "Definitions"; "Cumulativity"] ~value:true ()

let { Goptions.get = is_polymorphic_assumptions_cumulativity } =
  Goptions.declare_bool_option_and_ref ~key:["Polymorphic"; "Assumptions"; "Cumulativity"] ~value:false ()

let { Goptions.get = should_collapse_sort_variables  } =
  Goptions.declare_bool_option_and_ref ~key:["Collapse"; "Sorts"; "ToType"] ~value:true ()
let is_cumulative = function
  | PolyFlags.Inductive -> is_polymorphic_inductive_cumulativity()
  | PolyFlags.Assumption -> is_polymorphic_assumptions_cumulativity()
  | PolyFlags.Definition -> is_polymorphic_definitions_cumulativity()

let poly_for_ind mib =
  let indpoly = Declareops.inductive_is_polymorphic mib in
  let cumulative = Declareops.inductive_is_cumulative mib in
  let poly, cumulative =
    if not indpoly then
      if is_universe_polymorphism () then
        true, is_cumulative PolyFlags.Definition
      else false, false
    else indpoly, cumulative
  in PolyFlags.make ~univ_poly:poly ~cumulative ~collapse_sort_variables:true
