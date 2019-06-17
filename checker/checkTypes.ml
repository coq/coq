(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Term
open Constr
open Declarations
open Reduction
open Environ

(* Polymorphic arities utils *)

let check_kind env ar u =
  match Constr.kind (snd (dest_prod env ar)) with
  | Sort (Type u') when Univ.Universe.equal u' (Univ.Universe.make u) -> ()
  | _ -> failwith "not the correct sort"

let check_polymorphic_arity env params par =
  let pl = par.template_param_levels in
  let rec check_p env pl params =
    let open Context.Rel.Declaration in
    match pl, params with
        Some u::pl, LocalAssum (na,ty)::params ->
          check_kind env ty u;
          check_p (push_rel (LocalAssum (na,ty)) env) pl params
      | None::pl,d::params -> check_p (push_rel d env) pl params
      | [], _ -> ()
      | _ -> failwith "check_poly: not the right number of params" in
  check_p env pl (List.rev params)
