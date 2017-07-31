(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Util
open Misctypes
open Tac2intern
open Tac2expr
open Tac2core

(** Syntactic quoting of expressions. *)

let dummy_loc = Loc.make_loc (-1, -1)

let constructor ?loc kn args =
  let loc = Option.default dummy_loc loc in
  let cst = CTacCst (loc, AbsKn (Other kn)) in
  if List.is_empty args then cst
  else CTacApp (loc, cst, args)

let of_pair ?loc (e1, e2) =
  let loc = Option.default dummy_loc loc in
  CTacApp (loc, CTacCst (loc, AbsKn (Tuple 2)), [e1; e2])

let of_int ?loc n =
  CTacAtm (Loc.tag ?loc (AtmInt n))

let inj_wit ?loc wit x =
  let loc = Option.default dummy_loc loc in
  CTacExt (loc, Genarg.in_gen (Genarg.rawwit wit) x)

let of_variable ?loc id =
  let qid = Libnames.qualid_of_ident id in
  if Tac2env.is_constructor qid then
    CErrors.user_err ?loc (str "Invalid identifier")
  else CTacRef (RelId (Loc.tag ?loc qid))

let of_ident ?loc id = inj_wit ?loc Stdarg.wit_ident id

let of_constr ?loc c = inj_wit ?loc Stdarg.wit_constr c

let rec of_list ?loc = function
| [] -> constructor Core.c_nil []
| e :: l ->
  constructor ?loc Core.c_cons [e; of_list ?loc l]

let of_qhyp ?loc = function
| AnonHyp n -> constructor Core.c_anon_hyp [of_int ?loc n]
| NamedHyp id -> constructor Core.c_named_hyp [of_ident ?loc id]

let of_bindings ?loc = function
| NoBindings ->
  constructor ?loc Core.c_no_bindings []
| ImplicitBindings tl ->
  constructor ?loc Core.c_implicit_bindings [of_list ?loc tl]
| ExplicitBindings tl ->
  let tl = List.map (fun (loc, (qhyp, e)) -> of_pair ?loc (of_qhyp ?loc qhyp, e)) tl in
  constructor ?loc Core.c_explicit_bindings [of_list ?loc tl]
