(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Names
open Util
open Misctypes
open Tac2intern
open Tac2expr
open Tac2qexpr
open Tac2core

(** Syntactic quoting of expressions. *)

let std_core n = KerName.make2 Tac2env.std_prefix (Label.of_id (Id.of_string n))

let dummy_loc = Loc.make_loc (-1, -1)

let constructor ?loc kn args =
  let loc = Option.default dummy_loc loc in
  let cst = CTacCst (loc, AbsKn (Other kn)) in
  if List.is_empty args then cst
  else CTacApp (loc, cst, args)

let std_constructor ?loc name args =
  constructor ?loc (std_core name) args

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

let of_anti ?loc f = function
| QExpr x -> f ?loc x
| QAnti (loc, id) -> of_variable ?loc id

let of_ident ?loc id = inj_wit ?loc Stdarg.wit_ident id

let of_constr ?loc c = inj_wit ?loc Stdarg.wit_constr c

let of_bool ?loc b =
  let c = if b then Core.c_true else Core.c_false in
  constructor ?loc c []

let rec of_list ?loc = function
| [] -> constructor Core.c_nil []
| e :: l ->
  constructor ?loc Core.c_cons [e; of_list ?loc l]

let of_qhyp ?loc = function
| AnonHyp n -> constructor Core.c_anon_hyp [of_int ?loc n]
| NamedHyp id -> constructor Core.c_named_hyp [of_ident ?loc id]

let of_bindings ?loc = function
| QNoBindings ->
  std_constructor ?loc "NoBindings" []
| QImplicitBindings tl ->
  std_constructor ?loc "ImplicitBindings" [of_list ?loc tl]
| QExplicitBindings tl ->
  let tl = List.map (fun (loc, (qhyp, e)) -> of_pair ?loc (of_anti ?loc of_qhyp qhyp, e)) tl in
  std_constructor ?loc "ExplicitBindings" [of_list ?loc tl]

let rec of_intro_pattern ?loc = function
| QIntroForthcoming b ->
  std_constructor ?loc "IntroForthcoming" [of_bool b]
| QIntroNaming iname ->
  std_constructor ?loc "IntroNaming" [of_intro_pattern_naming iname]
| QIntroAction iact ->
  std_constructor ?loc "IntroAction" [of_intro_pattern_action iact]

and of_intro_pattern_naming ?loc = function
| QIntroIdentifier id ->
  std_constructor ?loc "IntroIdentifier" [of_anti ?loc of_ident id]
| QIntroFresh id ->
  std_constructor ?loc "IntroFresh" [of_anti ?loc of_ident id]
| QIntroAnonymous ->
  std_constructor ?loc "IntroAnonymous" []

and of_intro_pattern_action ?loc = function
| QIntroWildcard ->
  std_constructor ?loc "IntroWildcard" []
| QIntroOrAndPattern pat ->
  std_constructor ?loc "IntroOrAndPattern" [of_or_and_intro_pattern ?loc pat]
| QIntroInjection il ->
  std_constructor ?loc "IntroInjection" [of_intro_patterns ?loc il]
| QIntroRewrite b ->
  std_constructor ?loc "IntroRewrite" [of_bool ?loc b]

and of_or_and_intro_pattern ?loc = function
| QIntroOrPattern ill ->
  let ill = List.map (of_intro_patterns ?loc) ill in
  std_constructor ?loc "IntroOrPattern" [of_list ?loc ill]
| QIntroAndPattern il ->
  std_constructor ?loc "IntroAndPattern" [of_intro_patterns ?loc il]

and of_intro_patterns ?loc l =
  of_list ?loc (List.map (of_intro_pattern ?loc) l)
