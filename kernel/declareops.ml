(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Declarations

let safe_flags = safe_flags
let map_decl_arity = map_decl_arity
let constant_is_polymorphic = constant_is_polymorphic
let constant_has_body = constant_has_body
let constant_polymorphic_context = constant_polymorphic_context
let is_opaque = is_opaque
let subst_const_body = subst_const_body
let hcons_const_body = hcons_const_body
let eq_recarg = eq_recarg
let subst_recarg = subst_recarg
let mk_norec = mk_norec
let mk_paths = mk_paths
let dest_recarg = dest_recarg
let dest_subterms = dest_subterms
let recarg_length = recarg_length
let subst_wf_paths = subst_wf_paths
let inductive_polymorphic_context = inductive_polymorphic_context
let inductive_is_polymorphic = inductive_is_polymorphic
let inductive_is_cumulative = inductive_is_cumulative
let hcons_module_body = hcons_module_body
let hcons_module_type = hcons_module_type
let hcons_mind = hcons_mind
let subst_mind_body = subst_mind_body
let string_of_side_effect = Entries.string_of_side_effect
