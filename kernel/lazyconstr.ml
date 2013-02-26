(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Term
open Mod_subst

(** [constr_substituted] are [constr] with possibly pending
    substitutions of kernel names. *)

type constr_substituted = constr substituted

let from_val = from_val

let force = force subst_mps

let subst_constr_subst = subst_substituted

(** Opaque proof terms are not loaded immediately, but are there
    in a lazy form. Forcing this lazy may trigger some unmarshal of
    the necessary structure. The ['a substituted] type isn't really great
    here, so we store "manually" a substitution list, the younger one at top.
*)

type lazy_constr = constr_substituted Lazy.t * substitution list

let force_lazy_constr (c,l) =
  List.fold_right subst_constr_subst l (Lazy.force c)

let lazy_constr_is_val (c,_) = Lazy.lazy_is_val c

let make_lazy_constr c = (c, [])

let force_opaque lc = force (force_lazy_constr lc)

let opaque_from_val c = (Lazy.lazy_from_val (from_val c), [])

let subst_lazy_constr sub (c,l) = (c,sub::l)

