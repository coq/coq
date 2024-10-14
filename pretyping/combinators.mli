(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Environ
open Evd
open EConstr

(** [telescope env sigma ctx] turns a context [x1:A1;...;xn:An] into a
    right-associated nested sigma-type of the right sort. It returns:
    - the nested sigma-type [T := {x1:A1 & ... {xn-1:An-1 & ... An} ... }]
    - the canonical tuple [(existsT _ x1 ... (existsT _ xn-1 xn) ...)]
      inhabiting the sigma-type in the given context
    - an instantiation of the assumptions of [ctx] with values they
      have in the context [x:T], that is
      [x1:=projT1 x;...;xn-1:=projT1 ... (projT2 x);xn:=projT2 ... (projT2 x)];
      note that let-ins in the original context are preserved
    Depending on the sorts of types, it uses either [ex], [sig] or
    [sigT], even if we always used [sigT] above as an example.
*)

type telescope = {
  telescope_type : types;
  telescope_value : constr;
}

val telescope : env -> evar_map -> rel_context -> evar_map * rel_context * telescope

(** [make_iterated_tuple env sigma ~default c] encapsulates [c] (of
    inferred type [C]) and its free variables [x1,...,xn] into a
    right-associated nested tuple in a [sigT]-type. It returns:
    - the nested type [{x1:A1 & ... {xn:An & ... C} ... }]
    - the tuple [(existsT _ x1 ... (existsT _ xn c) ...)]
    - an alternative tuple [(existsT _ x1 ... (existsT _ xn default) ...)];
      if [default] has not the right type, it fails.
*)

val make_iterated_tuple : env -> evar_map -> default:constr -> constr -> types -> evar_map * telescope * constr

(** [make_selector env sigma ~pos ~special ~default c] constructs a
    case-split on [c] (assumed of inductive type), with the [pos]-th
    branch returning [special], and all the other branch returning
    [default]. *)

val make_selector : env -> evar_map -> pos:int -> special:constr -> default:constr -> constr -> types -> constr
