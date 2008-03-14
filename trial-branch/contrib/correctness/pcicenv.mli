(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id$ *)

open Penv
open Names
open Term
open Sign

(* Translation of local programs environments into Coq signatures.
 * It is mainly used to type the pre/post conditions in the good
 * environment *)

(* cci_sign_of: uniquement les objets purement fonctionnels de l'env. *)
val cci_sign_of : Prename.t -> local_env -> named_context

(* env. Coq avec seulement les variables X de l'env. *)
val now_sign_of : Prename.t -> local_env -> named_context

(* + les variables X@d pour toutes les dates de l'env. *)
val before_sign_of : Prename.t -> local_env -> named_context

(* + les variables `avant' X@ *)
val before_after_sign_of : Prename.t -> local_env -> named_context
val before_after_result_sign_of : ((identifier * constr) option)
                        -> Prename.t -> local_env -> named_context

(* env. des programmes traduits, avec les variables rennomées *)
val trad_sign_of : Prename.t -> local_env -> named_context

