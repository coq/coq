(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id$ *)

open Penv
open Names
open Term

(* Translation of local programs environments into Coq signatures.
 * It is mainly used to type the pre/post conditions in the good
 * environment *)

(* cci_sign_of: uniquement les objets purement fonctionnels de l'env. *)
val cci_sign_of : Renamings.t -> local_env -> context

(* env. Coq avec seulement les variables X de l'env. *)
val now_sign_of : Renamings.t -> local_env -> context

(* + les variables X@d pour toutes les dates de l'env. *)
val before_sign_of : Renamings.t -> local_env -> context

(* + les variables `avant' X@ *)
val before_after_sign_of : Renamings.t -> local_env -> context
val before_after_result_sign_of : ((identifier * constr) option)
                        -> Renamings.t -> local_env -> context

(* env. des programmes traduits, avec les variables rennomées *)
val trad_sign_of : Renamings.t -> local_env -> context

