(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id$ *)

open Names
open Term

open Pmisc
open Putil
open Ptype
open Past

(* on redéfinit add_sign pour éviter de construire des environnements
 * avec des doublons (qui font planter la résolution des implicites !) *)

let add_sign (id,t) s =
  if mem_sign s id then
    modify_sign id t s
  else
    add_sign (id,t) s

let cast_set c = make_type c mk_Set

let set = make_type Term.mkSet (Term.Type Impuniv.prop_univ)

(* [cci_sign_of env] construit un environnement pour CIC ne comprenant que
 * les objets fonctionnels de l'environnement de programes [env]
 *)

let cci_sign_of ren env =
   Prog_env.fold_all 
    (fun (id,v) sign ->
       match v with
	   Prog_env.TypeV (Ref _ | Array _) -> sign
	 | Prog_env.TypeV v -> 
	     let ty = Monad.trad_ml_type_v ren env v in
	       add_sign (id,cast_set ty) sign
	 | Prog_env.Set -> add_sign (id,set) sign)
    env (initial_sign())

(* [sign_meta ren env fadd ini]
 * construit un environnement pour CIC qui prend en compte les variables
 * de programme. 
 * pour cela, cette fonction parcours tout l'envrionnement (global puis
 * local [env]) et pour chaque déclaration, ajoute ce qu'il faut avec la
 * fonction [fadd] s'il s'agit d'un mutable et directement sinon,
 * en partant de [ini].
 *)

let sign_meta ren env fast ini =
   Prog_env.fold_all 
    (fun (id,v) sign ->
       match v with
	   Prog_env.TypeV (Ref _ | Array _ as v) -> 
	     let ty = Monad.trad_imp_type ren env v in
	       fast sign id ty
	 | Prog_env.TypeV v -> 
	     let ty = Monad.trad_ml_type_v ren env v in
	       add_sign (id,cast_set ty) sign
	 | Prog_env.Set -> add_sign (id,set) sign)
    env ini

let add_sign_d dates (id,c) sign =
  let sign =
    List.fold_left (fun sign d -> add_sign (at_id id d,c) sign) sign dates
  in
    add_sign (id,c) sign
 
let sign_of add ren env =
  sign_meta ren env
    (fun sign id c -> let c = cast_set c in add (id,c) sign)
    (initial_sign())

let result_of sign = function
    None   -> sign
  | Some (id,c) -> add_sign (id, cast_set c) sign
	
let before_after_result_sign_of res ren env =
  let dates = "" :: Renamings.all_dates ren in
  result_of (sign_of (add_sign_d dates) ren env) res

let before_after_sign_of ren =
  let dates = "" :: Renamings.all_dates ren in
  sign_of (add_sign_d dates) ren

let before_sign_of ren =
  let dates = Renamings.all_dates ren in
  sign_of (add_sign_d dates) ren

let now_sign_of =
  sign_of (add_sign_d [])


(* environnement après traduction *)

let trad_sign_of ren =
  sign_of
    (fun (id,c) sign -> add_sign (Renamings.current_var ren id,c) sign)
    ren


