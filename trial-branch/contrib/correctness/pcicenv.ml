(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id$ *)

open Names
open Term
open Sign

open Pmisc
open Putil
open Ptype
open Past

(* on redéfinit add_sign pour éviter de construire des environnements
 * avec des doublons (qui font planter la résolution des implicites !) *)

(* VERY UGLY!! find some work around *)
let modify_sign id t s =
  fold_named_context
    (fun ((x,b,ty) as d) sign ->
      if x=id then add_named_decl (x,b,t) sign else add_named_decl d sign)
    s ~init:empty_named_context

let add_sign (id,t) s =
  try 
    let _ = lookup_named id s in
    modify_sign id t s
  with Not_found ->
    add_named_decl (id,None,t) s

let cast_set c = mkCast (c, mkSet)

let set = mkCast (mkSet, mkType Univ.prop_univ)

(* [cci_sign_of env] construit un environnement pour CIC ne comprenant que
 * les objets fonctionnels de l'environnement de programes [env]
 *)

let cci_sign_of ren env =
  Penv.fold_all 
    (fun (id,v) sign ->
       match v with
	 | Penv.TypeV (Ref _ | Array _) -> sign
	 | Penv.TypeV v -> 
	     let ty = Pmonad.trad_ml_type_v ren env v in
	     add_sign (id,cast_set ty) sign
	 | Penv.Set -> add_sign (id,set) sign)
    env (Global.named_context ())

(* [sign_meta ren env fadd ini]
 * construit un environnement pour CIC qui prend en compte les variables
 * de programme. 
 * pour cela, cette fonction parcours tout l'envrionnement (global puis
 * local [env]) et pour chaque déclaration, ajoute ce qu'il faut avec la
 * fonction [fadd] s'il s'agit d'un mutable et directement sinon,
 * en partant de [ini].
 *)

let sign_meta ren env fast ini =
   Penv.fold_all 
    (fun (id,v) sign ->
       match v with
	 | Penv.TypeV (Ref _ | Array _ as v) -> 
	     let ty = Pmonad.trad_imp_type ren env v in
	     fast sign id ty
	 | Penv.TypeV v -> 
	     let ty = Pmonad.trad_ml_type_v ren env v in
	     add_sign (id,cast_set ty) sign
	 | Penv.Set -> add_sign (id,set) sign)
    env ini

let add_sign_d dates (id,c) sign =
  let sign =
    List.fold_left (fun sign d -> add_sign (at_id id d,c) sign) sign dates
  in
    add_sign (id,c) sign
 
let sign_of add ren env =
  sign_meta ren env
    (fun sign id c -> let c = cast_set c in add (id,c) sign)
    (Global.named_context ())

let result_of sign = function
    None   -> sign
  | Some (id,c) -> add_sign (id, cast_set c) sign
	
let before_after_result_sign_of res ren env =
  let dates = "" :: Prename.all_dates ren in
  result_of (sign_of (add_sign_d dates) ren env) res

let before_after_sign_of ren =
  let dates = "" :: Prename.all_dates ren in
  sign_of (add_sign_d dates) ren

let before_sign_of ren =
  let dates = Prename.all_dates ren in
  sign_of (add_sign_d dates) ren

let now_sign_of =
  sign_of (add_sign_d [])


(* environnement après traduction *)

let trad_sign_of ren =
  sign_of
    (fun (id,c) sign -> add_sign (Prename.current_var ren id,c) sign)
    ren


