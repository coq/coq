(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Pp
open Util
open Names
open Term
open Sign
open Evd
open Declarations
open Environ

let is_id_inst inst =
  let is_id (id,c) = match kind_of_term c with
    | Var id' -> id = id'
    | _ -> false
  in
  List.for_all is_id inst

(* Vérifier que les instances des let-in sont compatibles ?? *)
let instantiate_sign_including_let sign args =
  let rec instrec = function
    | ((id,b,_) :: sign, c::args) -> (id,c) :: (instrec (sign,args))
    | ([],[])                        -> []
    | ([],_) | (_,[]) ->
    anomaly "Signature and its instance do not match"
  in 
  instrec (sign,args)

let instantiate_evar sign c args =
  let inst = instantiate_sign_including_let sign args in
  if is_id_inst inst then
    c
  else
    replace_vars inst c

(* Existentials. *)

let existential_type sigma (n,args) =
  let info =
    try Evd.map sigma n
    with Not_found ->
      anomaly ("Evar "^(string_of_existential n)^" was not declared") in
  let hyps = info.evar_hyps in
  instantiate_evar hyps info.evar_concl (Array.to_list args)

exception NotInstantiatedEvar

let existential_value sigma (n,args) =
  let info = Evd.map sigma n in
  let hyps = info.evar_hyps in
  match evar_body info with
    | Evar_defined c ->
	instantiate_evar hyps c (Array.to_list args)
    | Evar_empty ->
	raise NotInstantiatedEvar

let existential_opt_value sigma ev =
  try Some (existential_value sigma ev)
  with NotInstantiatedEvar -> None

