(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Util
open Pp
open Names
open Libnames
open Nameops
open Term
open Instantiate
open Lib
open Declare
open Recordops
open Classops
open Nametab

(*****  object definition ******)
 
let typ_lams_of t = 
  let rec aux acc c = match kind_of_term c with
    | Lambda (x,c1,c2) -> aux (c1::acc) c2
    | Cast (c,_) -> aux acc c
    | t -> acc,t
  in aux [] t

let objdef_err ref =
  errorlabstrm "object_declare"
    (pr_id (id_of_global ref) ++
       str" is not a structure object")

let objdef_declare ref =
  let sp = match ref with ConstRef sp -> sp | _ -> objdef_err ref in
  let env = Global.env () in
  let v = constr_of_reference ref in
  let vc = match Environ.constant_opt_value env sp with
    | Some vc -> vc
    | None -> objdef_err ref in
  let lt,t = decompose_lam vc in
  let lt = List.rev (List.map snd lt) in
  let f,args = match kind_of_term t with
    | App (f,args) -> f,args 
    | _ -> objdef_err ref in
  let { s_PARAM = p; s_PROJ = lpj } = 
    try (find_structure
	   (match kind_of_term f with
              | Construct (indsp,1) -> indsp
	      | _ -> objdef_err ref))
    with Not_found -> objdef_err ref in
  let params, projs =
    try list_chop p (Array.to_list args)
    with _ -> objdef_err ref in
  let lps = 
    try List.combine lpj projs 
    with _ -> objdef_err ref in
  let comp =
    List.fold_left
      (fun l (spopt,t) -> (* comp=components *)
	 match spopt with
	   | None -> l
           | Some proji_sp ->
	       let c, args = decompose_app t in
	       try (ConstRef proji_sp, reference_of_constr c, args) :: l
               with Not_found -> l)
      [] lps in
  add_anonymous_leaf (inObjDef1 sp);
  List.iter
    (fun (refi,c,argj) -> add_new_objdef ((refi,c),v,lt,params,argj))
    comp

let add_object_hook _ = objdef_declare
