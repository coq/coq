(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Util
open Pp
open Names
open Term
open Instantiate
open Lib
open Declare
open Recordops
open Classops

(*****  object definition ******)
 
let typ_lams_of t = 
  let rec aux acc c = match kind_of_term c with
    | IsLambda (x,c1,c2) -> aux (c1::acc) c2
    | IsCast (c,_) -> aux acc c
    | t -> acc,t
  in aux [] t

let objdef_err ref =
  errorlabstrm "object_declare"
    [< Printer.pr_global ref; 'sTR" is not a structure object" >]

let trait t =
  match kind_of_term t with
    | IsApp (f,args) ->
	if (match kind_of_term f with  
              | IsConst _ | IsMutInd _ | IsVar _ | IsMutConstruct _ -> true    
	      | _ -> false)
	then (f,Array.to_list args)
        else raise Not_found
    | IsConst _ | IsMutInd _ | IsVar _ | IsMutConstruct _ -> t,[]
    | _ -> raise Not_found

let objdef_declare ref =
  let sp = match ref with ConstRef sp -> sp | _ -> objdef_err ref in
  let env = Global.env () in
  let v = constr_of_reference ref in
  let vc =
    match kind_of_term v with
      | IsConst cst ->
	  (match constant_opt_value env cst with
	     | Some vc -> vc
	     | None -> objdef_err ref)
      | _ -> objdef_err ref in
  let lt,t = decompose_lam vc in
  let lt = List.rev (List.map snd lt) in
  match kind_of_term t with 
    | IsApp (f,args) ->
	let { s_PARAM = p; s_PROJ = lpj } = 
        (try (find_structure
		(match kind_of_term f with
                   | IsMutConstruct (indsp,1) -> indsp
		   | _ -> objdef_err ref))
         with _ -> objdef_err ref) in
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
                 | Some sp ->
		     try (sp, trait t)::l
                     with Not_found -> l)
            [] lps in
        add_anonymous_leaf (inObjDef1 sp);
        List.iter 
	  (fun (spi,(ci,l_ui)) -> 
	     add_new_objdef 
	       ((ConstRef spi,reference_of_constr ci),v,lt,params,l_ui)) comp
    | _ -> objdef_err ref
                 
