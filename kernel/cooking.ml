(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

open Pp
open Util
open Names
open Term
open Sign
open Declarations
open Environ
open Reduction

(*s Cooking the constants. *)

type 'a modification =
  | NOT_OCCUR
  | DO_ABSTRACT of 'a * constr array
  | DO_REPLACE of constant_body

type work_list =
    (constant * constant modification) list
    * (inductive * inductive modification) list
    * (constructor * constructor modification) list

type recipe = {
  d_from : constant_body;
  d_abstract : identifier list;
  d_modlist : work_list }

let failure () =
  anomalylabstrm "generic__modify_opers"
    (str"An oper which was never supposed to appear has just appeared" ++
     spc () ++ str"Either this is in system code, and you need to" ++ spc () ++
     str"report this error," ++ spc () ++
     str"Or you are using a user-written tactic which calls" ++ spc () ++
     str"generic__modify_opers, in which case the user-written code" ++
     spc () ++ str"is broken - this function is an internal system" ++
     spc () ++ str"for internal system use only")

let modify_opers replfun (constl,indl,cstrl) =
  let rec substrec c =
    let c' = map_constr substrec c in
    match kind_of_term c' with
      | Case (ci,p,t,br) ->
	  (try
	     match List.assoc ci.ci_ind indl with
	       | DO_ABSTRACT (ind,abs_vars) ->
		   let n' = Array.length abs_vars + ci.ci_npar in
                   let ci' = { ci with
                               ci_ind = ind;
                               ci_npar = n' } in
		   mkCase (ci',p,t,br)
	       | _ -> raise Not_found
	   with
	     | Not_found -> c')

      | Ind spi ->
	  (try
	     (match List.assoc spi indl with
		| NOT_OCCUR -> failure ()
		| DO_ABSTRACT (oper',abs_vars) ->
                    mkApp (mkInd oper', abs_vars)
		| DO_REPLACE _ -> assert false)
	   with 
	     | Not_found -> c')

      | Construct spi ->
	  (try
	     (match List.assoc spi cstrl with
		| NOT_OCCUR -> failure ()
		| DO_ABSTRACT (oper',abs_vars) ->
		    mkApp (mkConstruct oper', abs_vars)
		| DO_REPLACE _ -> assert false)
	   with 
	     | Not_found -> c')

      | Const kn ->
	  (try
	     (match List.assoc kn constl with
		| NOT_OCCUR -> failure ()
		| DO_ABSTRACT (oper',abs_vars) ->
		    mkApp (mkConst oper', abs_vars)
		| DO_REPLACE cb -> substrec (replfun (kn,cb)))
	   with 
	     | Not_found -> c')
  
    | _ -> c'
  in 
  if (constl,indl,cstrl) = ([],[],[]) then fun x -> x else substrec

let expmod_constr modlist c =
  let simpfun = 
    if modlist = ([],[],[]) then fun x -> x else nf_betaiota in
  let expfun (kn,cb) = 
    if cb.const_opaque then
      errorlabstrm "expmod_constr"
	(str"Cannot unfold the value of " ++
        str(string_of_kn kn) ++ spc () ++
        str"You cannot declare local lemmas as being opaque" ++ spc () ++
        str"and then require that theorems which use them" ++ spc () ++
        str"be transparent");
    match cb.const_body with
      | Some body -> Declarations.force body
      | None -> assert false
  in
  let c' = modify_opers expfun modlist c in
  match kind_of_term c' with
    | Cast (value,typ) -> mkCast (simpfun value,simpfun typ)
    | _ -> simpfun c'

let expmod_type modlist c =
  type_app (expmod_constr modlist) c

let abstract_constant ids_to_abs hyps (body,typ) =
  let abstract_once_typ ((hyps,typ) as sofar) id =
    match hyps with
      | (hyp,c,t as decl)::rest when hyp = id ->
	  let typ' = mkNamedProd_wo_LetIn decl typ in
	  (rest, typ')
      | _ -> 
	  sofar
  in
  let abstract_once_body ((hyps,body) as sofar) id =
    match hyps with
      | (hyp,c,t as decl)::rest when hyp = id ->
	  let body' = mkNamedLambda_or_LetIn decl body in
	  (rest, body')
      | _ -> 
	  sofar
  in
  let (_,typ') =
    List.fold_left abstract_once_typ (hyps,typ) ids_to_abs 
  in
  let body' = match body with
      None -> None
    | Some l_body -> 
	Some (Declarations.from_val
		(let body = Declarations.force l_body in
		 let (_,body') = 
		   List.fold_left abstract_once_body (hyps,body) ids_to_abs
		 in
		   body'))
  in
    (body',typ')

let cook_constant env r =
  let cb = r.d_from in
  let typ = expmod_type r.d_modlist cb.const_type in
  let body = 
    option_app 
      (fun lconstr -> 
	 Declarations.from_val 
	   (expmod_constr r.d_modlist (Declarations.force lconstr))) 
      cb.const_body
  in
  let hyps =
    Sign.fold_named_context
      (fun d ctxt ->
        Sign.add_named_decl
          (map_named_declaration (expmod_constr r.d_modlist) d)
          ctxt)
      cb.const_hyps
      ~init:empty_named_context in
  let body,typ = abstract_constant r.d_abstract hyps (body,typ) in
  (body, typ, cb.const_constraints, cb.const_opaque)
