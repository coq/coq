(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

open Pp
open Util
open Names
open Term
open Sign
open Declarations
open Instantiate
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
    [< 'sTR"An oper which was never supposed to appear has just appeared" ;
       'sPC ; 'sTR"Either this is in system code, and you need to" ; 'sPC;
       'sTR"report this error," ; 'sPC ;
       'sTR"Or you are using a user-written tactic which calls" ; 'sPC ;
       'sTR"generic__modify_opers, in which case the user-written code" ;
       'sPC ; 'sTR"is broken - this function is an internal system" ;
       'sPC ; 'sTR"for internal system use only" >]

let modify_opers replfun (constl,indl,cstrl) =
  let rec substrec c =
    let op, cl = splay_constr c in
    let cl' = Array.map substrec cl in
    match op with
      | OpMutCase (n,(spi,a,b,c,d) as oper) ->
	  (try
	     match List.assoc spi indl with
	       | DO_ABSTRACT (spi',abs_vars) ->
		   let n' = Array.length abs_vars + n in
		   gather_constr (OpMutCase (n',(spi',a,b,c,d)),cl')
	       | _ -> raise Not_found
	   with
	     | Not_found -> gather_constr (op,cl'))

      | OpMutInd spi ->
	  assert (Array.length cl=0);
	  (try
	     (match List.assoc spi indl with
		| NOT_OCCUR -> failure ()
		| DO_ABSTRACT (oper',abs_vars) ->
                    mkApp (mkMutInd oper', abs_vars)
		| DO_REPLACE _ -> assert false)
	   with 
	     | Not_found -> mkMutInd spi)

      | OpMutConstruct spi ->
	  assert (Array.length cl=0);
	  (try
	     (match List.assoc spi cstrl with
		| NOT_OCCUR -> failure ()
		| DO_ABSTRACT (oper',abs_vars) ->
		    mkApp (mkMutConstruct oper', abs_vars)
		| DO_REPLACE _ -> assert false)
	   with 
	     | Not_found -> mkMutConstruct spi)

      | OpConst sp ->
	  assert (Array.length cl=0);
	  (try
	     (match List.assoc sp constl with
		| NOT_OCCUR -> failure ()
		| DO_ABSTRACT (oper',abs_vars) ->
		    mkApp (mkConst oper', abs_vars)
		| DO_REPLACE cb -> substrec (replfun sp cb cl'))
	   with 
	     | Not_found -> mkConst sp)
  
    | _ -> gather_constr (op, cl')
  in 
  if (constl,indl,cstrl) = ([],[],[]) then fun x -> x else substrec

let expmod_constr modlist c =
  let sigma = Evd.empty in
  let simpfun = 
    if modlist = ([],[],[]) then fun x -> x else nf_betaiota in
  let expfun sp cb args = 
    if cb.const_opaque then
      errorlabstrm "expmod_constr"
	[< 'sTR"Cannot unfold the value of ";
        'sTR(string_of_path sp); 'sPC;
        'sTR"You cannot declare local lemmas as being opaque"; 'sPC;
        'sTR"and then require that theorems which use them"; 'sPC;
        'sTR"be transparent" >];
    match cb.const_body with
      | Some body -> 
          instantiate_constr cb.const_hyps body (Array.to_list args)
      | None -> assert false
  in
  let c' =
    modify_opers expfun modlist c in
  match kind_of_term c' with
    | IsCast (val_0,typ) -> mkCast (simpfun val_0,simpfun typ)
    | _ -> simpfun c'

let expmod_type modlist c =
  type_app (expmod_constr modlist) c

let abstract_constant ids_to_abs hyps (body,typ) =
  let abstract_once ((hyps,body,typ) as sofar) id =
    match hyps with
      | (hyp,c,t as decl)::rest when hyp = id ->
	  let body' = option_app (mkNamedLambda_or_LetIn decl) body in
	  let typ' = mkNamedProd_wo_LetIn decl typ in
	  (rest, body', typ')
      | _ -> 
	  sofar
  in
  let (_,body',typ') =
    List.fold_left abstract_once (hyps,body,typ) ids_to_abs in
  (body',typ')

let cook_constant env r =
  let cb = r.d_from in
  let typ = expmod_type r.d_modlist cb.const_type in
  let body = option_app (expmod_constr r.d_modlist) cb.const_body in
  let hyps = List.map (fun (sp,c,t) -> (basename sp,c,t)) cb.const_hyps in
  let hyps = map_named_context (expmod_constr r.d_modlist) hyps in
  let body,typ = abstract_constant r.d_abstract hyps (body,typ) in
  (body, typ, cb.const_constraints, cb.const_opaque)
