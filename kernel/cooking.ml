
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

type modification_action = ABSTRACT | ERASE

type 'a modification =
  | NOT_OCCUR
  | DO_ABSTRACT of 'a * modification_action list
  | DO_REPLACE

type work_alist = (global_reference * global_reference modification) list

type recipe = {
  d_from : section_path;
  d_abstract : identifier list;
  d_modlist : (global_reference * global_reference modification) list }

let interp_modif absfun oper (oper',modif) cl = 
  let rec interprec = function
    | ([], cl) -> 
	(match oper' with
	   | ConstRef sp -> mkConst (sp,Array.of_list cl)
	   | ConstructRef sp -> mkMutConstruct (sp,Array.of_list cl)
	   | IndRef sp -> mkMutInd (sp,Array.of_list cl))
    | (ERASE::tlm, c::cl) -> interprec (tlm,cl)
    | (ABSTRACT::tlm, c::cl) -> absfun (interprec (tlm,cl)) c
    | _ -> assert false
  in 
  interprec (modif,cl)

let modify_opers replfun absfun oper_alist =
  let failure () =
    anomalylabstrm "generic__modify_opers"
      [< 'sTR"An oper which was never supposed to appear has just appeared" ;
         'sPC ; 'sTR"Either this is in system code, and you need to" ; 'sPC;
         'sTR"report this error," ; 'sPC ;
         'sTR"Or you are using a user-written tactic which calls" ; 'sPC ;
         'sTR"generic__modify_opers, in which case the user-written code" ;
         'sPC ; 'sTR"is broken - this function is an internal system" ;
         'sPC ; 'sTR"for internal system use only" >]
  in
  let rec substrec c =
    let op, cl = splay_constr c in
    let cl' = Array.map substrec cl in
    match op with
      (* Hack pour le sp dans l'annotation du Cases *)
      | OpMutCase (n,(spi,a,b,c,d) as oper) ->
	  (try
	     match List.assoc (IndRef spi) oper_alist with
	       | DO_ABSTRACT (IndRef spi',_) ->
		   gather_constr (OpMutCase (n,(spi',a,b,c,d)),cl')
	       | _ -> raise Not_found
	   with
	     | Not_found -> gather_constr (op,cl'))

      | OpMutInd spi ->
	  (try
	     (match List.assoc (IndRef spi) oper_alist with
		| NOT_OCCUR -> failure ()
		| DO_ABSTRACT (oper',modif) ->
		    assert (List.length modif <= Array.length cl);
		    interp_modif absfun (IndRef spi) (oper',modif)
		      (Array.to_list cl')
		| DO_REPLACE -> assert false)
	   with 
	     | Not_found -> mkMutInd (spi,cl'))

      | OpMutConstruct spi ->
	  (try
	     (match List.assoc (ConstructRef spi) oper_alist with
		| NOT_OCCUR -> failure ()
		| DO_ABSTRACT (oper',modif) ->
		    assert (List.length modif <= Array.length cl);
		    interp_modif absfun (ConstructRef spi) (oper',modif)
		      (Array.to_list cl')
		| DO_REPLACE -> assert false)
	   with 
	     | Not_found -> mkMutConstruct (spi,cl'))

      | OpConst sp ->
	  (try
	     (match List.assoc (ConstRef sp) oper_alist with
		| NOT_OCCUR -> failure ()
		| DO_ABSTRACT (oper',modif) ->
		    assert (List.length modif <= Array.length cl);
		    interp_modif absfun (ConstRef sp) (oper',modif)
		      (Array.to_list cl')
		| DO_REPLACE -> substrec (replfun (sp,cl')))
	   with 
	     | Not_found -> mkConst (sp,cl'))
  
    | _ -> gather_constr (op, cl')
  in 
  if oper_alist = [] then fun x -> x else substrec

let expmod_constr oldenv modlist c =
  let sigma = Evd.empty in
  let simpfun = 
    if modlist = [] then fun x -> x else nf_betaiota oldenv sigma in
  let expfun cst = 
    try 
      constant_value oldenv cst
    with NotEvaluableConst Opaque ->
      let (sp,_) = cst in
      errorlabstrm "expmod_constr"
	[< 'sTR"Cannot unfold the value of ";
           'sTR(string_of_path sp); 'sPC;
           'sTR"You cannot declare local lemmas as being opaque"; 'sPC;
           'sTR"and then require that theorems which use them"; 'sPC;
           'sTR"be transparent" >];
  in
  let c' = modify_opers expfun (fun a b -> mkApp (a, [|b|])) modlist c in
  match kind_of_term c' with
    | IsCast (val_0,typ) -> mkCast (simpfun val_0,simpfun typ)
    | _ -> simpfun c'

let expmod_type oldenv modlist c =
  type_app (expmod_constr oldenv modlist) c

let abstract_constant ids_to_abs hyps (body,typ) =
  let abstract_once ((hyps,body,typ) as sofar) id =
    match hyps with
      | [] -> 
	  sofar
      | (hyp,c,t as decl)::rest ->
	  if hyp <> id then 
	    sofar
	  else
	    let body' = match body with
	      | None -> None
	      | Some c -> Some (mkNamedLambda_or_LetIn decl c)
	    in
	    let typ' = mkNamedProd_or_LetIn decl typ in
	    (rest, body', typ')
  in
  let (_,body',typ') =
    List.fold_left abstract_once (hyps,body,typ) ids_to_abs in
  (body',typ')

let cook_constant env r =
  let cb = lookup_constant r.d_from env in
  let typ = expmod_type env r.d_modlist cb.const_type in
  let body = option_app (expmod_constr env r.d_modlist) cb.const_body in
  let hyps = map_named_context (expmod_constr env r.d_modlist) cb.const_hyps in
  abstract_constant r.d_abstract hyps (body,typ)

