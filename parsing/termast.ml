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
open Univ
open Names
open Nameops
open Term
open Termops
open Inductive
open Sign
open Environ
open Libnames
open Declare
open Impargs
open Coqast
open Ast
open Rawterm
open Pattern
open Nametab

(* In this file, we translate rawconstr to ast, in order to print constr *)

(**********************************************************************)
(* Parametrization                                                    *)
open Constrextern
(*
(* This governs printing of local context of references *)
let print_arguments = ref false

(* If true, prints local context of evars, whatever print_arguments *)
let print_evar_arguments = ref false
*)

(* This forces printing of cast nodes *)
let print_casts = ref true

(*
(* This governs printing of implicit arguments.  When
   [print_implicits] is on then [print_implicits_explicit_args] tells
   how implicit args are printed. If on, implicit args are printed
   prefixed by "!" otherwise the function and not the arguments is
   prefixed by "!" *)
let print_implicits = ref false
*)
let print_implicits_explicit_args = ref false

(*
(* This forces printing of coercions *)
let print_coercions = ref false

(* This forces printing universe names of Type{.} *)
let print_universes = ref false


let with_option o f x =
  let old = !o in o:=true;
  try let r = f x in o := old; r
  with e -> o := old; raise e

let with_arguments f = with_option print_arguments f
let with_casts f = with_option print_casts f
let with_implicits f = with_option print_implicits f
let with_coercions f = with_option print_coercions f
let with_universes f = with_option print_universes f
*)
(**********************************************************************)
(* conversion of references                                           *)

let ids_of_ctxt ctxt =
  Array.to_list
    (Array.map
       (function c -> match kind_of_term c with
	  | Var id -> id
	  | _ ->
       error
       "Termast: arbitrary substitution of references not yet implemented")
     ctxt)

let ast_of_ident id = nvar id

let ast_of_name = function 
  | Name id -> nvar id
  | Anonymous -> nvar wildcard

let idopt_of_name = function 
  | Name id -> Some id
  | Anonymous -> None

let ast_of_binders bl =
  List.map (fun (nal,isdef,ty) ->
    if isdef then ope("LETBINDER",ty::List.map ast_of_name nal)
    else ope("BINDER",ty::List.map ast_of_name nal)) bl

let ast_type_of_binder bl t =
  List.fold_right (fun (nal,isdef,ty) ast ->
    if isdef then
      ope("LETIN",[ty;slam(idopt_of_name (List.hd nal),ast)])
    else
      ope("PROD",[ty;List.fold_right
        (fun na ast -> slam(idopt_of_name na,ast)) nal ast]))
    bl t

let ast_body_of_binder bl t =
  List.fold_right (fun (nal,isdef,ty) ast ->
    if isdef then
      ope("LETIN",[ty;slam(idopt_of_name (List.hd nal),ast)])
    else
      ope("LAMBDA",[ty;List.fold_right
        (fun na ast -> slam(idopt_of_name na,ast)) nal ast]))
    bl t

let ast_of_constant_ref sp =
  ope("CONST", [path_section dummy_loc sp])

let ast_of_existential_ref ev =
(*
  let ev = 
    try int_of_string (string_of_id ev)
    with _ -> warning "cannot find existential variable number"; 0 in
*)
  ope("EVAR", [num ev])

let ast_of_constructor_ref ((sp,tyi),n) =
  ope("MUTCONSTRUCT",[path_section dummy_loc sp; num tyi; num n])

let ast_of_inductive_ref (sp,tyi) =
  ope("MUTIND", [path_section dummy_loc sp; num tyi])

let ast_of_section_variable_ref s =
  ope("SECVAR", [nvar s])

let ast_of_qualid p =
  let dir, s = repr_qualid p in
  let args = List.map nvar ((List.rev(repr_dirpath dir))@[s]) in
  ope ("QUALID", args)

let ast_of_ref = function
  | ConstRef sp -> ast_of_constant_ref sp
  | IndRef sp -> ast_of_inductive_ref sp
  | ConstructRef sp -> ast_of_constructor_ref sp
  | VarRef id -> ast_of_section_variable_ref id

(**********************************************************************)
(* conversion of patterns                                             *)

let rec ast_of_cases_pattern = function   (* loc is thrown away for printing *)
  | PatVar (loc,Name id) -> nvar id
  | PatVar (loc,Anonymous) -> nvar wildcard
  | PatCstr(loc,cstrsp,args,Name id) ->
      let args = List.map ast_of_cases_pattern args in
      ope("PATTAS",
	  [nvar id;
	   ope("PATTCONSTRUCT", (ast_of_constructor_ref cstrsp)::args)])
  | PatCstr(loc,cstrsp,args,Anonymous) ->
      ope("PATTCONSTRUCT",
	  (ast_of_constructor_ref cstrsp)
	  :: List.map ast_of_cases_pattern args)
	
let ast_dependent na aty =
  match na with
    | Name id -> occur_var_ast id aty
    | Anonymous -> false

let decompose_binder = function
  | RProd(_,na,ty,c) -> Some (BProd,na,ty,c)
  | RLambda(_,na,ty,c) -> Some (BLambda,na,ty,c)
  | RLetIn(_,na,b,c) -> Some (BLetIn,na,b,c)
  | _ -> None

(* Implicit args indexes are in ascending order *)
let explicitize impl args =
  let n = List.length args in
  let rec exprec q = function
    | a::args, imp::impl when is_status_implicit imp ->
        let tail = exprec (q+1) (args,impl) in
        let visible =
          (!print_implicits & !print_implicits_explicit_args)
          or not (is_inferable_implicit false n imp) in
        if visible then ope("EXPL", [num q; a]) :: tail else tail
    | a::args, _::impl -> a :: exprec (q+1) (args,impl)
    | args, [] -> args  (* In case of polymorphism *)
    | [], _ -> []
  in exprec 1 (args,impl)

let rec skip_coercion dest_ref (f,args as app) =
  if !print_coercions then app
  else
    try
      match dest_ref f with
	| Some r ->
	    (match Classops.hide_coercion r with
	       | Some n ->
		   if n >= List.length args then app
		   else (* We skip a coercion *)
		     let fargs = list_skipn n args in
	       	     skip_coercion dest_ref (List.hd fargs,List.tl fargs)
	       | None -> app)
	| None -> app
    with Not_found -> app

let ast_of_app impl f args =
  if !print_implicits & not !print_implicits_explicit_args then 
    ope("APPLISTEXPL", f::args)
  else
    let args = explicitize impl args in
    if args = [] then f else ope("APPLIST", f::args)

let rec ast_of_raw = function
  | RRef (_,ref) -> ast_of_ref ref
  | RVar (_,id) -> ast_of_ident id
  | REvar (_,n,_) -> (* we drop args *) ast_of_existential_ref n
  | RPatVar (_,(_,n)) -> ope("META",[ast_of_ident n])
  | RApp (_,f,args) ->
      let (f,args) =
	skip_coercion (function RRef(_,r) -> Some r | _ -> None) (f,args) in
      let astf = ast_of_raw f in
      let astargs = List.map ast_of_raw args in
      (match f with 
	 | RRef (_,ref) -> ast_of_app (implicits_of_global ref) astf astargs
	 | _       -> ast_of_app [] astf astargs)

  | RProd (_,Anonymous,t,c) ->
      (* Anonymous product are never factorized *)
      ope("ARROW",[ast_of_raw t; slam(None,ast_of_raw c)])

  | RLetIn (_,na,t,c) ->
      ope("LETIN",[ast_of_raw t; slam(idopt_of_name na,ast_of_raw c)])

  | RProd (_,na,t,c) ->
      let (n,a) = factorize_binder 1 BProd na (ast_of_raw t) c in
      (* PROD et PRODLIST doivent être distingués à cause du cas *)
      (* non dépendant, pour isoler l'implication; peut-être un *)
      (* constructeur ARROW serait-il plus justifié ? *) 
      let tag = if n=1 then "PROD" else "PRODLIST" in
      ope(tag,[ast_of_raw t;a])

  | RLambda (_,na,t,c) ->
      let (n,a) = factorize_binder 1 BLambda na (ast_of_raw t) c in
      (* LAMBDA et LAMBDALIST se comportent pareil ... Non ! *)
      (* Pour compatibilité des theories, il faut LAMBDALIST partout *)
      ope("LAMBDALIST",[ast_of_raw t;a])

  | RCases (_,(typopt,_),tml,eqns) ->
      let pred = ast_of_rawopt typopt in
      let tag = "CASES" in
      let asttomatch =
	ope("TOMATCH", List.map (fun (tm,_) -> ast_of_raw tm) tml) in
      let asteqns = List.map ast_of_eqn eqns in 
      ope(tag,pred::asttomatch::asteqns)
	
  | ROrderedCase (_,LetStyle,typopt,tm,[|bv|],_) ->
      let nvar' = function Anonymous -> nvar wildcard | Name id -> nvar id in
      let rec f l = function
        | RLambda (_,na,RHole _,c) -> f (nvar' na :: l) c
        | RLetIn (_,na,RHole _,c) -> f (nvar' na :: l) c
        | c -> List.rev l, ast_of_raw c in
      let l,c = f [] bv in
      let eqn = ope ("EQN", [c;ope ("PATTCONSTRUCT",(nvar wildcard)::l)]) in
      ope ("FORCELET",[(ast_of_rawopt typopt);(ast_of_raw tm);eqn])

  | ROrderedCase (_,st,typopt,tm,bv,_) ->
      let tag = match st with
	| IfStyle -> "FORCEIF"
	| RegularStyle -> "CASE"
	| MatchStyle | LetStyle -> "MATCH"
      in

      (* warning "Old Case syntax"; *)
      ope(tag,(ast_of_rawopt typopt)
	    ::(ast_of_raw tm)
	    ::(Array.to_list (Array.map ast_of_raw bv)))

  | RLetTuple _ | RIf _ ->
      error "Let tuple not supported in v7"

  | RRec (_,fk,idv,blv,tyv,bv) ->
      let alfi = Array.map ast_of_ident idv in
      (match fk with
	 | RFix (nv,n) ->
             let rec split_lambda binds = function
	       | (0, t) -> (List.rev binds,ast_of_raw t)
	       | (n, RLetIn (_,na,b,c)) ->
		   let bind = ope("LETBINDER",[ast_of_raw b;ast_of_name na]) in
		   split_lambda (bind::binds) (n,c)
	       | (n, RLambda (_,na,t,b)) ->
		   let bind = ope("BINDER",[ast_of_raw t;ast_of_name na]) in
		   split_lambda (bind::binds) (n-1,b)
	       | _ -> anomaly "ast_of_rawconst: ill-formed fixpoint body" in
	     let rec split_product = function
	       | (0, t) -> ast_of_raw t
	       | (n, RLetIn (_,na,_,c)) -> split_product (n,c)
	       | (n, RProd (_,na,t,b)) -> split_product (n-1,b)
	       | _ -> anomaly "ast_of_rawconst: ill-formed fixpoint type" in
	     let listdecl = 
	       Array.mapi
		 (fun i fi ->
                   if List.length blv.(i) >= nv.(i)+1 then
                     let (oldfixp,factb) = list_chop (nv.(i)+1) blv.(i) in
                     let bl = factorize_local_binder oldfixp in
                     let factb = factorize_local_binder factb in
                     let asttyp = ast_type_of_binder factb
                       (ast_of_raw tyv.(i)) in
                     let astdef = ast_body_of_binder factb
                       (ast_of_raw bv.(i)) in
                     ope("FDECL",[fi;ope("BINDERS",ast_of_binders bl);
                                  asttyp; astdef])
                   else
                     let n = nv.(i)+1 - List.length blv.(i) in
		     let (lparams,astdef) =
                       split_lambda [] (n,bv.(i)) in
                     let bl = factorize_local_binder blv.(i) in
                     let lparams = ast_of_binders bl @ lparams in
		     let asttyp = split_product (n,tyv.(i)) in
		     ope("FDECL",
		         [fi; ope ("BINDERS",lparams); 
		          asttyp; astdef]))
		 alfi
	     in 
	     ope("FIX", alfi.(n)::(Array.to_list listdecl))
	 | RCoFix n -> 
	     let listdecl =
               Array.mapi 
		 (fun i fi ->
                   let bl = factorize_local_binder blv.(i) in
                   let asttyp = ast_type_of_binder bl (ast_of_raw tyv.(i)) in
                   let astdef = ast_body_of_binder bl (ast_of_raw bv.(i)) in
		   ope("CFDECL",[fi; asttyp; astdef]))
		 alfi
	     in 
	     ope("COFIX", alfi.(n)::(Array.to_list listdecl)))

  | RSort (_,s) ->
      (match s with
	 | RProp Null -> ope("PROP",[])
	 | RProp Pos -> ope("SET",[])
	 | RType (Some u) when !print_universes -> ope("TYPE",[ide(Univ.string_of_univ u)])
	 | RType _ -> ope("TYPE",[]))
  | RHole _ -> ope("ISEVAR",[])
  | RCast (_,c,t) -> ope("CAST",[ast_of_raw c;ast_of_raw t])
  | RDynamic (loc,d) -> Dynamic (loc,d)
	
and ast_of_eqn (_,ids,pl,c) =
  ope("EQN", (ast_of_raw c)::(List.map ast_of_cases_pattern pl))

and ast_of_rawopt = function
  | None -> (string "SYNTH")
  | Some p -> ast_of_raw p

and factorize_binder n oper na aty c =
  let (p,body) = match decompose_binder c with
    | Some (oper',na',ty',c')
	when (oper = oper') & (aty = ast_of_raw ty')
	  & not (ast_dependent na aty) (* To avoid na in ty' escapes scope *)
	  & not (na' = Anonymous & oper = BProd)
	  -> factorize_binder (n+1) oper na' aty c'
    | _ -> (n,ast_of_raw c)
  in
  (p,slam(idopt_of_name na, body))

and factorize_local_binder = function
    [] -> []
  | (na,Some bd,ty)::l ->
      ([na],true,ast_of_raw bd) :: factorize_local_binder l
  | (na,None,ty)::l ->
      let ty = ast_of_raw ty in
      (match factorize_local_binder l with
          (lna,false,ty') :: l when ty=ty' ->
            (na::lna,false,ty') :: l
        | l -> ([na],false,ty) :: l)


let ast_of_rawconstr = ast_of_raw

(******************************************************************)
(* Main translation function from constr -> ast *)
       
let ast_of_constr at_top env t =
  let t' =
    if !print_casts then t
    else Reductionops.local_strong strip_outer_cast t in
  let avoid = if at_top then ids_of_context env else [] in
  ast_of_raw 
    (Detyping.detype (at_top,env) avoid (names_of_rel_context env) t')

let ast_of_constant env sp =
  let a = ast_of_constant_ref sp in
  a

let ast_of_existential env (ev,ids) =
  let a = ast_of_existential_ref ev in
  if !print_arguments or !print_evar_arguments then
    ope("INSTANCE",a::(array_map_to_list (ast_of_constr false env) ids))
  else a

let ast_of_constructor env cstr_sp =
  let a = ast_of_constructor_ref cstr_sp in
  a

let ast_of_inductive env ind_sp =
  let a = ast_of_inductive_ref ind_sp in
  a

let decompose_binder_pattern = function
  | PProd(na,ty,c) -> Some (BProd,na,ty,c)
  | PLambda(na,ty,c) -> Some (BLambda,na,ty,c)
  | PLetIn(na,b,c) -> Some (BLetIn,na,b,c)
  | _ -> None

let rec ast_of_pattern tenv env = function
  | PRef ref -> ast_of_ref ref

  | PVar id -> ast_of_ident id

  | PEvar (n,_) -> ast_of_existential_ref n

  | PRel n ->
      (try match lookup_name_of_rel n env with
	 | Name id   -> ast_of_ident id
	 | Anonymous ->
	     anomaly "ast_of_pattern: index to an anonymous variable"
       with Not_found ->
	 nvar (id_of_string ("[REL "^(string_of_int n)^"]")))

  | PApp (f,args) ->
      let (f,args) = 
	skip_coercion (function PRef r -> Some r | _ -> None)
	  (f,Array.to_list args) in
      let astf = ast_of_pattern tenv env f in
      let astargs = List.map (ast_of_pattern tenv env) args in
      (match f with 
	 | PRef ref -> ast_of_app (implicits_of_global ref) astf astargs
	 | _        -> ast_of_app [] astf astargs)

  | PSoApp (n,args) ->
      ope("SOAPP",(ope ("META",[ast_of_ident n])):: 
		  (List.map (ast_of_pattern tenv env) args))

  | PLetIn (na,b,c) ->
      let c' = ast_of_pattern tenv (add_name na env) c in
      ope("LETIN",[ast_of_pattern tenv env b;slam(idopt_of_name na,c')])
		
  | PProd (Anonymous,t,c) ->
      ope("PROD",[ast_of_pattern tenv env t;
                  slam(None,ast_of_pattern tenv env c)])
  | PProd (na,t,c) ->
      let env' = add_name na env in
      let (n,a) =
	factorize_binder_pattern tenv env' 1 BProd na
          (ast_of_pattern tenv env t) c in
      (* PROD et PRODLIST doivent être distingués à cause du cas *)
      (* non dépendant, pour isoler l'implication; peut-être un *)
      (* constructeur ARROW serait-il plus justifié ? *) 
      let tag = if n=1 then "PROD" else "PRODLIST" in
      ope(tag,[ast_of_pattern tenv env t;a])
  | PLambda (na,t,c) ->
      let env' = add_name na env in
      let (n,a) =
	factorize_binder_pattern tenv env' 1 BLambda na
          (ast_of_pattern tenv env t) c in
      (* LAMBDA et LAMBDALIST se comportent pareil *)
      let tag = if n=1 then "LAMBDA" else "LAMBDALIST" in
      ope(tag,[ast_of_pattern tenv env t;a])

  | PCase (st,typopt,tm,bv) ->
      warning "Old Case syntax";
      ope("MUTCASE",(ast_of_patopt tenv env typopt)
	    ::(ast_of_pattern tenv env tm)
	    ::(Array.to_list (Array.map (ast_of_pattern tenv env) bv)))

  | PSort s ->
      (match s with
	 | RProp Null -> ope("PROP",[])
	 | RProp Pos -> ope("SET",[])
	 | RType _ -> ope("TYPE",[]))

  | PMeta (Some n) -> ope("META",[ast_of_ident n])
  | PMeta None -> ope("ISEVAR",[])
  | PFix f -> ast_of_raw (Detyping.detype (false,tenv) [] env (mkFix f))
  | PCoFix c -> ast_of_raw (Detyping.detype (false,tenv) [] env (mkCoFix c))
	
and ast_of_patopt tenv env = function
  | None -> (string "SYNTH")
  | Some p -> ast_of_pattern tenv env p

and factorize_binder_pattern tenv env n oper na aty c =
  let (p,body) = match decompose_binder_pattern c with
    | Some (oper',na',ty',c')
	when (oper = oper') & (aty = ast_of_pattern tenv env ty')
	  & not (na' = Anonymous & oper = BProd)
	  ->
	factorize_binder_pattern tenv (add_name na' env) (n+1) oper na' aty c'
    | _ -> (n,ast_of_pattern tenv env c)
  in
  (p,slam(idopt_of_name na, body))
