
(* $Id$ *)

open Pp
open Util
open Univ
open Names
open Term
open Inductive
open Sign
open Environ
open Declare
open Impargs
open Coqast
open Ast
open Rawterm
open Pattern

(* In this file, we translate rawconstr to ast, in order to print constr *)

(**********************************************************************)
(* Parametrization                                                    *)

(* This governs printing of local context of references *)
let print_arguments = ref false

(* If true, prints local context of evars, whatever print_arguments *)
let print_evar_arguments = ref false

(* This forces printing of cast nodes *)
let print_casts = ref true

(* This governs printing of implicit arguments.  When
   [print_implicits] is on then [print_implicits_explicit_args] tells
   how implicit args are printed. If on, implicit args are printed
   prefixed by "!" otherwise the function and not the arguments is
   prefixed by "!" *)
let print_implicits = ref false
let print_implicits_explicit_args = ref false

(* This forces printing of coercions *)
let print_coercions = ref false

let with_option o f x =
  let old = !o in o:=true;
  try let r = f x in o := old; r
  with e -> o := old; raise e

let with_arguments f = with_option print_arguments f
let with_casts f = with_option print_casts f
let with_implicits f = with_option print_implicits f
let with_coercions f = with_option print_coercions f

(**********************************************************************)
(* conversion of references                                           *)

let ids_of_ctxt ctxt =
  Array.to_list
    (Array.map
       (function c -> match kind_of_term c with
	  | IsVar id -> id
	  | _ ->
       error
       "Termast: arbitrary substitution of references not yet implemented")
     ctxt)

let ast_of_ident id = nvar (string_of_id id)

let ast_of_name = function 
  | Name id -> nvar (string_of_id id)
  | Anonymous -> nvar "_"

let stringopt_of_name = function 
  | Name id -> Some (string_of_id id)
  | Anonymous -> None

let ast_of_constant_ref pr (sp,ids) =
  let a = ope("CONST", [path_section dummy_loc sp]) in
  if !print_arguments then ope("INSTANCE",a::(array_map_to_list pr ids))
  else a

let ast_of_existential_ref pr  (ev,ids) =
  let a = ope("EVAR", [num ev]) in
  if !print_arguments or !print_evar_arguments then
    ope("INSTANCE",a::(array_map_to_list pr ids))
  else a

let ast_of_constructor_ref pr  (((sp,tyi),n) as cstr_sp,ids) =
  let a = ope("MUTCONSTRUCT",[path_section dummy_loc sp; num tyi; num n]) in
  if !print_arguments then ope("INSTANCE",a::(array_map_to_list pr ids))
  else a

let ast_of_inductive_ref pr  ((sp,tyi) as ind_sp,ids) =
  let a = ope("MUTIND",	[path_section dummy_loc sp; num tyi]) in
  if !print_arguments then ope("INSTANCE",a::(array_map_to_list pr ids))
  else a

let ast_of_ref pr r =
  (* TODO gérer le ctxt *)
  let ctxt = [||] in match r with
  | ConstRef sp -> ast_of_constant_ref pr (sp,ctxt)
  | IndRef sp -> ast_of_inductive_ref pr (sp,ctxt)
  | ConstructRef sp -> ast_of_constructor_ref pr (sp,ctxt)
  | VarRef sp -> ast_of_ident (basename sp)
  | EvarRef ev -> ast_of_existential_ref pr (ev,ctxt)

let ast_of_qualid p =
  let dir, s = repr_qualid p in
  let args = List.map nvar (dir@[s]) in
  ope ("QUALID", args)

(**********************************************************************)
(* conversion of patterns                                             *)

let adapt (cstr_sp,ctxt) = (cstr_sp,Array.of_list ctxt)

let rec ast_of_cases_pattern = function   (* loc is thrown away for printing *)
  | PatVar (loc,Name id) -> nvar (string_of_id id)
  | PatVar (loc,Anonymous) -> nvar "_"
  | PatCstr(loc,cstr,args,Name id) ->
      let args = List.map ast_of_cases_pattern args in
      ope("PATTAS",
	  [nvar (string_of_id id);
	   ope("PATTCONSTRUCT",
	       (ast_of_constructor_ref ast_of_ident (adapt cstr))::args)])
  | PatCstr(loc,cstr,args,Anonymous) ->
      ope("PATTCONSTRUCT",
	  (ast_of_constructor_ref ast_of_ident (adapt cstr))::
	  List.map ast_of_cases_pattern args)
	
let ast_dependent na aty =
  match na with
    | Name id -> occur_var_ast (string_of_id id) aty
    | Anonymous -> false

(* Implicit args indexes are in ascending order *)
let explicitize =
  let rec exprec n lastimplargs impl = function
    | a::args ->
	(match impl with
	   | i::l when i=n ->
	       exprec (n+1) (ope("EXPL", [num i; a])::lastimplargs) l args
	   | _ ->
	       let tail = a::(exprec (n+1) [] impl args) in
	       if (!print_implicits & !print_implicits_explicit_args) then
		 List.rev_append lastimplargs tail
	       else tail)
    (* Tail impl args are always printed even if implicit printing is off *)
    | [] -> List.rev lastimplargs
  in exprec 1 []

let rec skip_coercion dest_ref (f,args as app) =
  if !print_coercions then app
  else
    try
      match dest_ref f with
	| Some r ->
	    let n = Classops.coercion_params r in
	    if n >= List.length args then app
	    else (* We skip a coercion *)
	      let _,fargs = list_chop n args in
	      skip_coercion dest_ref (List.hd fargs,List.tl fargs)
	| None -> app
    with Not_found -> app

let ast_of_app impl f args =
  if !print_implicits & not !print_implicits_explicit_args then 
    ope("APPLISTEXPL", f::args)
  else
    ope("APPLIST", f::(explicitize impl args))
(*
    let largs = List.length args in
    let impl = List.rev (List.filter (fun i -> i <= largs) impl) in
    let impl1,impl2 = div_implicits largs impl in
    let al1 = Array.of_list args in
    List.iter
      (fun i -> al1.(i) <-
         ope("EXPL", [str "EX"; num i; al1.(i)]))
      impl2;
    List.iter
      (fun i -> al1.(i) <-
         ope("EXPL",[num i; al1.(i)]))
      impl1;
    (* On laisse les implicites, à charge du PP de ne pas les imprimer *)
    ope("APPLISTEXPL",f::(Array.to_list al1))
*)

let rec ast_of_raw = function
  | RRef (_,ref) -> ast_of_ref ast_of_raw ref
  | RVar (_,id) -> ast_of_ident id
  | RMeta (_,n) -> ope("META",[num n])
  | RApp (_,f,args) ->
      let (f,args) =
	skip_coercion (function RRef(_,r) -> Some r | _ -> None) (f,args) in
      let astf = ast_of_raw f in
      let astargs = List.map ast_of_raw args in
      (match f with 
	 | RRef (_,ref) -> ast_of_app (implicits_of_global ref) astf astargs
	 | RVar (_,id) ->
	     let imp =
	       try 
		 let ref = Nametab.locate (make_qualid [] (string_of_id id)) in
		 implicits_of_global ref
	       with Not_found -> [] in
	     ast_of_app imp astf astargs
	 | _       -> ast_of_app [] astf astargs)
  | RBinder (_,BProd,Anonymous,t,c) ->
      (* Anonymous product are never factorized *)
      ope("PROD",[ast_of_raw t; slam(None,ast_of_raw c)])
  | RBinder (_,BLetIn,na,t,c) ->
      ope("LETIN",[ast_of_raw t; slam(stringopt_of_name na,ast_of_raw c)])
  | RBinder (_,bk,na,t,c) ->
      let (n,a) = factorize_binder 1 bk na (ast_of_raw t) c in
      let tag = match bk with
	  (* LAMBDA et LAMBDALIST se comportent pareil ... Non ! *)
	  (* Pour compatibilité des theories, il faut LAMBDALIST partout *)
	| BLambda -> (* if n=1 then "LAMBDA" else *) "LAMBDALIST"
	  (* PROD et PRODLIST doivent être distingués à cause du cas *)
	  (* non dépendant, pour isoler l'implication; peut-être un *)
	  (* constructeur ARROW serait-il plus justifié ? *) 
	| BProd -> if n=1 then "PROD" else "PRODLIST" 
	| BLetIn -> if n=1 then "LETIN" else "LETINLIST" 
      in
      ope(tag,[ast_of_raw t;a])

  | RCases (_,printinfo,typopt,tml,eqns) ->
      let pred = ast_of_rawopt typopt in
      let tag = match printinfo with
	| PrintIf -> "FORCEIF"
	| PrintLet -> "FORCELET"
	| PrintCases -> "CASES" 
      in
      let asttomatch = ope("TOMATCH", List.map ast_of_raw tml) in
      let asteqns = List.map ast_of_eqn eqns in 
      ope(tag,pred::asttomatch::asteqns)
	
  | ROldCase (_,isrec,typopt,tm,bv) ->
      warning "Old Case syntax";
      ope("MUTCASE",(ast_of_rawopt typopt)
	    ::(ast_of_raw tm)
	    ::(Array.to_list (Array.map ast_of_raw bv)))
  | RRec (_,fk,idv,tyv,bv) ->
      let alfi = Array.map ast_of_ident idv in
      (match fk with
	 | RFix (nv,n) ->
             let rec split_lambda binds = function
	       | (0, t) -> (binds,ast_of_raw t)
	       | (n, RBinder(_,BLambda,na,t,b)) ->
		   let bind = ope("BINDER",[ast_of_raw t;ast_of_name na]) in
		   split_lambda (bind::binds) (n-1,b)
	       | _ -> anomaly "ast_of_rawconst: ill-formed fixpoint body" in
	     let rec split_product = function
	       | (0, t) -> ast_of_raw t
	       | (n, RBinder(_,BProd,na,t,b)) -> split_product (n-1,b)
	       | _ -> anomaly "ast_of_rawconst: ill-formed fixpoint type" in
	     let listdecl = 
	       Array.mapi
		 (fun i fi ->
		    let (lparams,astdef) = split_lambda [] (nv.(i)+1,bv.(i)) in
		    let asttyp = split_product (nv.(i)+1,tyv.(i)) in
		    ope("FDECL",
		       	[fi; ope ("BINDERS",List.rev lparams); 
			 asttyp; astdef]))
		 alfi
	     in 
	     ope("FIX", alfi.(n)::(Array.to_list listdecl))
	 | RCoFix n -> 
	     let listdecl =
               Array.mapi 
		 (fun i fi ->
		    ope("CFDECL",[fi; ast_of_raw tyv.(i); ast_of_raw bv.(i)]))
		 alfi
	     in 
	     ope("COFIX", alfi.(n)::(Array.to_list listdecl)))

  | RSort (_,s) ->
      (match s with
	 | RProp Null -> ope("PROP",[])
	 | RProp Pos -> ope("SET",[])
	 | RType -> ope("TYPE",[]))
  | RHole _ -> ope("ISEVAR",[])
  | RCast (_,c,t) -> ope("CAST",[ast_of_raw c;ast_of_raw t])
	
and ast_of_eqn (ids,pl,c) =
  ope("EQN", (ast_of_raw c)::(List.map ast_of_cases_pattern pl))

and ast_of_rawopt = function
  | None -> (str "SYNTH")
  | Some p -> ast_of_raw p

and factorize_binder n oper na aty c =
  let (p,body) = match c with
    | RBinder(_,oper',na',ty',c')
	when (oper = oper') & (aty = ast_of_raw ty')
	  & not (ast_dependent na aty) (* To avoid na in ty' escapes scope *)
	  & not (na' = Anonymous & oper = BProd)
	  -> factorize_binder (n+1) oper na' aty c'
    | _ -> (n,ast_of_raw c)
  in
  (p,slam(stringopt_of_name na, body))

let ast_of_rawconstr = ast_of_raw

(******************************************************************)
(* Main translation function from constr -> ast *)
       
let ast_of_constr at_top env t =
  let t' =
    if !print_casts then t
    else Reduction.local_strong strip_outer_cast t in
  let avoid = if at_top then ids_of_context env else [] in
  ast_of_raw 
    (Detyping.detype avoid (names_of_rel_context env) t')

let ast_of_constant env    = ast_of_constant_ref (ast_of_constr false env)

let ast_of_existential env = ast_of_existential_ref (ast_of_constr false env)

let ast_of_inductive env   = ast_of_inductive_ref (ast_of_constr false env)

let ast_of_constructor env = ast_of_constructor_ref (ast_of_constr false env)

let rec ast_of_pattern env = function
  | PRef ref -> ast_of_ref (fun c -> ast_of_raw (Detyping.detype [] env c)) ref

  | PVar id -> ast_of_ident id

  | PRel n ->
      (try match lookup_name_of_rel n env with
	 | Name id   -> ast_of_ident id
	 | Anonymous ->
	     anomaly "ast_of_pattern: index to an anonymous variable"
       with Not_found ->
	 let s = "[REL "^(string_of_int n)^"]"
	 in nvar s)

  | PApp (f,args) ->
      let (f,args) = 
	skip_coercion (function PRef r -> Some r | _ -> None)
	  (f,Array.to_list args) in
      let astf = ast_of_pattern env f in
      let astargs = List.map (ast_of_pattern env) args in
      (match f with 
	 | PRef ref -> ast_of_app (implicits_of_global ref) astf astargs
	 | _        -> ast_of_app [] astf astargs)

  | PSoApp (n,args) ->
      ope("SOAPP",(ope ("META",[num n])):: 
		  (List.map (ast_of_pattern env) args))

  | PBinder (BLetIn,na,b,c) ->
      let c' = ast_of_pattern (add_name na env) c in
      ope("LETIN",[ast_of_pattern env b;slam(stringopt_of_name na,c')])
		
  | PBinder (BProd,Anonymous,t,c) ->
      ope("PROD",[ast_of_pattern env t; slam(None,ast_of_pattern env c)])
  | PBinder (bk,na,t,c) ->
      let env' = add_name na env in
      let (n,a) = factorize_binder_pattern
		    env' 1 bk na (ast_of_pattern env t) c in
      let tag = match bk with
	  (* LAMBDA et LAMBDALIST se comportent pareil *)
	| BLambda -> if n=1 then "LAMBDA" else "LAMBDALIST"
	  (* PROD et PRODLIST doivent être distingués à cause du cas *)
	  (* non dépendant, pour isoler l'implication; peut-être un *)
	  (* constructeur ARROW serait-il plus justifié ? *) 
	| BProd -> if n=1 then "PROD" else "PRODLIST" 
	| BLetIn -> anomaly "Should be captured before"
      in
      ope(tag,[ast_of_pattern env t;a])

  | PCase (typopt,tm,bv) ->
      warning "Old Case syntax";
      ope("MUTCASE",(ast_of_patopt env typopt)
	    ::(ast_of_pattern env tm)
	    ::(Array.to_list (Array.map (ast_of_pattern env) bv)))

  | PSort s ->
      (match s with
	 | RProp Null -> ope("PROP",[])
	 | RProp Pos -> ope("SET",[])
	 | RType -> ope("TYPE",[]))

  | PMeta (Some n) -> ope("META",[num n])
  | PMeta None -> ope("ISEVAR",[])
  | PFix f -> ast_of_raw (Detyping.detype [] env (mkFix f))
  | PCoFix c -> ast_of_raw (Detyping.detype [] env (mkCoFix c))
	
and ast_of_patopt env = function
  | None -> (str "SYNTH")
  | Some p -> ast_of_pattern env p

and factorize_binder_pattern env n oper na aty c =
  let (p,body) = match c with
    | PBinder(oper',na',ty',c')
	when (oper = oper') & (aty = ast_of_pattern env ty')
	  & not (na' = Anonymous & oper = BProd)
	  ->
	factorize_binder_pattern (add_name na' env) (n+1) oper na' aty c'
    | _ -> (n,ast_of_pattern env c)
  in
  (p,slam(stringopt_of_name na, body))
