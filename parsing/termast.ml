
(* $Id$ *)

open Pp
open Util
open Univ
open Names
open Generic
open Term
open Inductive
open Sign
open Declare
open Impargs
open Coqast
open Ast
open Rawterm

(* In this file, we translate rawconstr to ast, in order to print constr *)

(**********************************************************************)
(* Parametrization                                                    *)

(* This governs printing of local context of references *)
let print_arguments = ref false

(* This forces printing of cast nodes *)
let print_casts = ref false

(* This governs printing of implicit arguments.  When
   [print_implicits] is on then [print_implicits_explicit_args] tells
   how jimplicit args are printed. If on, implicit args are printed
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

let ids_of_ctxt = array_map_to_list (function VAR id -> id | _ -> assert false)

let ast_of_ident id = nvar (string_of_id id)

let ast_of_name = function 
  | Name id -> nvar (string_of_id id)
  | Anonymous -> nvar "_"

let stringopt_of_name = function 
  | Name id -> Some (string_of_id id)
  | Anonymous -> None

let ast_of_qualified sp id =
  if Nametab.sp_of_id (kind_of_path sp) id = sp then nvar (string_of_id id)
  else nvar (string_of_path sp)

let ast_of_constant_ref (sp,ids) =
  if !print_arguments then
    ope("CONST", (path_section dummy_loc sp)::(List.map ast_of_ident ids))
  else ast_of_qualified sp (basename sp)

let ast_of_constant (ev,ids) = ast_of_constant_ref (ev,ids_of_ctxt ids)

let ast_of_existential_ref (ev,ids) =
  if !print_arguments then
      ope("EVAR", (num ev)::(List.map ast_of_ident ids))
  else nvar ("?" ^ string_of_int ev)

let ast_of_existential (ev,ids) = ast_of_existential_ref (ev,ids_of_ctxt ids)

let ast_of_constructor_ref (((sp,tyi),n) as cstr_sp,ids) =
  if !print_arguments then
    ope("MUTCONSTRUCT",
	(path_section dummy_loc sp)::(num tyi)::(num n)
	::(List.map ast_of_ident ids))
  else ast_of_qualified sp (Global.id_of_global (MutConstruct cstr_sp))

let ast_of_constructor (ev,ids) = ast_of_constructor_ref (ev,ids_of_ctxt ids)

let ast_of_inductive_ref ((sp,tyi) as ind_sp,ids) =
  if !print_arguments then
    ope("MUTIND",
	(path_section dummy_loc sp)::(num tyi)::(List.map ast_of_ident ids))
  else ast_of_qualified sp (Global.id_of_global (MutInd ind_sp))

let ast_of_inductive (ev,ids) = ast_of_inductive_ref (ev,ids_of_ctxt ids)

let ast_of_ref = function
  | RConst (sp,ids) -> ast_of_constant_ref (sp,ids)
  | RAbst (sp) ->
      ope("ABST", (path_section dummy_loc sp)
	    ::(List.map ast_of_ident (* on triche *) []))
  | RInd (ind,ids) -> ast_of_inductive_ref (ind,ids)
  | RConstruct (cstr,ids) -> ast_of_constructor_ref (cstr,ids)
  | RVar id -> nvar (string_of_id id)
  | REVar (ev,ids) -> ast_of_existential_ref (ev,ids)
  | RMeta n -> ope("META",[num n])

(**********************************************************************)
(* conversion of patterns                                             *)

let rec ast_of_pattern = function   (* loc is thrown away for printing *)
  | PatVar (loc,Name id) -> nvar (string_of_id id)
  | PatVar (loc,Anonymous) -> nvar "_"
  | PatCstr(loc,cstr,args,Name id) ->
      ope("PATTAS",
	  [nvar (string_of_id id);
	   ope("PATTCONSTRUCT",
	       (ast_of_constructor_ref cstr)::List.map ast_of_pattern args)])
  | PatCstr(loc,cstr,args,Anonymous) ->
      ope("PATTCONSTRUCT",
	  (ast_of_constructor_ref cstr)::List.map ast_of_pattern args)
	
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
  in exprec 0 []

let implicit_of_ref = function
  | RConstruct (cstrid,_) -> constructor_implicits_list cstrid
  | RInd (indid,_) -> inductive_implicits_list indid
  | RConst (sp,_) -> constant_implicits_list sp
  | RVar id -> (try (implicits_of_var CCI id) with _ -> []) (* et FW? *)
  | _ -> []

let rec skip_coercion (f,args as app) =
  if !print_coercions then app
  else
    try
      match f with
	| RRef (_,r) ->
	    let n = Classops.coercion_params r in
	    if n >= List.length args then app
	    else (* We skip a coercion *)
	      let _,fargs = list_chop n args in
	      skip_coercion (List.hd fargs,List.tl fargs)
	| _ -> app
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
  | RRef (_,ref) -> ast_of_ref ref
  | RApp (_,f,args) ->
      let (f,args) = skip_coercion (f,args) in
      let astf = ast_of_raw f in
      let astargs = List.map ast_of_raw args in
      (match f with 
	 | RRef (_,ref) -> ast_of_app (implicit_of_ref ref) astf astargs
	 | _           -> ast_of_app [] astf astargs)
  | RBinder (_,BProd,Anonymous,t,c) ->
      (* Anonymous product are never factorized *)
      ope("PROD",[ast_of_raw t; slam(None,ast_of_raw c)])
  | RBinder (_,bk,na,t,c) ->
      let (n,a) = factorize_binder 1 bk na (ast_of_raw t) c in
      let tag = match bk with
	  (* LAMBDA et LAMBDALIST se comportent pareil *)
	| BLambda -> if n=1 then "LAMBDA" else "LAMBDALIST"
	  (* PROD et PRODLIST doivent être distingués à cause du cas *)
	  (* non dépendant, pour isoler l'implication; peut-être un *)
	  (* constructeur ARROW serait-il plus justifié ? *) 
	| BProd -> if n=1 then "PROD" else "PRODLIST" 
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
	 | RCofix n -> 
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
  ope("EQN", (ast_of_raw c)::(List.map ast_of_pattern pl))

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

(*****************************************************************)
(* TO EJECT ... REPRIS DANS detyping *)


(* Nouvelle version de renommage des variables (DEC 98) *)
(* This is the algorithm to display distinct bound variables 

    - Règle 1 : un nom non anonyme, même non affiché, contribue à la liste
      des noms à éviter 
    - Règle 2 : c'est la dépendance qui décide si on affiche ou pas

    Exemple : 
    si bool_ind = (P:bool->Prop)(f:(P true))(f:(P false))(b:bool)(P b), alors
    il est affiché (P:bool->Prop)(P true)->(P false)->(b:bool)(P b)
    mais f et f0 contribue à la liste des variables à éviter (en supposant 
    que les noms f et f0 ne sont pas déjà pris)
    Intérêt : noms homogènes dans un but avant et après Intro
*)

type used_idents = identifier list

let occur_id env id0 c =
  let rec occur n = function
    | VAR id             -> id=id0
    | DOPN (Const sp,cl) -> (basename sp = id0) or (array_exists (occur n) cl)
    | DOPN (Abst sp,cl)  -> (basename sp = id0) or (array_exists (occur n) cl)
    | DOPN (MutInd ind_sp, cl) as t -> 
  	(basename (path_of_inductive_path ind_sp) = id0)
	or (array_exists (occur n) cl)
    | DOPN (MutConstruct cstr_sp, cl) as t -> 
    	(basename (path_of_constructor_path cstr_sp) = id0)
	or (array_exists (occur n) cl)
    | DOPN(_,cl)         -> array_exists (occur n) cl
    | DOP1(_,c)          -> occur n c
    | DOP2(_,c1,c2)      -> (occur n c1) or (occur n c2)
    | DOPL(_,cl)         -> List.exists (occur n) cl
    | DLAM(_,c)          -> occur (n+1) c
    | DLAMV(_,v)         -> array_exists (occur (n+1)) v
    | Rel p              ->
    	p>n &
    	(try (fst (lookup_rel (p-n) env) = Name id0)
	 with Not_found -> false) (* Unbound indice : may happen in debug *)
    | DOP0 _             -> false
  in 
  occur 1 c

let next_name_not_occuring name l env t =
  let rec next id =
    if List.mem id l or occur_id env id t then next (lift_ident id) else id
  in 
  match name with
    | Name id   -> next id
    | Anonymous -> id_of_string "_"

(* Remark: Anonymous var may be dependent in Evar's contexts *)
let concrete_name l env n c =
  if n = Anonymous & not (dependent (Rel 1) c) then
    (None,l)
  else
    let fresh_id = next_name_not_occuring n l env c in
    let idopt = if dependent (Rel 1) c then (Some fresh_id) else None in
    (idopt, fresh_id::l)

    (* Returns the list of global variables and constants in a term *)
let global_vars_and_consts t =
  let rec collect acc = function
    | VAR id             -> id::acc
    | DOPN (Const sp,cl) -> (basename sp)::(Array.fold_left collect acc cl)
    | DOPN (Abst sp,cl)  -> (basename sp)::(Array.fold_left collect acc cl)
    | DOPN (MutInd ind_sp, cl) as t       -> 
	(basename (path_of_inductive_path ind_sp))
	::(Array.fold_left collect acc cl)
    | DOPN (MutConstruct cstr_sp, cl) as t -> 
	(basename (path_of_constructor_path cstr_sp))
	::(Array.fold_left collect acc cl)
    | DOPN(_,cl)         -> Array.fold_left collect acc cl
    | DOP1(_,c)          -> collect acc c
    | DOP2(_,c1,c2)      -> collect (collect acc c1) c2
    | DOPL(_,cl)         -> List.fold_left collect acc cl
    | DLAM(_,c)          -> collect acc c
    | DLAMV(_,v)         -> Array.fold_left collect acc v
    | _                  -> acc
  in
  list_uniquize (collect [] t)
    
let used_of = global_vars_and_consts
let ids_of_env = Sign.ids_of_env


(****************************************************************************)
(* Tools for printing of Cases                                              *)
(* These functions implement a light form of Termenv.mind_specif_of_mind    *)
(* specially for handle Cases printing; they respect arities but not typing *)

let indsp_of_id id  =
  let (oper,_) =
    try 
      let sp = Nametab.sp_of_id CCI id in global_operator sp id
    with Not_found -> 
      error ("Cannot find reference "^(string_of_id id))
  in
  match oper with
    | MutInd(sp,tyi) -> (sp,tyi)
    | _ -> errorlabstrm "indsp_of_id" 
	  [< 'sTR ((string_of_id id)^" is not an inductive type") >]
	  
let mind_specif_of_mind_light (sp,tyi) =
  let mib = Global.lookup_mind sp in
  (mib,mind_nth_type_packet mib tyi)

let rec remove_indtypes = function
  | (1, DLAMV(_,cl)) -> cl
  | (n, DLAM (_,c))  -> remove_indtypes (n-1, c)
  | _                -> anomaly "remove_indtypes: bad list of constructors"

let rec remove_params n t =
  if n = 0 then 
    t
  else 
    match t with
      | DOP2(Prod,_,DLAM(_,c)) -> remove_params (n-1) c
      | DOP2(Cast,c,_)         -> remove_params n c
      | _ -> anomaly "remove_params : insufficiently quantified"
	    
let rec get_params = function
  | DOP2(Prod,_,DLAM(x,c)) -> x::(get_params c)
  | DOP2(Cast,c,_)         -> get_params c
  | _                      -> []

let lc_of_lmis (mib,mip) =
  let lc = remove_indtypes (mib.mind_ntypes,mip.mind_lc) in
  Array.map (remove_params mib.mind_nparams) lc

let sp_of_spi ((sp,_) as spi) =
  let (_,mip) = mind_specif_of_mind_light spi in
  let (pa,_,k) = repr_path sp in 
  make_path pa (mip.mind_typename) k

let bdize_app c al =
  let impl =
    match c with
      | DOPN(MutConstruct constr_sp,_) -> constructor_implicits_list constr_sp
      | DOPN(MutInd ind_sp,_) -> inductive_implicits_list ind_sp
      | DOPN(Const sp,_) -> constant_implicits_list sp
      | VAR id -> (try (implicits_of_var CCI id) with _ -> []) (* et FW? *)
      | _ -> []
  in
  if !print_implicits then 
    ope("APPLISTEXPL", al)
  else
    ope("APPLIST", explicitize impl al)

(* Auxiliary function for MutCase printing *)
(* [computable] tries to tell if the predicate typing the result is inferable*)

let computable p k =
    (* We first remove as many lambda as the arity, then we look
       if it remains a lambda for a dependent elimination. This function
       works for normal eta-expanded term. For non eta-expanded or
       non-normal terms, it may affirm the pred is synthetisable
       because of an undetected ultimate dependent variable in the second
       clause, or else, it may affirms the pred non synthetisable
       because of a non normal term in the fourth clause.
       A solution could be to store, in the MutCase, the eta-expanded
       normal form of pred to decide if it depends on its variables

       Lorsque le prédicat est dépendant de manière certaine, on
       ne déclare pas le prédicat synthétisable (même si la
       variable dépendante ne l'est pas effectivement) parce que
       sinon on perd la réciprocité de la synthèse (qui, lui,
       engendrera un prédicat non dépendant) *)

  let rec striprec = function
    | (0,DOP2(Lambda,_,DLAM(_,d))) -> false
    | (0,d               )         -> noccur_bet 1 k d
    | (n,DOP2(Lambda,_,DLAM(_,d))) -> striprec (n-1,d)
    |  _                           -> false
  in 
  striprec (k,p)

let ids_of_var cl =
  List.map
    (function 
       | RRef (_,RVar id) -> id
       | _-> anomaly "ids_of_var")
    (Array.to_list cl)

(* Main translation function from constr -> ast *)

let old_bdize at_top env t =
  let init_avoid = if at_top then ids_of_env env else [] in
  let rec bdrec avoid env t = match collapse_appl t with
    (* Not well-formed constructions *)
    | DLAM(na,c) ->
	(match concrete_name avoid env na c with
           | (Some id,avoid') -> 
	       slam(Some (string_of_id id),
                    bdrec avoid' (add_rel (Name id,()) env) c)
           | (None,avoid') -> 
	       slam(None,bdrec avoid' env (pop c)))
    | DLAMV(na,cl) ->
	if not(array_exists (dependent (Rel 1)) cl) then
	  slam(None,ope("V$",array_map_to_list
			  (fun c -> bdrec avoid env (pop c)) cl))
	else
	  let id = next_name_away na avoid in 
	  slam(Some (string_of_id id),
	       ope("V$", array_map_to_list
		     (bdrec (id::avoid) (add_rel (Name id,()) env)) cl))
	    
    (* Well-formed constructions *)
    | regular_constr -> 
	(match kind_of_term regular_constr with
	   | IsRel n ->
	       (try 
		  match fst(lookup_rel n env) with
		    | Name id   -> nvar (string_of_id id)
		    | Anonymous -> raise Not_found
		with Not_found -> 
		  ope("REL",[num n]))
	     (* TODO: Change this to subtract the current depth *)
	   | IsMeta n -> ope("META",[num n])
	   | IsVar id -> nvar (string_of_id id)
	   | IsXtra s -> ope("XTRA",[str s])
	   | IsSort s ->
	       (match s with
		  | Prop Null -> ope("PROP",[])
		  | Prop Pos -> ope("SET",[])
		  | Type u -> 
		      ope("TYPE",
			  [path_section dummy_loc u.u_sp; num u.u_num]))
	   | IsCast (c1,c2) ->
	       if !print_casts then 
		 bdrec avoid env c1 
	       else 
		 ope("CAST",[bdrec avoid env c1;bdrec avoid env c2])
	   | IsProd (Anonymous,ty,c) ->
                    (* Anonymous product are never factorized *)
	       ope("PROD",[bdrec [] env ty;
			   slam(None,bdrec avoid env (pop c))])
	   | IsProd (Name _ as na,ty,c) ->
	       let (n,a) = factorize_binder 1 avoid env Prod na ty c in
               (* PROD et PRODLIST doivent être distingués à cause du cas
                  non dépendant, pour isoler l'implication; peut-être 
	          un constructeur ARROW serait-il plus justifié ? *)
	       let oper = if n=1 then "PROD" else "PRODLIST" in
	       ope(oper,[bdrec [] env ty;a])
	   | IsLambda (na,ty,c) ->
	       let (n,a) = factorize_binder 1 avoid env Lambda na ty c in
               (* LAMBDA et LAMBDALIST se comportent pareil *)
	       let oper = if n=1 then "LAMBDA" else "LAMBDALIST" in
	       ope(oper,[bdrec [] env ty;a])
	   | IsAppL (f,args) ->
	       bdize_app f (List.map (bdrec avoid env) (f::args))
	   | IsConst (sp,cl) ->
	       ope("CONST",((path_section dummy_loc sp)::
			    (array_map_to_list (bdrec avoid env) cl)))
	   | IsEvar (ev,cl) ->
	       ope("EVAR",((num ev)::
			   (array_map_to_list (bdrec avoid env) cl)))
	   | IsAbst (sp,cl) ->
	       ope("ABST",((path_section dummy_loc sp)::
			   (array_map_to_list (bdrec avoid env) cl)))
	   | IsMutInd ((sp,tyi),cl) ->
	       ope("MUTIND",((path_section dummy_loc sp)::(num tyi)::
			     (array_map_to_list (bdrec avoid env) cl)))
	   | IsMutConstruct (((sp,tyi),n),cl) ->
	       ope("MUTCONSTRUCT",
		   ((path_section dummy_loc sp)::(num tyi)::(num n)::
		    (array_map_to_list (bdrec avoid env) cl)))
	   | IsMutCase (annot,p,c,bl) ->
	       let synth_type = Detyping.synthetize_type () in
	       let tomatch = bdrec avoid env c in
	       begin 
		 match annot with
(*		 | None -> 
	             (* Pas d'annotation --> affichage avec vieux Case *)
		     let pred = bdrec avoid env p in
		     let bl' = array_map_to_list (bdrec avoid env) bl in
		     ope("MUTCASE",pred::tomatch::bl')
		 | Some *) indsp ->
		     let (mib,mip as lmis) = 
		       mind_specif_of_mind_light indsp in
		     let lc = lc_of_lmis lmis in
		     let lcparams = Array.map get_params lc in
		     let k = (nb_prod mip.mind_arity.body) - 
			     mib.mind_nparams in
		     let pred = 
		       if synth_type & computable p k & lcparams <> [||] then
			 (str "SYNTH")
		       else 
			 bdrec avoid env p 
		     in
		     if Detyping.force_if indsp then 
		       ope("FORCEIF", [ pred; tomatch;
					bdrec avoid env bl.(0); 
					bdrec avoid env bl.(1) ])
		     else
		       let idconstructs = mip.mind_consnames in
		       let asttomatch = ope("TOMATCH", [tomatch]) in
		       let eqnv =
			 array_map3 (bdize_eqn avoid env) idconstructs
			   lcparams bl in
		       let eqnl = Array.to_list eqnv in
		       let tag =
			 if Detyping.force_let indsp then 
			   "FORCELET" 
			 else 
			   "CASES"
		       in 
		       ope(tag,pred::asttomatch::eqnl)
	       end
	       
	   | IsFix (nv,n,cl,lfn,vt) ->
	       let lfi = List.map (fun na -> next_name_away na avoid) lfn in
	       let def_env = 
		 List.fold_left
		   (fun env id -> add_rel (Name id,()) env) env lfi in
	       let def_avoid = lfi@avoid in
	       let f = List.nth lfi n in
	       let rec split_lambda binds env avoid = function
		 | (0, t) -> (binds,bdrec avoid env t)
		 | (n, DOP2(Cast,t,_)) -> split_lambda binds env avoid (n,t)
		 | (n, DOP2(Lambda,t,DLAM(na,b))) ->
		     let ast = bdrec avoid env t in
		     let id = next_name_away na avoid in
		     let ast_of_bind = 
		       ope("BINDER",[ast;nvar (string_of_id id)]) in
		     let new_env = add_rel (Name id,()) env in
		     split_lambda (ast_of_bind::binds) 
		       new_env (id::avoid) (n-1,b)
		 | _ -> error "split_lambda" 
	       in
	       let rec split_product env avoid = function
		 | (0, t) -> bdrec avoid env t
		 | (n, DOP2(Cast,t,_)) -> split_product env avoid (n,t)
		 | (n, DOP2(Prod,t,DLAM(na,b))) ->
		     let ast = bdrec avoid env t in
		     let id = next_name_away na avoid in
		     let new_env = add_rel (Name id,()) env in
		     split_product new_env (id::avoid) (n-1,b)
		 | _ -> error "split_product" 
	       in
	       let listdecl = 
		 list_map_i
		   (fun i fi ->
		      let (lparams,ast_of_def) =
			split_lambda [] def_env def_avoid (nv.(i)+1,vt.(i)) in
		      let ast_of_typ = 
			split_product env avoid (nv.(i)+1,cl.(i)) in
		      ope("FDECL",
			  [nvar (string_of_id fi); 
			   ope ("BINDERS",List.rev lparams);
			   ast_of_typ; ast_of_def ]))
		   0 lfi 
	       in 
	       ope("FIX", (nvar (string_of_id f))::listdecl)

	   | IsCoFix (n,cl,lfn,vt) ->
	       let lfi = List.map (fun na -> next_name_away na avoid) lfn in
	       let def_env =
		 List.fold_left 
		   (fun env id -> add_rel (Name id,()) env) env lfi in
	       let def_avoid = lfi@avoid in
	       let f = List.nth lfi n in
	       let listdecl =
		 list_map_i (fun i fi -> ope("CFDECL",
					     [nvar (string_of_id fi);
					      bdrec avoid env cl.(i);
					      bdrec def_avoid def_env vt.(i)]))
		   0 lfi
	       in 
	       ope("COFIX", (nvar (string_of_id f))::listdecl))

  and bdize_eqn avoid env constructid construct_params branch =
    let print_underscore = Detyping.force_wildcard () in
    let cnvar = nvar (string_of_id constructid) in
    let rec buildrec nvarlist avoid env = function

	_::l, DOP2(Lambda,_,DLAM(x,b))
	-> let x'=
          if not print_underscore or (dependent (Rel 1) b) then x 
          else Anonymous in
           let id = next_name_away x' avoid in
           let new_env = (add_rel (Name id,()) env) in
           let new_avoid = id::avoid in
           let new_nvarlist = (nvar (string_of_id id))::nvarlist in
             buildrec new_nvarlist new_avoid new_env (l,b)
	       
      | l   , DOP2(Cast,b,_)     (* Oui, il y a parfois des cast *)
	-> buildrec nvarlist avoid env (l,b)
	  
      | x::l, b (* eta-expansion : n'arrivera plus lorsque tous les
                   termes seront construits à partir de la syntaxe Cases *)
	-> (* nommage de la nouvelle variable *)
          let id = next_name_away_with_default "x" x avoid in
	  let new_nvarlist = (nvar (string_of_id id))::nvarlist in
          let new_env = (add_rel (Name id,()) env) in
          let new_avoid = id::avoid in
          let new_b = DOPN(AppL,[|lift 1 b; Rel 1|]) in
            buildrec new_nvarlist new_avoid new_env (l,new_b)

      | []  , b
	-> let pattern =
          if nvarlist = [] then cnvar
          else ope ("PATTCONSTRUCT", cnvar::(List.rev nvarlist)) in
	   let action = bdrec avoid env b in
	     ope("EQN", [action; pattern])

    in buildrec [] avoid env (construct_params,branch)

  and factorize_binder n avoid env oper na ty c =
    let (env2, avoid2,na2) =
      match concrete_name avoid env na c with
	  (Some id,l') -> add_rel (Name id,()) env, l', Some (string_of_id id) 
	| (None,l')    -> add_rel (Anonymous,()) env, l', None
    in
    let (p,body) = match c with
	DOP2(oper',ty',DLAM(na',c')) 
	  when (oper = oper')
	    & eq_constr (lift 1 ty) ty'
	    & not (na' = Anonymous & oper = Prod)
	    -> factorize_binder (n+1) avoid2 env2 oper na' ty' c'
      | _ -> (n,bdrec avoid2 env2 c)
    in (p,slam(na2, body))

  in
    bdrec init_avoid env t
(* FIN TO EJECT *)
(******************************************************************)
       
let bdize at_top env t =
  let t' =
    if !print_casts then t
    else Reduction.strong (fun _ _ -> strip_outer_cast)
      Environ.empty_env Evd.empty t in
  try
    let avoid = if at_top then ids_of_env env else [] in
    ast_of_raw (Detyping.detype avoid env t')
  with Detyping.StillDLAM ->
    old_bdize at_top env t'
