
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

(* In this file, we translate constr to ast, in order to print constr *)

(**********************************************************************)
(* conversion of references                                           *)

let ids_of_ctxt cl =
  List.map
    (function 
       | VAR id -> id
       | Rel n ->
	   warning "ids_of_ctxt: rel";
	   id_of_string ("REL "^(string_of_int n))
       | _-> anomaly "ids_of_ctxt")
    (Array.to_list cl)

let ast_of_ident id = nvar (string_of_id id)

let ast_of_constructor (((sp,tyi),n),ids) =
  ope("MUTCONSTRUCT",
      (path_section dummy_loc sp)::(num tyi)::(num n)
      ::(List.map ast_of_ident ids))

let ast_of_mutind ((sp,tyi),ids) =
  ope("MUTIND",
      (path_section dummy_loc sp)::(num tyi)::(List.map ast_of_ident ids))
    
let ast_of_ref = function
  | RConst (sp,idl) ->
      ope("CONST", (path_section dummy_loc sp)::(List.map ast_of_ident idl))
  | RAbst (sp) ->
      ope("ABST", (path_section dummy_loc sp)
	    ::(List.map ast_of_ident (* on triche *) []))
  | RInd (ind,idl) -> ast_of_mutind(ind,idl)
  | RConstruct (cstr,idl) -> ast_of_constructor (cstr,idl)
  | RVar id -> nvar (string_of_id id)
  | REVar (ev,idl) ->
      ope("EVAR", (num ev)::(List.map ast_of_ident idl))
  | RMeta n -> ope("META",[num n])

(**********************************************************************)
(* conversion of patterns                                             *)

let rec ast_of_pattern = function   (* loc is thrown away for printing *)
  | PatVar (loc,Name id) -> nvar (string_of_id id)
  | PatVar (loc,Anonymous) -> nvar "_"
  | PatCstr(loc,cstr,args) ->
      ope("PATTCONSTRUCT",
	  (ast_of_constructor cstr)::List.map ast_of_pattern args)
  | PatAs(loc,id,p) -> ope("PATTAS",[nvar (string_of_id id); ast_of_pattern p])
	
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

(*
  let concrete_name (lo,l as ll) n c =
    if n = Anonymous then
      if dependent (Rel 1) c then anomaly "Anonymous should be non dependent"
      else (None,ll)
    else
      let l' = match lo with None -> l | Some l0 -> l0@l in
      let fresh_id = next_name_away n l' in
      let idopt = if dependent (Rel 1) c then (Some fresh_id) else None in
      (idopt, (lo,fresh_id::l))
*)

let occur_id env id0 c =
  let rec occur n = function
    | VAR id             -> id=id0
    | DOPN (Const sp,cl) -> (basename sp = id0) or (array_exists (occur n) cl)
    | DOPN (Abst sp,cl)  -> (basename sp = id0) or (array_exists (occur n) cl)
    | DOPN (MutInd _, cl) as t -> 
  	(basename (mind_path t) = id0) or (array_exists (occur n) cl)
    | DOPN (MutConstruct _, cl) as t -> 
    	(basename (mind_path t) = id0) or (array_exists (occur n) cl)
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

let concrete_name l env n c =
  if n = Anonymous then begin
    if dependent (Rel 1) c then anomaly "Anonymous should be non dependent";
    (None,l)
  end else
    let fresh_id = next_name_not_occuring n l env c in
    let idopt = if dependent (Rel 1) c then (Some fresh_id) else None in
    (idopt, fresh_id::l)

    (* Returns the list of global variables and constants in a term *)
let global_vars_and_consts t =
  let rec collect acc = function
    | VAR id             -> id::acc
    | DOPN (Const sp,cl) -> (basename sp)::(Array.fold_left collect acc cl)
    | DOPN (Abst sp,cl)  -> (basename sp)::(Array.fold_left collect acc cl)
    | DOPN (MutInd _, cl) as t       -> 
	(basename (mind_path t))::(Array.fold_left collect acc cl)
    | DOPN (MutConstruct _, cl) as t -> 
	(basename (mind_path t))::(Array.fold_left collect acc cl)
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


(* Parameterization of the translation from constr to ast      *)

(* Tables for Cases printing under a "if" form, a "let" form,  *)

let isomorphic_to_bool lc =
  let lcparams = Array.map get_params lc in
  Array.length lcparams = 2 & lcparams.(0) = [] & lcparams.(1) = []

let isomorphic_to_tuple lc = (Array.length lc = 1)

module PrintingCasesMake =
  functor (Test : sig 
     val test : constr array -> bool
     val error_message : string
     val member_message : identifier -> bool -> string
     val field : string
     val title : string
  end) ->
  struct
    type t = section_path * int
    let encode = indsp_of_id
    let check indsp =
      if not (Test.test (lc_of_lmis (mind_specif_of_mind_light indsp))) then 
	errorlabstrm "check_encode" [< 'sTR Test.error_message >]
    let decode = sp_of_spi
    let key = Goptions.SecondaryTable ("Printing",Test.field)
    let title = Test.title
    let member_message = Test.member_message
    let synchronous = true
  end

module PrintingCasesIf =
  PrintingCasesMake (struct 
    let test = isomorphic_to_bool
    let error_message = "This type cannot be seen as a boolean type"
    let field = "If"
    let title = "Types leading to pretty-printing of Cases using a `if' form: "
    let member_message id = function
      | true  -> 
          "Cases on elements of " ^ (string_of_id id)
          ^ " are printed using a `if' form"
      | false -> 
          "Cases on elements of " ^ (string_of_id id)
          ^ " are not printed using `if' form"
  end)

module PrintingCasesLet =
  PrintingCasesMake (struct 
    let test = isomorphic_to_tuple
    let error_message = "This type cannot be seen as a tuple type"
    let field = "Let"
    let title = 
      "Types leading to a pretty-printing of Cases using a `let' form:"
    let member_message id = function
      | true  -> 
          "Cases on elements of " ^ (string_of_id id)
          ^ " are printed using a `let' form"
      | false -> 
          "Cases on elements of " ^ (string_of_id id)
          ^ " are not printed using a `let' form"
  end)

module PrintingIf  = Goptions.MakeTable(PrintingCasesIf)
module PrintingLet = Goptions.MakeTable(PrintingCasesLet)

(* Options for printing or not wildcard and synthetisable types *)

open Goptions

let wildcard_value = ref true
let force_wildcard () = !wildcard_value

let _ =                           
  declare_async_bool_option 
    { optasyncname  = "the forced wildcard option";
      optasynckey   = SecondaryTable ("Printing","Wildcard");
      optasyncread  = force_wildcard;
      optasyncwrite = (fun v -> wildcard_value := v) }

let synth_type_value = ref true
let synthetize_type () = !synth_type_value

let _ = 
  declare_async_bool_option 
    { optasyncname = "the synthesisablity";
      optasynckey   = SecondaryTable ("Printing","Synth");
      optasyncread = synthetize_type;
      optasyncwrite = (fun v -> synth_type_value := v) }

(* Printing of implicit *)

let print_implicits = ref false


(**************************************************)
(* The main translation function is bdize_depcast *)

(* pour les implicites *)

(* l est ordonne'ee (croissant), ne garder que les elements <= n *)
let filter_until n l =
  let rec aux = function
    | [] -> []
    | i::l -> if i > n then [] else i::(aux l)
  in 
  aux l

(* l est ordonne'e (de'croissant), n>=max(l), diviser l en deux listes,
   la 2eme est la plus longue se'quence commencant par n,
   la 1ere contient les autres elements *)

let rec div_implicits n = 
  function 
    | [] -> [],[]
    | i::l -> 
	if i = n then 
	  let l1,l2=(div_implicits (n-1) l) in l1,i::l2
        else 
	  i::l,[]

let bdize_app c al =
  let impl =
    match c with
      | DOPN(MutConstruct constr_sp,_) -> constructor_implicits_list constr_sp
      | DOPN(MutInd ind_sp,_) -> inductive_implicits_list ind_sp
      | DOPN(Const sp,_) -> constant_implicits_list sp
      | VAR id -> (try (implicits_of_var CCI id) with _ -> []) (* et FW? *)
      | _ -> []
  in
  if impl = [] then 
    ope("APPLIST", al)
  else if !print_implicits then 
    ope("APPLIST", ope("XTRA",[str "!";List.hd al])::List.tl al)
  else 
    let largs = List.length al - 1 in
    let impl = List.rev (filter_until largs impl) in
    let impl1,impl2=div_implicits largs impl in
    let al1 = Array.of_list al in
    List.iter
      (fun i -> al1.(i) <-
         ope("XTRA", [str "!"; str "EX"; num i; al1.(i)]))
      impl2;
    List.iter
      (fun i -> al1.(i) <-
         ope("XTRA",[str "!"; num i; al1.(i)]))
      impl1;
    al1.(0) <- ope("XTRA",[str "!"; al1.(0)]);
    ope("APPLIST",Array.to_list al1)

type optioncast = WithCast | WithoutCast

(* [reference_tree p] pre-computes the variables and de bruijn occurring
   in a term to avoid a O(n2) factor when computing dependent each time *)

type ref_tree =
  NODE of (int list * identifier list) * ref_tree list

let combine l =
  let rec combine_rec = function
    | [] -> [],[]
    | NODE ((a,b),_)::l -> 
        let a',b' = combine_rec l in (list_union a a',list_union b b')
  in 
  NODE (combine_rec l,l)

let rec reference_tree p = function
  | VAR id -> NODE (([],[id]),[])
  | Rel n  -> NODE (([n-p],[]),[])
  | DOP0 op -> NODE (([],[]),[])
  | DOP1(op,c) -> reference_tree p c
  | DOP2(op,c1,c2) -> combine [reference_tree p c1;reference_tree p c2]
  | DOPN(op,cl) -> combine (List.map (reference_tree p) (Array.to_list cl))
  | DOPL(op,cl) -> combine (List.map (reference_tree p) cl)
  | DLAM(na,c) -> reference_tree (p+1) c 
  | DLAMV(na,cl) -> combine (List.map (reference_tree (p+1))(Array.to_list cl))

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

(* Main translation function from constr -> ast *)

let old_bdize_depcast opcast at_top env t =
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
	       if opcast=WithoutCast then 
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
	       let (_,a) = factorize_binder 1 avoid env Lambda na ty c in
               (* LAMBDA et LAMBDALIST se comportent pareil *)
	       ope("LAMBDALIST",[bdrec [] env ty;a])
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
	   | IsMutInd (sp,tyi,cl) ->
	       ope("MUTIND",((path_section dummy_loc sp)::(num tyi)::
			     (array_map_to_list (bdrec avoid env) cl)))
	   | IsMutConstruct (sp,tyi,n,cl) ->
	       ope("MUTCONSTRUCT",
		   ((path_section dummy_loc sp)::(num tyi)::(num n)::
		    (array_map_to_list (bdrec avoid env) cl)))
	   | IsMutCase (annot,p,c,bl) ->
	       let synth_type = synthetize_type () in
	       let tomatch = bdrec avoid env c in
	       begin match annot with
		 | None -> 
	             (* Pas d'annotation --> affichage avec vieux Case *)
		     let pred = bdrec avoid env p in
		     let bl' = array_map_to_list (bdrec avoid env) bl in
		     ope("MUTCASE",pred::tomatch::bl')
		 | Some indsp ->
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
		     if PrintingIf.active indsp then 
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
			 if PrintingLet.active indsp then 
			   "FORCELET" 
			 else 
			   "MULTCASE"
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
    let print_underscore = force_wildcard () in
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

let lookup_name_as_renamed env t s =
  let rec lookup avoid env n = function
      DOP2(Prod,_,DLAM(name,c')) ->
       (match concrete_name avoid env name c' with
          (Some id,avoid') -> 
	    if id=s then (Some n) 
	    else lookup avoid' (add_rel (Name id,()) env) (n+1) c'
	  | (None,avoid')    -> lookup avoid' env (n+1) (pop c'))
     | DOP2(Cast,c,_) -> lookup avoid env n c
     | _ -> None
  in lookup (ids_of_env env) env 1 t

let lookup_index_as_renamed t n =
  let rec lookup n d = function
      DOP2(Prod,_,DLAM(name,c')) -> 
	  (match concrete_name [] (gLOB nil_sign) name c' with
          (Some _,_) -> lookup n (d+1) c'
        | (None  ,_) -> if n=1 then Some d else lookup (n-1) (d+1) c')
    | DOP2(Cast,c,_) -> lookup n d c
    | _ -> None
  in lookup n 1 t

(*
Until V6.2.4, similar names were allowed in hypothesis and quantified
variables of a goal.
*)

(* $Id$ *)

exception StillDLAM

let rec detype t = 
  match collapse_appl t with
    (* Not well-formed constructions *)
    | DLAM _ | DLAMV _ -> raise StillDLAM
    (* Well-formed constructions *)
    | regular_constr -> 
  	(match kind_of_term regular_constr with
	   | IsRel n -> RRel (dummy_loc,n)
	   | IsMeta n -> RRef (dummy_loc,RMeta n)
	   | IsVar id -> RRef (dummy_loc,RVar id)
	   | IsXtra s -> anomaly "bdize: Xtra should no longer occur in constr"
	     (*       ope("XTRA",((str s):: pl@(List.map detype cl)))*)
	   | IsSort (Prop c) -> RSort (dummy_loc,RProp c)
	   | IsSort (Type _) -> RSort (dummy_loc,RType)
	   | IsCast (c1,c2) -> RCast(dummy_loc,detype c1,detype c2)
	   | IsProd (na,ty,c) -> 
	       RBinder (dummy_loc,BProd,na,detype ty,detype c)
	   | IsLambda (na,ty,c) -> 
	       RBinder (dummy_loc,BLambda,na,detype ty,detype c)
	   | IsAppL (f,args) -> RApp (dummy_loc,detype f,List.map detype args)
	   | IsConst (sp,cl) -> RRef (dummy_loc,RConst (sp,ids_of_ctxt cl))
	   | IsEvar (ev,cl) -> RRef (dummy_loc,REVar (ev,ids_of_ctxt cl))
	   | IsAbst (sp,cl) -> 
	       anomaly "bdize: Abst should no longer occur in constr"
	   | IsMutInd (sp,tyi,cl) ->
	       RRef (dummy_loc,RInd ((sp,tyi),ids_of_ctxt cl))
	   | IsMutConstruct (sp,tyi,n,cl) -> 
	       RRef (dummy_loc,RConstruct (((sp,tyi),n),ids_of_ctxt cl))
	   | IsMutCase (annot,p,c,bl) ->
	       let synth_type = synthetize_type () in
	       let tomatch = detype c in
	       begin match annot with
		 | None -> (* Pas d'annotation --> affichage avec vieux Case *)
		     warning "Printing in old Case syntax";
		     ROldCase (dummy_loc,false,Some (detype p),
			       tomatch,Array.map detype bl)
		 | Some indsp ->
		     let (mib,mip as lmis) = mind_specif_of_mind_light indsp in
		     let lc = lc_of_lmis lmis in
		     let lcparams = Array.map get_params lc in
		     let k = (nb_prod mip.mind_arity.body) - 
			     mib.mind_nparams in
		     let pred = 
		       if synth_type & computable p k & lcparams <> [||] then
			 None
		       else 
			 Some (detype p) 
		     in
		     let constructs = 
		       Array.init
			 (Array.length mip.mind_consnames)
			 (fun i -> ((indsp,i),[] (* on triche *))) in
		     let eqnv = array_map3 bdize_eqn constructs lcparams bl in
		     let eqnl = Array.to_list eqnv in
		     let tag =
		       if PrintingLet.active indsp then 
			 PrintLet 
		       else if PrintingIf.active indsp then 
			 PrintIf 
		       else 
			 PrintCases
		     in 
		     RCases (dummy_loc,tag,pred,[tomatch],eqnl)
	       end
	       
	   | IsFix (nv,n,cl,lfn,vt) ->
	       let l = 
		 Array.of_list 
		   (List.map
		      (function Name id -> id | Anonymous -> anomaly"detype")
		      lfn) 
	       in
	       RRec(dummy_loc,RFix (nv,n),l,Array.map detype cl,
		    Array.map detype vt)
	   | IsCoFix (n,cl,lfn,vt) ->
	       let l = 
		 Array.of_list 
		   (List.map
		      (function Name id -> id | Anonymous -> anomaly"detype")
		      lfn) 
	       in
	       RRec(dummy_loc,RCofix n,l,Array.map detype cl,
		    Array.map detype vt))
	
and bdize_eqn constr_id construct_params branch =
  let avoid = global_vars_and_consts branch in
  let make_pat x avoid b =
    if not (force_wildcard ()) or (dependent (Rel 1) b) then
      let id = next_name_away x avoid in
      (PatVar (dummy_loc,Name id)),id::avoid,id
    else 
      PatVar (dummy_loc,Anonymous),avoid,id_of_string "_" 
  in
  let rec buildrec idl patlist avoid = function
    | _::l, DOP2(Lambda,_,DLAM(x,b)) -> 
	let pat,new_avoid,id = make_pat x avoid b in
        buildrec (id::idl) (pat::patlist) new_avoid (l,b)
	  
    | l   , DOP2(Cast,b,_) ->    (* Oui, il y a parfois des cast *)
	buildrec idl patlist avoid (l,b)
	  
    | x::l, b -> (* eta-expansion : n'arrivera plus lorsque tous les
                   termes seront construits à partir de la syntaxe Cases *)
	(* nommage de la nouvelle variable *)
	let new_b = DOPN(AppL,[|lift 1 b; Rel 1|]) in
        let pat,new_avoid,id = make_pat x avoid new_b in
	buildrec (id::idl) (pat::patlist) new_avoid (l,new_b)
	  
    | []  , rhs	-> 
	(idl, [PatCstr(dummy_loc, constr_id, List.rev patlist)], detype rhs)
  in 
  buildrec [] [] avoid (construct_params,branch)


let implicit_of_ref = function
  | RConstruct (cstrid,_) -> constructor_implicits_list cstrid
  | RInd (indid,_) -> inductive_implicits_list indid
  | RConst (sp,_) -> constant_implicits_list sp
  | RVar id -> (try (implicits_of_var CCI id) with _ -> []) (* et FW? *)
  | _ -> []

let ast_of_app impl f args =
  if impl = [] then 
    ope("APPLIST", f::args)
  else if !print_implicits then 
    ope("APPLISTEXPL", (f::args))
  else 
    let largs = List.length args in
    let impl = List.rev (filter_until largs impl) in
    let impl1,impl2=div_implicits largs impl in
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

let rec ast_of_raw avoid env = function
  | RRef (_,ref) -> ast_of_ref ref
  | RRel (_,n) ->
      (try match fst (lookup_rel n env) with
	 | Name id   -> ast_of_ident id
	 | Anonymous -> 
	     anomaly "ast_of_raw: index to an anonymous variable"
       with Not_found ->
	 ope("REL",[num (n - List.length (get_rels env))]))
  | RApp (_,f,args) ->
      let astf = ast_of_raw avoid env  f in
      let astargs = List.map (ast_of_raw avoid env ) args in
      (match f with 
	 | RRef (_,ref) -> ast_of_app (implicit_of_ref ref) astf astargs
	 | _           -> ast_of_app [] astf astargs)
  | RBinder (_,BProd,Anonymous,t,c) ->
      (* Anonymous product are never factorized *)
      ope("PROD",[ast_of_raw avoid env t;
		  slam(None,ast_of_raw avoid (add_rel (Anonymous,()) env) c)])
  | RBinder (_,bk,na,t,c) ->
      let (n,a) = factorize_binder 1 avoid env bk na t c in
      let tag = match bk with
	  (* LAMBDA et LAMBDALIST se comportent pareil *)
	| BLambda -> "LAMBDALIST"
	  (* PROD et PRODLIST doivent être distingués à cause du cas *)
	  (* non dépendant, pour isoler l'implication; peut-être un *)
	  (* constructeur ARROW serait-il plus justifié ? *) 
	| BProd -> if n=1 then "PROD" else "PRODLIST" 
      in
      ope(tag,[ast_of_raw [] env t;a])

  | RCases (_,printinfo,typopt,tml,eqns) ->
      let pred = ast_of_rawopt avoid env typopt in
      let tag = match printinfo with
	| PrintIf -> "FORCEIF"
	| PrintLet -> "FORCELET"
	| PrintCases -> "MULTCASE" 
      in
      let asttomatch = ope("TOMATCH", List.map (ast_of_raw avoid env) tml) in
      let asteqns = List.map (ast_of_eqn avoid env) eqns in 
      ope(tag,pred::asttomatch::asteqns)
	
  | ROldCase (_,isrec,typopt,tm,bv) ->
      warning "Old Case syntax";
      ope("MUTCASE",(ast_of_rawopt avoid env typopt)
	    ::(ast_of_raw avoid env tm)
	    ::(Array.to_list (Array.map (ast_of_raw avoid env) bv)))
  | RRec (_,fk,idv,tyv,bv) ->
      let lfi = Array.map (fun id -> next_ident_away id avoid) idv in
      let alfi = Array.map ast_of_ident lfi in
      let def_avoid = (Array.to_list lfi)@avoid in
      let def_env =
	List.fold_left (fun env id -> add_rel (Name id,()) env) env 
	  (Array.to_list lfi) in
      (match fk with 
	 | RFix (nv,n) ->
             let rec split_lambda binds avoid env = function
	       | (0, t) -> (binds,ast_of_raw avoid env t)
	       | (n, RBinder(_,BLambda,na,t,b)) ->
		   let ast = ast_of_raw avoid env t in
		   let id = next_name_away na avoid in
		   let bind = ope("BINDER",[ast;ast_of_ident id]) in
		   split_lambda (bind::binds) (id::avoid)
		     (add_rel (na,()) env) (n-1,b)
	       | _ -> anomaly "ast_of_rawconst: ill-formed fixpoint body" 
	     in
	     let rec split_product avoid env = function
	       | (0, t) -> ast_of_raw avoid env t
	       | (n, RBinder(_,BProd,na,t,b)) ->
		   let id = next_name_away na avoid in
		   split_product (id::avoid) (add_rel (na,()) env) (n-1,b)
	       | _ -> anomaly "ast_of_rawconst: ill-formed fixpoint type" 
	     in
	     let listdecl = 
	       Array.mapi
		 (fun i fi ->
		    let (lparams,astdef) =
		      split_lambda [] avoid def_env (nv.(i)+1,bv.(i)) in
		    let asttyp = split_product avoid env (nv.(i)+1,tyv.(i)) in
		    ope("FDECL",
		       	[fi; ope ("BINDERS",List.rev lparams); 
			 asttyp; astdef]))
		 alfi
	     in 
	     ope("FIX", alfi.(n)::(Array.to_list listdecl))
	 | RCofix n -> 
	     let listdecl =
               Array.mapi 
		 (fun i fi -> ope("CFDECL",
				  [fi;
				   ast_of_raw avoid env tyv.(i);
				   ast_of_raw def_avoid def_env bv.(i)]))
		 alfi
	     in 
	     ope("COFIX", alfi.(n)::(Array.to_list listdecl)))

  | RSort (_,s) ->
      (match s with
	 | RProp Null -> ope("PROP",[])
	 | RProp Pos -> ope("SET",[])
	 | RType -> ope("TYPE",[]))
  | RHole _ -> ope("ISEVAR",[])
  | RCast (_,c,t) ->
      ope("CAST",[ast_of_raw avoid env c;ast_of_raw avoid env t])
	
and ast_of_eqn avoid env (idl,pl,c) =
  let new_env = 
    List.fold_left (fun env id -> add_rel (Name id,()) env) env idl in
  let rhs = ast_of_raw avoid new_env c in
  ope("EQN", rhs::(List.map ast_of_pattern pl))

and ast_of_rawopt avoid env  = function
  | None -> (str "SYNTH")
  | Some p -> ast_of_raw avoid env  p
	
and factorize_binder n avoid env  oper na ty c =
  let (env2, avoid2,na2) =
    match weak_concrete_name avoid env na c with
      | (Some id,l') -> add_rel (Name id,()) env, l', Some (string_of_id id) 
      | (None,l')    -> add_rel (Anonymous,()) env, l', None
  in
  let (p,body) = match c with
      RBinder(_,oper',na',ty',c')
	when (oper = oper')
	  & (ast_of_raw avoid env ty) 
	  = (ast_of_raw avoid (add_rel (na,()) env) ty')
	    & not (na' = Anonymous & oper = BProd)
	    -> factorize_binder (n+1) avoid2 env2 oper na' ty' c'
    | _ -> (n,ast_of_raw avoid2 env2 c)
  in 
  (p,slam(na2, body))
       
(* A brancher sur le vrai concrete_name *)
and weak_concrete_name avoid env na c =
  match na with
    | Anonymous -> (None,avoid)
    | Name id -> (Some id,avoid)

let bdize at_top env t =
  try
    let avoid = if at_top then ids_of_env env else [] in
    ast_of_raw avoid env (detype t)
  with StillDLAM -> 
    old_bdize_depcast WithoutCast at_top env t

(* En attendant que strong aille dans term.ml *)
let rec strong whdfun t = 
  match whdfun t with 
    | DOP0 _ as t -> t
	(* Cas ad hoc *)
    | DOP1(oper,c) -> DOP1(oper,strong whdfun c)
    | DOP2(oper,c1,c2) -> DOP2(oper,strong whdfun c1,strong whdfun c2)
    | DOPN(oper,cl) -> DOPN(oper,Array.map (strong whdfun) cl)
    | DOPL(oper,cl) -> DOPL(oper,List.map (strong whdfun) cl)
    | DLAM(na,c) -> DLAM(na,strong whdfun c)
    | DLAMV(na,c) -> DLAMV(na,Array.map (strong whdfun) c)
    | VAR _ as t -> t
    | Rel _ as t -> t

let bdize_no_casts at_top env t = bdize at_top env (strong strip_outer_cast t) 
			   
let ast_of_rawconstr = ast_of_raw []
