
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
open Rawterm

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

let encode_inductive id =
  let (indsp,_ as ind) =
    try 
      match kind_of_term (global_reference CCI id) with
	| IsMutInd (indsp,args) -> (indsp,args)
	| _ -> errorlabstrm "indsp_of_id" 
	    [< 'sTR ((string_of_id id)^" is not an inductive type") >]
    with Not_found -> 
      error ("Cannot find reference "^(string_of_id id))
  in
  let mis = Global.lookup_mind_specif ind in
  let constr_lengths = Array.map List.length (mis_recarg mis) in
  (indsp,constr_lengths)

let sp_of_spi (refsp,tyi) =
  let mip = Declarations.mind_nth_type_packet (Global.lookup_mind refsp) tyi in
  let (pa,_,k) = repr_path refsp in 
  make_path pa mip.Declarations.mind_typename k

(*
  let (_,mip) = mind_specif_of_mind_light spi in
  let (pa,_,k) = repr_path sp in 
  make_path pa (mip.mind_typename) k
*)
(* Parameterization of the translation from constr to ast      *)

(* Tables for Cases printing under a "if" form, a "let" form,  *)

let isomorphic_to_bool lc =
  Array.length lc = 2 & lc.(0) = 0 & lc.(1) = 0

(*
let isomorphic_to_bool lc =
  let lcparams = Array.map get_params lc in
  Array.length lcparams = 2 & lcparams.(0) = [] & lcparams.(1) = []
*)

let isomorphic_to_tuple lc = (Array.length lc = 1)
(*
let isomorphic_to_tuple lc = (Array.length lc = 1)
*)
module PrintingCasesMake =
  functor (Test : sig 
     val test : int array -> bool
(*     val test : constr array -> bool*)
     val error_message : string
     val member_message : identifier -> bool -> string
     val field : string
     val title : string
  end) ->
  struct
    type t = inductive_path * int array
    let encode = encode_inductive
    let check (_,lc) =
      if not (Test.test lc) then 
	errorlabstrm "check_encode" [< 'sTR Test.error_message >]
    let decode (spi,_) = sp_of_spi spi
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

let force_let (lc,(indsp,_,_,_,_)) = PrintingLet.active (indsp,lc)
let force_if (lc,(indsp,_,_,_,_)) = PrintingIf.active (indsp,lc)

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

(*
let ids_of_var cl =
  List.map
    (function 
       | RRef (_,RVar id) -> id
       | _-> anomaly "ids_of_var")
    (Array.to_list cl)
*)

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

exception StillDLAM

let rec detype avoid env t =
  match collapse_appl t with
    (* Not well-formed constructions *)
    | DLAM _ | DLAMV _ -> raise StillDLAM
    (* Well-formed constructions *)
    | regular_constr -> 
    (match kind_of_term regular_constr with
    | IsRel n ->
      (try match fst (lookup_rel n env) with
	 | Name id   -> RRef (dummy_loc, RVar id)
	 | Anonymous -> anomaly "detype: index to an anonymous variable"
       with Not_found ->
	 let s = "[REL "^(string_of_int (number_of_rels env - n))^"]"
	 in RRef (dummy_loc, RVar (id_of_string s)))
    | IsMeta n -> RMeta (dummy_loc, n)
    | IsVar id -> RRef (dummy_loc,RVar id)
    | IsXtra s -> warning "bdize: Xtra should no longer occur in constr";
	RRef(dummy_loc,RVar (id_of_string ("XTRA"^s)))
        (* ope("XTRA",((str s):: pl@(List.map detype cl)))*) 
    | IsSort (Prop c) -> RSort (dummy_loc,RProp c)
    | IsSort (Type _) -> RSort (dummy_loc,RType)
    | IsCast (c1,c2) ->
	RCast(dummy_loc,detype avoid env c1,detype avoid env c2)
    | IsProd (na,ty,c) -> detype_binder BProd avoid env na ty c
    | IsLambda (na,ty,c) -> detype_binder BLambda avoid env na ty c
    | IsAppL (f,args) ->
	RApp (dummy_loc,detype avoid env f,List.map (detype avoid env) args)
    | IsConst (sp,cl) ->
	RRef(dummy_loc,RConst(sp,Array.map (detype avoid env) cl))
    | IsEvar (ev,cl) ->
	RRef(dummy_loc,REVar(ev,Array.map (detype avoid env) cl))
    | IsAbst (sp,cl) -> 
	anomaly "bdize: Abst should no longer occur in constr"
    | IsMutInd (ind_sp,cl) ->
	RRef (dummy_loc,RInd (ind_sp,Array.map (detype avoid env) cl))
    | IsMutConstruct (cstr_sp,cl) ->
	RRef (dummy_loc,RConstruct (cstr_sp,Array.map (detype avoid env) cl))
    | IsMutCase (annot,p,c,bl) ->
	let synth_type = synthetize_type () in
	let tomatch = detype avoid env c in
	begin 
	  match annot with
(*	  | None -> (* Pas d'annotation --> affichage avec vieux Case *)
	      warning "Printing in old Case syntax";
	      ROldCase (dummy_loc,false,Some (detype avoid env p),
			tomatch,Array.map (detype avoid env) bl)
	  | Some *) (consnargsl,(indsp,considl,k,style,tags)) ->
	    let pred = 
	      if synth_type & computable p k & considl <> [||] then
		None
	      else 
		Some (detype avoid env p) 
	    in
	    let constructs = 
	      Array.init (Array.length considl)
		(fun i -> ((indsp,i+1),[] (* on triche *))) in
	    let eqnv =
	      array_map3 (detype_eqn avoid env) constructs consnargsl bl in
	    let eqnl = Array.to_list eqnv in
	    let tag =
	      if PrintingLet.active (indsp,consnargsl) then 
		PrintLet 
	      else if PrintingIf.active (indsp,consnargsl) then 
		PrintIf 
	      else 
		PrintCases
	    in 
	    RCases (dummy_loc,tag,pred,[tomatch],eqnl)
	end
	
    | IsFix (nv,n,cl,lfn,vt) -> detype_fix (RFix (nv,n)) avoid env cl lfn vt
    | IsCoFix (n,cl,lfn,vt)  -> detype_fix (RCofix n) avoid env cl lfn vt)

and detype_fix fk avoid env cl lfn vt =
  let lfi = List.map (fun id -> next_name_away id avoid) lfn in
  let def_avoid = lfi@avoid in
  let def_env =
    List.fold_left (fun env id -> add_rel (Name id,()) env) env lfi in
  RRec(dummy_loc,fk,Array.of_list lfi,Array.map (detype avoid env) cl,
       Array.map (detype def_avoid def_env) vt)


and detype_eqn avoid env constr_id construct_nargs branch =
  let make_pat x avoid env b ids =
    if not (force_wildcard ()) or (dependent (Rel 1) b) then
      let id = next_name_away_with_default "x" x avoid in
      PatVar (dummy_loc,Name id),id::avoid,(add_rel (Name id,()) env),id::ids
    else 
      PatVar (dummy_loc,Anonymous),avoid,(add_rel (Anonymous,()) env),ids
  in
  let rec buildrec ids patlist avoid env = function
    | 0  , rhs	-> 
	(ids, [PatCstr(dummy_loc, constr_id, List.rev patlist,Anonymous)],
	 detype avoid env rhs)

    | n, DOP2(Lambda,_,DLAM(x,b)) -> 
	let pat,new_avoid,new_env,new_ids = make_pat x avoid env b ids in
        buildrec new_ids (pat::patlist) new_avoid new_env (n-1,b)

    | n, DOP2(Cast,b,_) ->    (* Oui, il y a parfois des cast *)
	buildrec ids patlist avoid env (n,b)
	  
    | n, b -> (* eta-expansion : n'arrivera plus lorsque tous les
                   termes seront construits à partir de la syntaxe Cases *)
	(* nommage de la nouvelle variable *)
	let new_b = DOPN(AppL,[|lift 1 b; Rel 1|]) in
        let pat,new_avoid,new_env,new_ids =
	  make_pat Anonymous avoid env new_b ids in
	buildrec new_ids (pat::patlist) new_avoid new_env (n-1,new_b)
	  
  in 
  buildrec [] [] avoid env (construct_nargs,branch)

and detype_binder bk avoid env na ty c =
  let na',avoid' = match concrete_name avoid env na c with
    | (Some id,l') -> (Name id), l'
    | (None,l')    -> Anonymous, l' in
  RBinder (dummy_loc,bk,
	   na',detype [] env ty,
	   detype avoid' (add_rel (na',()) env) c)
