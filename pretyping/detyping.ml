
(* $Id$ *)

open Pp
open Util
open Univ
open Names
open Term
open Inductive
open Environ
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

exception Occur

let occur_rel p env id = 
  try lookup_name_of_rel p env = Name id
  with Not_found -> false (* Unbound indice : may happen in debug *)

let occur_id env id0 c =
  let rec occur n c = match kind_of_term c with
    | IsVar id when  id=id0 -> raise Occur
    | IsConst (sp, _) when basename sp = id0 -> raise Occur
    | IsMutInd (ind_sp, _)
	when basename (path_of_inductive_path ind_sp) = id0 -> raise Occur
    | IsMutConstruct (cstr_sp, _) 
	when basename (path_of_constructor_path cstr_sp) = id0 -> raise Occur
    | IsRel p when p>n & occur_rel (p-n) env id0 -> raise Occur
    | _ -> iter_constr_with_binders succ occur n c
  in 
  try occur 1 c; false
  with Occur -> true

let next_name_not_occuring name l env_names t =
  let rec next id =
    if List.mem id l or occur_id env_names id t then next (lift_ident id)
    else id
  in 
  match name with
    | Name id   -> next id
    | Anonymous -> id_of_string "_"

(* Remark: Anonymous var may be dependent in Evar's contexts *)
let concrete_name l env_names n c =
  if n = Anonymous & not (dependent (mkRel 1) c) then
    (None,l)
  else
    let fresh_id = next_name_not_occuring n l env_names c in
    let idopt = if dependent (mkRel 1) c then (Some fresh_id) else None in
    (idopt, fresh_id::l)

let concrete_let_name l env_names n c =
  let fresh_id = next_name_not_occuring n l env_names c in
  (Name fresh_id, fresh_id::l)

    (* Returns the list of global variables and constants in a term *)
let global_vars_and_consts t =
  let rec collect acc c =
    let op, cl = splay_constr c in
    let acc' = Array.fold_left collect acc cl in
    match op with
    | OpVar id -> id::acc'
    | OpConst sp -> (basename sp)::acc'
    | OpMutInd ind_sp -> (basename (path_of_inductive_path ind_sp))::acc'
    | OpMutConstruct csp -> (basename (path_of_constructor_path csp))::acc'
    | _ -> acc'
  in
  list_uniquize (collect [] t)
    
let used_of = global_vars_and_consts

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
    let printer (spi,_) = [< 'sTR(string_of_path (sp_of_spi spi)) >]
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

module PrintingIf  = Goptions.MakeIdentTable(PrintingCasesIf)
module PrintingLet = Goptions.MakeIdentTable(PrintingCasesLet)

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

  let _,ccl = decompose_lam p in 
  noccur_between 1 (k+1) ccl



let lookup_name_as_renamed ctxt t s =
  let rec lookup avoid env_names n c = match kind_of_term c with
    | IsProd (name,_,c') ->
	(match concrete_name avoid env_names name c' with
           | (Some id,avoid') -> 
	       if id=s then (Some n) 
	       else lookup avoid' (add_name (Name id) env_names) (n+1) c'
	   | (None,avoid')    -> lookup avoid' env_names (n+1) (pop c'))
    | IsLetIn (name,_,_,c') ->
	(match concrete_name avoid env_names name c' with
           | (Some id,avoid') -> 
	       if id=s then (Some n) 
	       else lookup avoid' (add_name (Name id) env_names) (n+1) c'
	   | (None,avoid')    -> lookup avoid' env_names (n+1) (pop c'))
    | IsCast (c,_) -> lookup avoid env_names n c
    | _ -> None
  in lookup (ids_of_named_context ctxt) empty_names_context 1 t

let lookup_index_as_renamed t n =
  let rec lookup n d c = match kind_of_term c with
    | IsProd (name,_,c') ->
	  (match concrete_name [] empty_names_context name c' with
               (Some _,_) -> lookup n (d+1) c'
             | (None  ,_) -> if n=1 then Some d else lookup (n-1) (d+1) c')
    | IsLetIn (name,_,_,c') ->
	  (match concrete_name [] empty_names_context name c' with
             | (Some _,_) -> lookup n (d+1) c'
             | (None  ,_) -> if n=1 then Some d else lookup (n-1) (d+1) c')
    | IsCast (c,_) -> lookup n d c
    | _ -> None
  in lookup n 1 t

let rec detype avoid env t =
  match kind_of_term (collapse_appl t) with
    | IsRel n ->
      (try match lookup_name_of_rel n env with
	 | Name id   -> RVar (dummy_loc, id)
	 | Anonymous -> anomaly "detype: index to an anonymous variable"
       with Not_found ->
	 let s = "[REL "^(string_of_int n)^"]"
	 in RVar (dummy_loc, id_of_string s))
    | IsMeta n -> RMeta (dummy_loc, n)
    | IsVar id -> RVar (dummy_loc, id)
    | IsXtra s -> warning "bdize: Xtra should no longer occur in constr";
	RVar(dummy_loc, id_of_string ("XTRA"^s))
        (* ope("XTRA",((str s):: pl@(List.map detype cl)))*) 
    | IsSort (Prop c) -> RSort (dummy_loc,RProp c)
    | IsSort (Type _) -> RSort (dummy_loc,RType)
    | IsCast (c1,c2) ->
	RCast(dummy_loc,detype avoid env c1,detype avoid env c2)
    | IsProd (na,ty,c) -> detype_binder BProd avoid env na ty c
    | IsLambda (na,ty,c) -> detype_binder BLambda avoid env na ty c
    | IsLetIn (na,b,_,c) -> detype_binder BLetIn avoid env na b c
    | IsApp (f,args) ->
	RApp (dummy_loc,detype avoid env f,array_map_to_list (detype avoid env) args)
    | IsConst (sp,cl) ->
	detype_reference avoid env (ConstRef sp) cl
    | IsEvar (ev,cl) ->
	let f = REvar (dummy_loc, ev) in
	RApp (dummy_loc, f, List.map (detype avoid env) (Array.to_list cl))
    | IsMutInd (ind_sp,cl) ->
	detype_reference avoid env (IndRef ind_sp) cl
    | IsMutConstruct (cstr_sp,cl) ->
	detype_reference avoid env (ConstructRef cstr_sp) cl
    | IsMutCase (annot,p,c,bl) ->
	let synth_type = synthetize_type () in
	let tomatch = detype avoid env c in
	let (consnargsl,(indsp,considl,k,style,tags)) = annot in
	let pred = 
	  if synth_type & computable p k & considl <> [||] then
	    None
	  else 
	    Some (detype avoid env p) in
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
	
    | IsFix (nvn,(cl,lfn,vt)) -> detype_fix (RFix nvn) avoid env cl lfn vt
    | IsCoFix (n,(cl,lfn,vt))  -> detype_fix (RCoFix n) avoid env cl lfn vt

and detype_reference avoid env ref args =
  let args = 
    try Array.to_list (extract_instance ref args)
    with Not_found -> (* May happen in debugger *)
      if Array.length args = 0 then []
      else
	let m = "<<Cannot split "^(string_of_int (Array.length args))^
		" arguments>>" in
	(mkVar (id_of_string m))::(Array.to_list args)
  in
  let f = RRef (dummy_loc, ref) in
  if args = [] then f
  else RApp (dummy_loc, f, List.map (detype avoid env) args)

and detype_fix fk avoid env cl lfn vt =
  let lfi = List.map (fun id -> next_name_away id avoid) lfn in
  let def_avoid = lfi@avoid in
  let def_env =
    List.fold_left (fun env id -> add_name (Name id) env) env lfi in
  RRec(dummy_loc,fk,Array.of_list lfi,Array.map (detype avoid env) cl,
       Array.map (detype def_avoid def_env) vt)


and detype_eqn avoid env constr_id construct_nargs branch =
  let make_pat x avoid env b ids =
    if not (force_wildcard ()) or (dependent (mkRel 1) b) then
      let id = next_name_away_with_default "x" x avoid in
      PatVar (dummy_loc,Name id),id::avoid,(add_name (Name id) env),id::ids
    else 
      PatVar (dummy_loc,Anonymous),avoid,(add_name Anonymous env),ids
  in
  let rec buildrec ids patlist avoid env n b =
    if n=0 then
      (ids, [PatCstr(dummy_loc, constr_id, List.rev patlist,Anonymous)],
       detype avoid env b)
    else
      match kind_of_term b with
	| IsLambda (x,_,b) -> 
	    let pat,new_avoid,new_env,new_ids = make_pat x avoid env b ids in
            buildrec new_ids (pat::patlist) new_avoid new_env (n-1) b

	| IsCast (c,_) ->    (* Oui, il y a parfois des cast *)
	    buildrec ids patlist avoid env n c

	| _ -> (* eta-expansion : n'arrivera plus lorsque tous les
                  termes seront construits à partir de la syntaxe Cases *)
            (* nommage de la nouvelle variable *)
	    let new_b = applist (lift 1 b, [mkRel 1]) in
            let pat,new_avoid,new_env,new_ids =
	      make_pat Anonymous avoid env new_b ids in
	    buildrec new_ids (pat::patlist) new_avoid new_env (n-1) new_b
	  
  in 
  buildrec [] [] avoid env construct_nargs branch

and detype_binder bk avoid env na ty c =
  let na',avoid' =
    if bk = BLetIn then concrete_let_name avoid env na c
    else
      match concrete_name avoid env na c with
	| (Some id,l') -> (Name id), l'
	| (None,l')    -> Anonymous, l' in
  let r =  detype avoid' (add_name na' env) c in
  match bk with
    | BProd -> RProd (dummy_loc, na',detype [] env ty, r)
    | BLambda -> RLambda (dummy_loc, na',detype [] env ty, r)
    | BLetIn -> RLetIn (dummy_loc, na',detype [] env ty, r)
