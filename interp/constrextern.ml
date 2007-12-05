(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

(*i*)
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
open Impargs
open Topconstr
open Rawterm
open Pattern
open Nametab
open Notation
open Reserve
open Detyping
(*i*)

(* Translation from rawconstr to front constr *)

(**********************************************************************)
(* Parametrization                                                    *)

(* This governs printing of local context of references *)
let print_arguments = ref false

(* If true, prints local context of evars, whatever print_arguments *)
let print_evar_arguments = ref false

(* This governs printing of implicit arguments.  When
   [print_implicits] is on then [print_implicits_explicit_args] tells
   how implicit args are printed. If on, implicit args are printed
   with the form (id:=arg) otherwise arguments are printed normally and
   the function is prefixed by "@" *)
let print_implicits = ref false
let print_implicits_explicit_args = ref false

(* Tells if implicit arguments not known to be inferable from a rigid
   position are systematically printed *)
let print_implicits_defensive = ref true

(* This forces printing of coercions *)
let print_coercions = ref false

(* This forces printing universe names of Type{.} *)
let print_universes = ref false

(* This suppresses printing of primitive tokens (e.g. numeral) and symbols *)
let print_no_symbol = ref false

(* This governs printing of projections using the dot notation symbols *)
let print_projections = ref false

let print_meta_as_hole = ref false

let with_arguments f = Options.with_option print_arguments f
let with_implicits f = Options.with_option print_implicits f
let with_coercions f = Options.with_option print_coercions f
let with_universes f = Options.with_option print_universes f
let without_symbols f = Options.with_option print_no_symbol f
let with_meta_as_hole f = Options.with_option print_meta_as_hole f

(**********************************************************************)
(* Various externalisation functions *)

let insert_delimiters e = function
  | None -> e
  | Some sc -> CDelimiters (dummy_loc,sc,e)

let insert_pat_delimiters loc p = function
  | None -> p
  | Some sc -> CPatDelimiters (loc,sc,p)

let insert_pat_alias loc p = function
  | Anonymous -> p
  | Name id -> CPatAlias (loc,p,id)

(**********************************************************************)
(* conversion of references                                           *)

let ids_of_ctxt ctxt =
  Array.to_list
    (Array.map
       (function c -> match kind_of_term c with
	  | Var id -> id
	  | _ ->
       error "arbitrary substitution of references not implemented")
     ctxt)

let idopt_of_name = function 
  | Name id -> Some id
  | Anonymous -> None

let extern_evar loc n l =
  if !print_evar_arguments then CEvar (loc,n,l) else CEvar (loc,n,None)

let rawdebug = ref false

let raw_string_of_ref = function
  | ConstRef kn -> 
      "CONST("^(string_of_con kn)^")"
  | IndRef (kn,i) ->
      "IND("^(string_of_kn kn)^","^(string_of_int i)^")"
  | ConstructRef ((kn,i),j) -> 
      "CONSTRUCT("^
      (string_of_kn kn)^","^(string_of_int i)^","^(string_of_int j)^")"
  | VarRef id -> 
      "SECVAR("^(string_of_id id)^")"

let short_string_of_ref = function
  | VarRef id -> string_of_id id
  | ConstRef cst -> string_of_label (pi3 (repr_con cst))
  | IndRef (kn,0) -> string_of_label (pi3 (repr_kn kn))
  | IndRef (kn,i) -> 
      "IND("^string_of_label (pi3 (repr_kn kn))^(string_of_int i)^")"
  | ConstructRef ((kn,i),j) -> 
      "CONSTRUCT("^
      string_of_label (pi3 (repr_kn kn))^","^(string_of_int i)^","^(string_of_int j)^")"

let extern_reference loc vars r =
  try Qualid (loc,shortest_qualid_of_global vars r)
  with Not_found ->
    (* happens in debugger *)
    let f = if !rawdebug then raw_string_of_ref else short_string_of_ref in
    Ident (loc,id_of_string (f r))

(************************************************************************)
(* Equality up to location (useful for translator v8) *)

let rec check_same_pattern p1 p2 =
  match p1, p2 with
    | CPatAlias(_,a1,i1), CPatAlias(_,a2,i2) when i1=i2 ->
        check_same_pattern a1 a2
    | CPatCstr(_,c1,a1), CPatCstr(_,c2,a2) when c1=c2 ->
        List.iter2 check_same_pattern a1 a2
    | CPatAtom(_,r1), CPatAtom(_,r2) when r1=r2 -> ()
    | CPatPrim(_,i1), CPatPrim(_,i2) when i1=i2 -> ()
    | CPatDelimiters(_,s1,e1), CPatDelimiters(_,s2,e2) when s1=s2 ->
        check_same_pattern e1 e2
    | _ -> failwith "not same pattern"

let check_same_ref r1 r2 =
  match r1,r2 with
  | Qualid(_,q1), Qualid(_,q2) when q1=q2 -> ()
  | Ident(_,i1), Ident(_,i2) when i1=i2 -> ()
  | _ -> failwith "not same ref"

let rec check_same_type ty1 ty2 =
  match ty1, ty2 with
  | CRef r1, CRef r2 -> check_same_ref r1 r2
  | CFix(_,(_,id1),fl1), CFix(_,(_,id2),fl2) when id1=id2 ->
      List.iter2 (fun (id1,i1,bl1,a1,b1) (id2,i2,bl2,a2,b2) ->
        if id1<>id2 || i1<>i2 then failwith "not same fix";
        check_same_fix_binder bl1 bl2;
        check_same_type a1 a2;
        check_same_type b1 b2)
        fl1 fl2
  | CCoFix(_,(_,id1),fl1), CCoFix(_,(_,id2),fl2) when id1=id2 ->
      List.iter2 (fun (id1,bl1,a1,b1) (id2,bl2,a2,b2) ->
        if id1<>id2 then failwith "not same fix";
        check_same_fix_binder bl1 bl2;
        check_same_type a1 a2;
        check_same_type b1 b2)
        fl1 fl2
  | CArrow(_,a1,b1), CArrow(_,a2,b2) ->
      check_same_type a1 a2;
      check_same_type b1 b2
  | CProdN(_,bl1,a1), CProdN(_,bl2,a2) ->
      List.iter2 check_same_binder bl1 bl2;
      check_same_type a1 a2
  | CLambdaN(_,bl1,a1), CLambdaN(_,bl2,a2) ->
      List.iter2 check_same_binder bl1 bl2;
      check_same_type a1 a2
  | CLetIn(_,(_,na1),a1,b1), CLetIn(_,(_,na2),a2,b2) when na1=na2 ->
      check_same_type a1 a2;
      check_same_type b1 b2
  | CAppExpl(_,r1,al1), CAppExpl(_,r2,al2) when r1=r2 ->
      List.iter2 check_same_type al1 al2
  | CApp(_,(_,e1),al1), CApp(_,(_,e2),al2) ->
      check_same_type e1 e2;
      List.iter2 (fun (a1,e1) (a2,e2) ->
                    if e1<>e2 then failwith "not same expl";
                    check_same_type a1 a2) al1 al2
  | CCases(_,_,a1,brl1), CCases(_,_,a2,brl2) ->
      List.iter2 (fun (tm1,_) (tm2,_) -> check_same_type tm1 tm2) a1 a2;
      List.iter2 (fun (_,pl1,r1) (_,pl2,r2) ->
        List.iter2 (List.iter2 check_same_pattern) pl1 pl2;
        check_same_type r1 r2) brl1 brl2
  | CHole _, CHole _ -> ()
  | CPatVar(_,i1), CPatVar(_,i2) when i1=i2 -> ()
  | CSort(_,s1), CSort(_,s2) when s1=s2 -> ()
  | CCast(_,a1,CastConv (_,b1)), CCast(_,a2, CastConv(_,b2)) ->
      check_same_type a1 a2;
      check_same_type b1 b2
  | CCast(_,a1,CastCoerce), CCast(_,a2, CastCoerce) ->
      check_same_type a1 a2
  | CNotation(_,n1,e1), CNotation(_,n2,e2) when n1=n2 ->
      List.iter2 check_same_type e1 e2
  | CPrim(_,i1), CPrim(_,i2) when i1=i2 -> ()
  | CDelimiters(_,s1,e1), CDelimiters(_,s2,e2) when s1=s2 ->
      check_same_type e1 e2
  | _ when ty1=ty2 -> ()
  | _ -> failwith "not same type"

and check_same_binder (nal1,e1) (nal2,e2) =
  List.iter2 (fun (_,na1) (_,na2) ->
    if na1<>na2 then failwith "not same name") nal1 nal2;
  check_same_type e1 e2

and check_same_fix_binder bl1 bl2 =
  List.iter2 (fun b1 b2 ->
    match b1,b2 with
        LocalRawAssum(nal1,ty1), LocalRawAssum(nal2,ty2) ->
          check_same_binder (nal1,ty1) (nal2,ty2)
      | LocalRawDef(na1,def1), LocalRawDef(na2,def2) ->
          check_same_binder ([na1],def1) ([na2],def2)          
      | _ -> failwith "not same binder") bl1 bl2

let same c d = try check_same_type c d; true with _ -> false

(* Idem for rawconstr *)

let array_iter2 f v1 v2 =
  List.iter2 f (Array.to_list v1) (Array.to_list v2)

let rec same_patt p1 p2 =
  match p1, p2 with
      PatVar(_,na1), PatVar(_,na2) -> if na1<>na2 then failwith "PatVar"
    | PatCstr(_,c1,pl1,al1), PatCstr(_,c2,pl2,al2) ->
        if c1<>c2 || al1 <> al2 then failwith "PatCstr";
        List.iter2 same_patt pl1 pl2
    | _ -> failwith "same_patt"

let rec same_raw c d =
  match c,d with
   | RRef(_,gr1), RRef(_,gr2) -> if gr1<>gr2 then failwith "RRef"
   | RVar(_,id1), RVar(_,id2) -> if id1<>id2 then failwith "RVar"
   | REvar(_,e1,a1), REvar(_,e2,a2) ->
       if e1 <> e2 then failwith "REvar";
       Option.iter2(List.iter2 same_raw) a1 a2
  | RPatVar(_,pv1), RPatVar(_,pv2) -> if pv1<>pv2 then failwith "RPatVar"
  | RApp(_,f1,a1), RApp(_,f2,a2) ->
      List.iter2 same_raw (f1::a1) (f2::a2)
  | RLambda(_,na1,t1,m1), RLambda(_,na2,t2,m2) ->
      if na1 <> na2 then failwith "RLambda";
      same_raw t1 t2; same_raw m1 m2
  | RProd(_,na1,t1,m1), RProd(_,na2,t2,m2) ->
      if na1 <> na2 then failwith "RProd";
      same_raw t1 t2; same_raw m1 m2
  | RLetIn(_,na1,t1,m1), RLetIn(_,na2,t2,m2) ->
      if na1 <> na2 then failwith "RLetIn";
      same_raw t1 t2; same_raw m1 m2
  | RCases(_,_,c1,b1), RCases(_,_,c2,b2) ->
      List.iter2
        (fun (t1,(al1,oind1)) (t2,(al2,oind2)) ->
          same_raw t1 t2;
          if al1 <> al2 then failwith "RCases";
          Option.iter2(fun (_,i1,_,nl1) (_,i2,_,nl2) ->
            if i1<>i2 || nl1 <> nl2 then failwith "RCases") oind1 oind2) c1 c2;
      List.iter2 (fun (_,_,pl1,b1) (_,_,pl2,b2) ->
        List.iter2 same_patt pl1 pl2;
        same_raw b1 b2) b1 b2
  | RLetTuple(_,nl1,_,b1,c1), RLetTuple(_,nl2,_,b2,c2) ->
      if nl1<>nl2 then failwith "RLetTuple";
      same_raw b1 b2;
      same_raw c1 c2
  | RIf(_,b1,_,t1,e1),RIf(_,b2,_,t2,e2) ->
      same_raw b1 b2; same_raw t1 t2; same_raw e1 e2
  | RRec(_,fk1,na1,bl1,ty1,def1), RRec(_,fk2,na2,bl2,ty2,def2) ->
      if fk1 <> fk2 || na1 <> na2 then failwith "RRec";
      array_iter2
        (List.iter2 (fun (na1,bd1,ty1) (na2,bd2,ty2) ->
          if na1<>na2 then failwith "RRec";
          Option.iter2 same_raw bd1 bd2;
          same_raw ty1 ty2)) bl1 bl2;
      array_iter2 same_raw ty1 ty2;
      array_iter2 same_raw def1 def2
  | RSort(_,s1), RSort(_,s2) -> if s1<>s2 then failwith "RSort"
  | RHole _, _ -> ()
  | _, RHole _ -> ()
  | RCast(_,c1,_),r2 -> same_raw c1 r2
  | r1, RCast(_,c2,_) -> same_raw r1 c2
  | RDynamic(_,d1), RDynamic(_,d2) -> if d1<>d2 then failwith"RDynamic"
  | _ -> failwith "same_raw"
     
let same_rawconstr c d = 
  try same_raw c d; true
  with Failure _ | Invalid_argument _ -> false

(**********************************************************************)
(* mapping patterns to cases_pattern_expr                                *)

let has_curly_brackets ntn =
  String.length ntn >= 6 & (String.sub ntn 0 6 = "{ _ } " or
    String.sub ntn (String.length ntn - 6) 6 = " { _ }" or
    string_string_contains ntn " { _ } ")

let rec wildcards ntn n =
  if n = String.length ntn then []
  else let l = spaces ntn (n+1) in if ntn.[n] = '_' then n::l else l
and spaces ntn n =
  if n = String.length ntn then []
  else if ntn.[n] = ' ' then wildcards ntn (n+1) else spaces ntn (n+1)

let expand_curly_brackets loc mknot ntn l =
  let ntn' = ref ntn in
  let rec expand_ntn i =
    function
    | [] -> []
    | a::l ->
        let a' = 
          let p = List.nth (wildcards !ntn' 0) i - 2 in
          if p>=0 & p+5 <= String.length !ntn' & String.sub !ntn' p 5 = "{ _ }"
          then begin
            ntn' := 
              String.sub !ntn' 0 p ^ "_" ^ 
              String.sub !ntn' (p+5) (String.length !ntn' -p-5);
            mknot (loc,"{ _ }",[a]) end
          else a in
        a' :: expand_ntn (i+1) l in
  let l = expand_ntn 0 l in
  (* side effect *)
  mknot (loc,!ntn',l)

let destPrim = function CPrim(_,t) -> Some t | _ -> None
let destPatPrim = function CPatPrim(_,t) -> Some t | _ -> None

let make_notation_gen loc ntn mknot mkprim destprim l =
  if has_curly_brackets ntn
  then expand_curly_brackets loc mknot ntn l
  else match ntn,List.map destprim l with
    (* Special case to avoid writing "- 3" for e.g. (Zopp 3) *)
    | "- _", [Some (Numeral p)] when Bigint.is_strictly_pos p ->
        mknot (loc,ntn,[mknot (loc,"( _ )",l)])
    | _ -> 
	match decompose_notation_key ntn, l with
	| [Terminal "-"; Terminal x], [] ->
	    (try mkprim (loc, Numeral (Bigint.neg (Bigint.of_string x)))
 	     with _ -> mknot (loc,ntn,[]))
	| [Terminal x], [] ->
	    (try mkprim (loc, Numeral (Bigint.of_string x))
 	     with _ -> mknot (loc,ntn,[]))
	| _ ->
	    mknot (loc,ntn,l)

let make_notation loc ntn l =
  make_notation_gen loc ntn
    (fun (loc,ntn,l) -> CNotation (loc,ntn,l))
    (fun (loc,p) -> CPrim (loc,p))
    destPrim l

let make_pat_notation loc ntn l =
  make_notation_gen loc ntn
    (fun (loc,ntn,l) -> CPatNotation (loc,ntn,l))
    (fun (loc,p) -> CPatPrim (loc,p))
    destPatPrim l

let bind_env sigma var v =
  try
    let vvar = List.assoc var sigma in
    if v=vvar then sigma else raise No_match
  with Not_found ->
    (* TODO: handle the case of multiple occs in different scopes *)
    (var,v)::sigma

let rec match_cases_pattern metas sigma a1 a2 = match (a1,a2) with
  | r1, AVar id2 when List.mem id2 metas -> bind_env sigma id2 r1
  | PatVar (_,Anonymous), AHole _ -> sigma
  | a, AHole _ -> sigma
  | PatCstr (loc,(ind,_ as r1),args1,_), _ ->
      let nparams =
	(fst (Global.lookup_inductive ind)).Declarations.mind_nparams in
      let l2 =
        match a2 with
	  | ARef (ConstructRef r2) when r1 = r2 -> []
	  | AApp (ARef (ConstructRef r2),l2)  when r1 = r2 -> l2
          | _ -> raise No_match in
      if List.length l2 <> nparams + List.length args1
      then raise No_match
      else
        let (p2,args2) = list_chop nparams l2 in
        (* All parameters must be _ *)
        List.iter (function AHole _ -> () | _ -> raise No_match) p2;
	List.fold_left2 (match_cases_pattern metas) sigma args1 args2
  | _ -> raise No_match

let match_aconstr_cases_pattern c (metas_scl,pat) =
  let subst = match_cases_pattern (List.map fst metas_scl) [] c pat in
  (* Reorder canonically the substitution *)
  let find x subst =
    try List.assoc x subst
    with Not_found -> anomaly "match_aconstr_cases_pattern" in
  List.map (fun (x,scl) -> (find x subst,scl)) metas_scl

 (* Better to use extern_rawconstr composed with injection/retraction ?? *)
let rec extern_cases_pattern_in_scope (scopes:local_scopes) vars pat =
  try 
    if !Options.raw_print or !print_no_symbol then raise No_match;
    let (na,sc,p) = uninterp_prim_token_cases_pattern pat in
    match availability_of_prim_token sc scopes with
    | None -> raise No_match
    | Some key ->
      let loc = cases_pattern_loc pat in
      insert_pat_alias loc (insert_pat_delimiters loc (CPatPrim(loc,p)) key) na
  with No_match ->
  try 
    if !Options.raw_print or !print_no_symbol then raise No_match;
    extern_symbol_pattern scopes vars pat
      (uninterp_cases_pattern_notations pat)
  with No_match ->
  match pat with
  | PatVar (loc,Name id) -> CPatAtom (loc,Some (Ident (loc,id)))
  | PatVar (loc,Anonymous) -> CPatAtom (loc, None) 
  | PatCstr(loc,cstrsp,args,na) ->
      let args = List.map (extern_cases_pattern_in_scope scopes vars) args in
      let p = CPatCstr
        (loc,extern_reference loc vars (ConstructRef cstrsp),args) in
      insert_pat_alias loc p na
	
and extern_symbol_pattern (tmp_scope,scopes as allscopes) vars t = function
  | [] -> raise No_match
  | (keyrule,pat,n as _rule)::rules ->
      try
	(* Check the number of arguments expected by the notation *)
	let loc,na = match t,n with
	  | PatCstr (_,f,l,_), Some n when List.length l > n ->
	      raise No_match
	  | PatCstr (loc,_,_,na),_ -> loc,na
	  | PatVar (loc,na),_ -> loc,na in
	(* Try matching ... *)
	let subst = match_aconstr_cases_pattern t pat in
	(* Try availability of interpretation ... *)
	let p = match keyrule with
          | NotationRule (sc,ntn) ->
	      (match availability_of_notation (sc,ntn) allscopes with
                  (* Uninterpretation is not allowed in current context *)
              | None -> raise No_match
                  (* Uninterpretation is allowed in current context *)
	      | Some (scopt,key) ->
	          let scopes' = option_cons scopt scopes in
	          let l =
		    List.map (fun (c,(scopt,scl)) ->
		      extern_cases_pattern_in_scope (scopt,scl@scopes') vars c)
                      subst in
		  insert_pat_delimiters loc (make_pat_notation loc ntn l) key)
          | SynDefRule kn ->
	      let qid = shortest_qualid_of_syndef vars kn in
              CPatAtom (loc,Some (Qualid (loc, qid))) in
	insert_pat_alias loc p na
      with
	  No_match -> extern_symbol_pattern allscopes vars t rules

let extern_cases_pattern vars p = 
  extern_cases_pattern_in_scope (None,[]) vars p

(**********************************************************************)
(* Externalising applications *)

let occur_name na aty =
  match na with
    | Name id -> occur_var_constr_expr id aty
    | Anonymous -> false

let is_projection nargs = function
  | Some r when not !Options.raw_print & !print_projections ->
      (try 
	let n = Recordops.find_projection_nparams r + 1 in
	if n <= nargs then Some n else None
      with Not_found -> None)
  | _ -> None

let is_hole = function CHole _ -> true | _ -> false

let is_significant_implicit a impl tail =
  not (is_hole a) or (tail = [] & not (List.for_all is_status_implicit impl))

(* Implicit args indexes are in ascending order *)
(* inctx is useful only if there is a last argument to be deduced from ctxt *)
let explicitize loc inctx impl (cf,f) args =
  let n = List.length args in
  let rec exprec q = function
    | a::args, imp::impl when is_status_implicit imp ->
        let tail = exprec (q+1) (args,impl) in
        let visible =
          !Options.raw_print or
          (!print_implicits & !print_implicits_explicit_args) or 
	  (!print_implicits_defensive &
	   is_significant_implicit a impl tail &
	   not (is_inferable_implicit inctx n imp))
	in
        if visible then 
	  (a,Some (dummy_loc, ExplByName (name_of_implicit imp))) :: tail 
	else
	  tail
    | a::args, _::impl -> (a,None) :: exprec (q+1) (args,impl)
    | args, [] -> List.map (fun a -> (a,None)) args (*In case of polymorphism*)
    | [], _ -> [] in
  match is_projection (List.length args) cf with
    | Some i as ip ->
	if impl <> [] & is_status_implicit (List.nth impl (i-1)) then
	  let f' = match f with CRef f -> f | _ -> assert false in
	  CAppExpl (loc,(ip,f'),args)
	else
	  let (args1,args2) = list_chop i args in
	  let (impl1,impl2) = if impl=[] then [],[] else list_chop i impl in
	  let args1 = exprec 1 (args1,impl1) in
	  let args2 = exprec (i+1) (args2,impl2) in
	  CApp (loc,(Some (List.length args1),f),args1@args2)
    | None -> 
	let args = exprec 1 (args,impl) in
	if args = [] then f else CApp (loc, (None, f), args)

let extern_global loc impl f =
  if impl <> [] & List.for_all is_status_implicit impl then
    CAppExpl (loc, (None, f), [])
  else
    CRef f

let extern_app loc inctx impl (cf,f) args =
  if args = [] (* maybe caused by a hidden coercion *) then
    extern_global loc impl f
  else
  if 
    ((!Options.raw_print or
      (!print_implicits & not !print_implicits_explicit_args)) &
     List.exists is_status_implicit impl)
  then 
    CAppExpl (loc, (is_projection (List.length args) cf, f), args)
  else
    explicitize loc inctx impl (cf,CRef f) args

let rec extern_args extern scopes env args subscopes =
  match args with
    | [] -> []
    | a::args ->
	let argscopes, subscopes = match subscopes with
	  | [] -> (None,scopes), []
	  | scopt::subscopes -> (scopt,scopes), subscopes in
	extern argscopes env a :: extern_args extern scopes env args subscopes

let rec remove_coercions inctx = function
  | RApp (loc,RRef (_,r),args) as c
      when  not (!Options.raw_print or !print_coercions)
      ->
      let nargs = List.length args in
      (try match Classops.hide_coercion r with
	  | Some n when n < nargs && (inctx or n+1 < nargs) ->
	      (* We skip a coercion *) 
	      let l = list_skipn n args in
	      let (a,l) = match l with a::l -> (a,l) | [] -> assert false in
	      let (a,l) =
                (* Recursively remove the head coercions *)
                match remove_coercions true a with
                  | RApp (_,a,l') -> a,l'@l
                  | a -> a,l in
              if l = [] then a
              else
                (* Recursively remove coercions in arguments *)
                RApp (loc,a,List.map (remove_coercions true) l)
	  | _ -> c
      with Not_found -> c)
  | c -> c

let rec rename_rawconstr_var id0 id1 = function
    RRef(loc,VarRef id) when id=id0 -> RRef(loc,VarRef id1)
  | RVar(loc,id) when id=id0 -> RVar(loc,id1)
  | c -> map_rawconstr (rename_rawconstr_var id0 id1) c

let rec share_fix_binders n rbl ty def =
  match ty,def with
      RProd(_,na0,t0,b), RLambda(_,na1,t1,m) ->
        if not(same_rawconstr t0 t1) then List.rev rbl, ty, def
        else
          let (na,b,m) =
            match na0, na1 with
                Name id0, Name id1 ->
                  if id0=id1 then (na0,b,m)
                  else if not (occur_rawconstr id1 b) then
                    (na1,rename_rawconstr_var id0 id1 b,m)
                  else if not (occur_rawconstr id0 m) then
                    (na1,b,rename_rawconstr_var id1 id0 m)
                  else (* vraiment pas de chance! *)
                    failwith "share_fix_binders: capture"
              | Name id, Anonymous ->
                  if not (occur_rawconstr id m) then (na0,b,m)
                  else
                    failwith "share_fix_binders: capture"
              | Anonymous, Name id -> 
                  if not (occur_rawconstr id b) then (na1,b,m)
                  else
                    failwith "share_fix_binders: capture"
              | _ -> (na1,b,m) in
          share_fix_binders (n-1) ((na,None,t0)::rbl) b m
    | _ -> List.rev rbl, ty, def

(**********************************************************************)
(* mapping rawterms to numerals (in presence of coercions, choose the *)
(* one with no delimiter if possible)                                 *)

let extern_possible_prim_token scopes r =
  try
    let (sc,n) = uninterp_prim_token r in
    match availability_of_prim_token sc scopes with
    | None -> None
    | Some key -> Some (insert_delimiters (CPrim (loc_of_rawconstr r,n)) key)
  with No_match ->
    None

let extern_optimal_prim_token scopes r r' =
  let c = extern_possible_prim_token scopes r in
  let c' = if r==r' then None else extern_possible_prim_token scopes r' in
  match c,c' with
  | Some n, (Some (CDelimiters _) | None) | _, Some n -> n
  | _ -> raise No_match

(**********************************************************************)
(* mapping rawterms to constr_expr                                    *)

let extern_rawsort = function
  | RProp _ as s -> s
  | RType (Some _) as s when !print_universes -> s
  | RType _ -> RType None

let rec extern inctx scopes vars r =
  let r' = remove_coercions inctx r in
  try 
    if !Options.raw_print or !print_no_symbol then raise No_match;
    extern_optimal_prim_token scopes r r'
  with No_match ->
  try 
    if !Options.raw_print or !print_no_symbol then raise No_match;
    extern_symbol scopes vars r' (uninterp_notations r')
  with No_match -> match r' with
  | RRef (loc,ref) ->
      extern_global loc (implicits_of_global ref)
        (extern_reference loc vars ref)

  | RVar (loc,id) -> CRef (Ident (loc,id))

  | REvar (loc,n,None) when !print_meta_as_hole -> CHole loc

  | REvar (loc,n,l) ->
      extern_evar loc n (Option.map (List.map (extern false scopes vars)) l)

  | RPatVar (loc,n) ->
      if !print_meta_as_hole then CHole loc else CPatVar (loc,n)

  | RApp (loc,f,args) ->
      (match f with
	 | RRef (rloc,ref) ->
	     let subscopes = find_arguments_scope ref in
	     let args =
	       extern_args (extern true) (snd scopes) vars args subscopes in
	     extern_app loc inctx (implicits_of_global ref)
               (Some ref,extern_reference rloc vars ref)
	       args
	 | _       -> 
	     explicitize loc inctx [] (None,sub_extern false scopes vars f)
               (List.map (sub_extern true scopes vars) args))

  | RProd (loc,Anonymous,t,c) ->
      (* Anonymous product are never factorized *)
      CArrow (loc,extern_typ scopes vars t, extern_typ scopes vars c)

  | RLetIn (loc,na,t,c) ->
      CLetIn (loc,(loc,na),sub_extern false scopes vars t,
              extern inctx scopes (add_vname vars na) c)

  | RProd (loc,na,t,c) ->
      let t = extern_typ scopes vars (anonymize_if_reserved na t) in
      let (idl,c) = factorize_prod scopes (add_vname vars na) t c in
      CProdN (loc,[(dummy_loc,na)::idl,t],c)

  | RLambda (loc,na,t,c) ->
      let t = extern_typ scopes vars (anonymize_if_reserved na t) in
      let (idl,c) = factorize_lambda inctx scopes (add_vname vars na) t c in
      CLambdaN (loc,[(dummy_loc,na)::idl,t],c)

  | RCases (loc,rtntypopt,tml,eqns) ->
      let vars' = 
	List.fold_right (name_fold Idset.add)
	  (cases_predicate_names tml) vars in
      let rtntypopt' = Option.map (extern_typ scopes vars') rtntypopt in
      let tml = List.map (fun (tm,(na,x)) ->
        let na' = match na,tm with
            Anonymous, RVar (_,id) when 
              rtntypopt<>None & occur_rawconstr id (Option.get rtntypopt)
              -> Some Anonymous
          | Anonymous, _ -> None
          | Name id, RVar (_,id') when id=id' -> None
          | Name _, _ -> Some na in
	(sub_extern false scopes vars tm,
	(na',Option.map (fun (loc,ind,n,nal) ->
	  let params = list_tabulate
	    (fun _ -> RHole (dummy_loc,Evd.InternalHole)) n in
	  let args = List.map (function
	    | Anonymous -> RHole (dummy_loc,Evd.InternalHole) 
	    | Name id -> RVar (dummy_loc,id)) nal in
	  let t = RApp (dummy_loc,RRef (dummy_loc,IndRef ind),params@args) in
	  (extern_typ scopes vars t)) x))) tml in
      let eqns = List.map (extern_eqn (rtntypopt<>None) scopes vars) eqns in 
      CCases (loc,rtntypopt',tml,eqns)

  | RLetTuple (loc,nal,(na,typopt),tm,b) ->
      CLetTuple (loc,nal,
        (Option.map (fun _ -> na) typopt,
         Option.map (extern_typ scopes (add_vname vars na)) typopt),
        sub_extern false scopes vars tm,
        extern false scopes (List.fold_left add_vname vars nal) b)

  | RIf (loc,c,(na,typopt),b1,b2) ->
      CIf (loc,sub_extern false scopes vars c,
        (Option.map (fun _ -> na) typopt,
         Option.map (extern_typ scopes (add_vname vars na)) typopt),
        sub_extern false scopes vars b1, sub_extern false scopes vars b2)

  | RRec (loc,fk,idv,blv,tyv,bv) ->
      let vars' = Array.fold_right Idset.add idv vars in
      (match fk with
	 | RFix (nv,n) ->
	     let listdecl = 
	       Array.mapi (fun i fi ->
                 let (bl,ty,def) = blv.(i), tyv.(i), bv.(i) in
                 let (ids,bl) = extern_local_binder scopes vars bl in
                 let vars0 = List.fold_right (name_fold Idset.add) ids vars in
                 let vars1 = List.fold_right (name_fold Idset.add) ids vars' in
		 let n, ro = fst nv.(i), extern_recursion_order scopes vars (snd nv.(i)) in
		 (fi, (n, ro), bl, extern_typ scopes vars0 ty,
                  extern false scopes vars1 def)) idv
	     in 
	     CFix (loc,(loc,idv.(n)),Array.to_list listdecl)
	 | RCoFix n -> 
	     let listdecl =
               Array.mapi (fun i fi ->
                 let (ids,bl) = extern_local_binder scopes vars blv.(i) in
                 let vars0 = List.fold_right (name_fold Idset.add) ids vars in
                 let vars1 = List.fold_right (name_fold Idset.add) ids vars' in
		 (fi,bl,extern_typ scopes vars0 tyv.(i),
                  sub_extern false scopes vars1 bv.(i))) idv
	     in
	     CCoFix (loc,(loc,idv.(n)),Array.to_list listdecl))

  | RSort (loc,s) -> CSort (loc,extern_rawsort s)

  | RHole (loc,e) -> CHole loc

  | RCast (loc,c, CastConv (k,t)) ->
      CCast (loc,sub_extern true scopes vars c, CastConv (k,extern_typ scopes vars t))
  | RCast (loc,c, CastCoerce) ->
      CCast (loc,sub_extern true scopes vars c, CastCoerce)

  | RDynamic (loc,d) -> CDynamic (loc,d)

and extern_typ (_,scopes) = 
  extern true (Some Notation.type_scope,scopes)

and sub_extern inctx (_,scopes) = extern inctx (None,scopes)

and factorize_prod scopes vars aty c =
  try 
    if !Options.raw_print or !print_no_symbol then raise No_match;
    ([],extern_symbol scopes vars c (uninterp_notations c))
  with No_match -> match c with
  | RProd (loc,(Name id as na),ty,c)
      when same aty (extern_typ scopes vars (anonymize_if_reserved na ty))
	& not (occur_var_constr_expr id aty) (* avoid na in ty escapes scope *)
	-> let (nal,c) = factorize_prod scopes (Idset.add id vars) aty c in
           ((loc,Name id)::nal,c)
  | c -> ([],extern_typ scopes vars c)

and factorize_lambda inctx scopes vars aty c =
  try 
    if !Options.raw_print or !print_no_symbol then raise No_match;
    ([],extern_symbol scopes vars c (uninterp_notations c))
  with No_match -> match c with
  | RLambda (loc,na,ty,c)
      when same aty (extern_typ scopes vars (anonymize_if_reserved na ty))
	& not (occur_name na aty) (* To avoid na in ty' escapes scope *)
	-> let (nal,c) =
	     factorize_lambda inctx scopes (add_vname vars na) aty c in
           ((loc,na)::nal,c)
  | c -> ([],sub_extern inctx scopes vars c)

and extern_local_binder scopes vars = function
    [] -> ([],[])
  | (na,Some bd,ty)::l ->
      let (ids,l) =
        extern_local_binder scopes (name_fold Idset.add na vars) l in
      (na::ids,
       LocalRawDef((dummy_loc,na), extern false scopes vars bd) :: l)
      
  | (na,None,ty)::l ->
      let ty = extern_typ scopes vars (anonymize_if_reserved na ty) in
      (match extern_local_binder scopes (name_fold Idset.add na vars) l with
          (ids,LocalRawAssum(nal,ty')::l)
            when same ty ty' &
              match na with Name id -> not (occur_var_constr_expr id ty')
                | _ -> true ->
              (na::ids,
               LocalRawAssum((dummy_loc,na)::nal,ty')::l)
        | (ids,l) ->
            (na::ids,
             LocalRawAssum([(dummy_loc,na)],ty) :: l))

and extern_eqn inctx scopes vars (loc,ids,pl,c) =
  (loc,[List.map (extern_cases_pattern_in_scope scopes vars) pl],
   extern inctx scopes vars c)

and extern_symbol (tmp_scope,scopes as allscopes) vars t = function
  | [] -> raise No_match
  | (keyrule,pat,n as _rule)::rules ->
      let loc = Rawterm.loc_of_rawconstr t in
      try
	(* Adjusts to the number of arguments expected by the notation *)
	let (t,args) = match t,n with
	  | RApp (_,(RRef _ as f),args), Some n when List.length args >= n ->
	      let args1, args2 = list_chop n args in
	      (if n = 0 then f else RApp (dummy_loc,f,args1)), args2
	  | RApp (_,(RRef _ as f),args), None -> f, args
	  | RRef _, Some 0 -> RApp (dummy_loc,t,[]), []
          | _, None -> t,[]
          | _ -> raise No_match in
	(* Try matching ... *)
	let subst = match_aconstr t pat in
	(* Try availability of interpretation ... *)
        let e =
          match keyrule with
          | NotationRule (sc,ntn) ->
	      (match availability_of_notation (sc,ntn) allscopes with
                  (* Uninterpretation is not allowed in current context *)
              | None -> raise No_match
                  (* Uninterpretation is allowed in current context *)
	      | Some (scopt,key) ->
	          let scopes' = option_cons scopt scopes in
	          let l =
		    List.map (fun (c,(scopt,scl)) ->
		      extern (* assuming no overloading: *) true
		        (scopt,scl@scopes') vars c)
                      subst in
	          insert_delimiters (make_notation loc ntn l) key)
          | SynDefRule kn ->
              CRef (Qualid (loc, shortest_qualid_of_syndef vars kn)) in
 	if args = [] then e 
	else
	  (* TODO: compute scopt for the extra args, in case, head is a ref *)
	  explicitize loc false [] (None,e)
	  (List.map (extern true allscopes vars) args)
      with
	  No_match -> extern_symbol allscopes vars t rules

and extern_recursion_order scopes vars = function
    RStructRec -> CStructRec
  | RWfRec c -> CWfRec (extern true scopes vars c)
  | RMeasureRec c -> CMeasureRec (extern true scopes vars c)


let extern_rawconstr vars c =
  extern false (None,[]) vars c

let extern_rawtype vars c =
  extern_typ (None,[]) vars c

(******************************************************************)
(* Main translation function from constr -> constr_expr *)

let loc = dummy_loc (* for constr and pattern, locations are lost *)

let extern_constr_gen at_top scopt env t =
  let avoid = if at_top then ids_of_context env else [] in
  let r = Detyping.detype at_top avoid (names_of_rel_context env) t in
  let vars = vars_of_env env in
  extern false (scopt,[]) vars r

let extern_constr_in_scope at_top scope env t =
  extern_constr_gen at_top (Some scope) env t

let extern_constr at_top env t =
  extern_constr_gen at_top None env t

let extern_type at_top env t =
  let avoid = if at_top then ids_of_context env else [] in
  let r = Detyping.detype at_top avoid (names_of_rel_context env) t in
  extern_rawtype (vars_of_env env) r

let extern_sort s = extern_rawsort (detype_sort s)

(******************************************************************)
(* Main translation function from pattern -> constr_expr *)

let it_destPLambda n c =
  let rec aux n nal c =
    if n=0 then (nal,c) else match c with
      | PLambda (na,_,c) -> aux (n-1) (na::nal) c
      | _ -> anomaly "it_destPLambda" in
  aux n [] c

let rec raw_of_pat env = function
  | PRef ref -> RRef (loc,ref)
  | PVar id -> RVar (loc,id)
  | PEvar (n,l) -> REvar (loc,n,Some (array_map_to_list (raw_of_pat env) l))
  | PRel n ->
      let id = try match lookup_name_of_rel n env with
	| Name id   -> id
	| Anonymous ->
	    anomaly "rawconstr_of_pattern: index to an anonymous variable"
      with Not_found -> id_of_string ("[REL "^(string_of_int n)^"]") in
      RVar (loc,id)
  | PMeta None -> RHole (loc,Evd.InternalHole)
  | PMeta (Some n) -> RPatVar (loc,(false,n))
  | PApp (f,args) ->
      RApp (loc,raw_of_pat env f,array_map_to_list (raw_of_pat env) args)
  | PSoApp (n,args) ->
      RApp (loc,RPatVar (loc,(true,n)),
        List.map (raw_of_pat env) args)
  | PProd (na,t,c) ->
      RProd (loc,na,raw_of_pat env t,raw_of_pat (na::env) c)
  | PLetIn (na,t,c) ->
      RLetIn (loc,na,raw_of_pat env t, raw_of_pat (na::env) c)
  | PLambda (na,t,c) ->
      RLambda (loc,na,raw_of_pat env t, raw_of_pat (na::env) c)
  | PIf (c,b1,b2) ->
      RIf (loc, raw_of_pat env c, (Anonymous,None), 
           raw_of_pat env b1, raw_of_pat env b2)
  | PCase ((LetStyle,[|n|],ind,None),PMeta None,tm,[|b|]) ->
      let nal,b = it_destRLambda_or_LetIn_names n (raw_of_pat env b) in
      RLetTuple (loc,nal,(Anonymous,None),raw_of_pat env tm,b)
  | PCase (_,PMeta None,tm,[||]) ->
      RCases (loc,None,[raw_of_pat env tm,(Anonymous,None)],[])
  | PCase ((_,cstr_nargs,indo,ind_nargs),p,tm,bv) ->
      let brs = Array.to_list (Array.map (raw_of_pat env) bv) in
      let brns = Array.to_list cstr_nargs in
        (* ind is None only if no branch and no return type *)
      let ind = Option.get indo in
      let mat = simple_cases_matrix_of_branches ind brns brs in
      let indnames,rtn =
	if p = PMeta None then (Anonymous,None),None
	else 
	  let nparams,n = Option.get ind_nargs in
	  return_type_of_predicate ind nparams n (raw_of_pat env p) in
      RCases (loc,rtn,[raw_of_pat env tm,indnames],mat)
  | PFix f -> Detyping.detype false [] env (mkFix f)
  | PCoFix c -> Detyping.detype false [] env (mkCoFix c)
  | PSort s -> RSort (loc,s)

and raw_of_eqns env constructs consnargsl bl =
  Array.to_list (array_map3 (raw_of_eqn env) constructs consnargsl bl)

and raw_of_eqn env constr construct_nargs branch =
  let make_pat x env b ids =
    let avoid = List.fold_right (name_fold (fun x l -> x::l)) env [] in
    let id = next_name_away_with_default "x" x avoid in
    PatVar (dummy_loc,Name id),(Name id)::env,id::ids
  in
  let rec buildrec ids patlist env n b =
    if n=0 then
      (dummy_loc, ids, 
       [PatCstr(dummy_loc, constr, List.rev patlist,Anonymous)],
       raw_of_pat env b)
    else
      match b with
	| PLambda (x,_,b) -> 
	    let pat,new_env,new_ids = make_pat x env b ids in
            buildrec new_ids (pat::patlist) new_env (n-1) b

	| PLetIn (x,_,b) -> 
	    let pat,new_env,new_ids = make_pat x env b ids in
            buildrec new_ids (pat::patlist) new_env (n-1) b

	| _ ->
	    error "Unsupported branch in case-analysis while printing pattern"
  in 
  buildrec [] [] env construct_nargs branch

let extern_constr_pattern env pat =
  extern true (None,[]) Idset.empty (raw_of_pat env pat)

let extern_rel_context where env sign =
  let a = detype_rel_context where [] (names_of_rel_context env) sign in
  let vars = vars_of_env env in
  snd (extern_local_binder (None,[]) vars a)
