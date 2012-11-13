(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i*)
open Pp
open Errors
open Util
open Names
open Nameops
open Term
open Termops
open Libnames
open Globnames
open Impargs
open Constrexpr
open Constrexpr_ops
open Notation_ops
open Topconstr
open Glob_term
open Glob_ops
open Pattern
open Nametab
open Notation
open Reserve
open Detyping
open Misctypes
open Decl_kinds
(*i*)

(* Translation from glob_constr to front constr *)

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
let print_universes = Detyping.print_universes

(* This suppresses printing of primitive tokens (e.g. numeral) and symbols *)
let print_no_symbol = ref false

(* This governs printing of projections using the dot notation symbols *)
let print_projections = ref false

let print_meta_as_hole = ref false

let with_arguments f = Flags.with_option print_arguments f
let with_implicits f = Flags.with_option print_implicits f
let with_coercions f = Flags.with_option print_coercions f
let with_universes f = Flags.with_option print_universes f
let without_symbols f = Flags.with_option print_no_symbol f
let with_meta_as_hole f = Flags.with_option print_meta_as_hole f

(**********************************************************************)
(* Control printing of records *)

let is_record indsp =
  try
    let _ = Recordops.lookup_structure indsp in
    true
  with Not_found -> false

let encode_record r =
  let indsp = global_inductive r in
  if not (is_record indsp) then
    user_err_loc (loc_of_reference r,"encode_record",
    str "This type is not a structure type.");
  indsp

module PrintingRecordRecord =
  PrintingInductiveMake (struct
    let encode = encode_record
    let field = "Record"
    let title = "Types leading to pretty-printing using record notation: "
    let member_message s b =
      str "Terms of " ++ s ++
      str
      (if b then " are printed using record notation"
      else " are not printed using record notation")
  end)

module PrintingRecordConstructor =
  PrintingInductiveMake (struct
    let encode = encode_record
    let field = "Constructor"
    let title = "Types leading to pretty-printing using constructor form: "
    let member_message s b =
      str "Terms of " ++ s ++
      str
      (if b then " are printed using constructor form"
      else " are not printed using constructor form")
  end)

module PrintingRecord = Goptions.MakeRefTable(PrintingRecordRecord)
module PrintingConstructor = Goptions.MakeRefTable(PrintingRecordConstructor)

(**********************************************************************)
(* Various externalisation functions *)

let insert_delimiters e = function
  | None -> e
  | Some sc -> CDelimiters (Loc.ghost,sc,e)

let insert_pat_delimiters loc p = function
  | None -> p
  | Some sc -> CPatDelimiters (loc,sc,p)

let insert_pat_alias loc p = function
  | Anonymous -> p
  | Name id -> CPatAlias (loc,p,id)

(**********************************************************************)
(* conversion of references                                           *)

let extern_evar loc n l =
  if !print_evar_arguments then CEvar (loc,n,l) else CEvar (loc,n,None)

let debug_global_reference_printer =
  ref (fun _ -> failwith "Cannot print a global reference")

let in_debugger = ref false

let set_debug_global_reference_printer f =
  debug_global_reference_printer := f

let extern_reference loc vars r =
  if !in_debugger then
    (* Debugger does not have the tables of global reference at hand *)
    !debug_global_reference_printer loc r
  else
    Qualid (loc,shortest_qualid_of_global vars r)


(************************************************************************)
(* Equality up to location (useful for translator v8) *)

let rec check_same_pattern p1 p2 =
  match p1, p2 with
    | CPatAlias(_,a1,i1), CPatAlias(_,a2,i2) when i1=i2 ->
        check_same_pattern a1 a2
    | CPatCstr(_,c1,a1,b1), CPatCstr(_,c2,a2,b2) when c1=c2 ->
        let () = List.iter2 check_same_pattern a1 a2 in
        List.iter2 check_same_pattern b1 b2
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
  | CProdN(_,bl1,a1), CProdN(_,bl2,a2) ->
      List.iter2 check_same_binder bl1 bl2;
      check_same_type a1 a2
  | CLambdaN(_,bl1,a1), CLambdaN(_,bl2,a2) ->
      List.iter2 check_same_binder bl1 bl2;
      check_same_type a1 a2
  | CLetIn(_,(_,na1),a1,b1), CLetIn(_,(_,na2),a2,b2) when na1=na2 ->
      check_same_type a1 a2;
      check_same_type b1 b2
  | CAppExpl(_,(proj1,r1),al1), CAppExpl(_,(proj2,r2),al2) when proj1=proj2 ->
      check_same_ref r1 r2;
      List.iter2 check_same_type al1 al2
  | CApp(_,(_,e1),al1), CApp(_,(_,e2),al2) ->
      check_same_type e1 e2;
      List.iter2 (fun (a1,e1) (a2,e2) ->
                    if e1<>e2 then failwith "not same expl";
                    check_same_type a1 a2) al1 al2
  | CCases(_,_,_,a1,brl1), CCases(_,_,_,a2,brl2) ->
      List.iter2 (fun (tm1,_) (tm2,_) -> check_same_type tm1 tm2) a1 a2;
      List.iter2 (fun (_,pl1,r1) (_,pl2,r2) ->
        List.iter2 (Loc.located_iter2 (List.iter2 check_same_pattern)) pl1 pl2;
        check_same_type r1 r2) brl1 brl2
  | CHole _, CHole _ -> ()
  | CPatVar(_,i1), CPatVar(_,i2) when i1=i2 -> ()
  | CSort(_,s1), CSort(_,s2) when s1=s2 -> ()
  | CCast(_,a1,(CastConv b1|CastVM b1)), CCast(_,a2,(CastConv b2|CastVM b2)) ->
      check_same_type a1 a2;
      check_same_type b1 b2
  | CCast(_,a1,CastCoerce), CCast(_,a2, CastCoerce) ->
      check_same_type a1 a2
  | CNotation(_,n1,(e1,el1,bl1)), CNotation(_,n2,(e2,el2,bl2)) when n1=n2 ->
      List.iter2 check_same_type e1 e2;
      List.iter2 (List.iter2 check_same_type) el1 el2;
      List.iter2 check_same_fix_binder bl1 bl2
  | CPrim(_,i1), CPrim(_,i2) when i1=i2 -> ()
  | CDelimiters(_,s1,e1), CDelimiters(_,s2,e2) when s1=s2 ->
      check_same_type e1 e2
  | _ when ty1=ty2 -> ()
  | _ -> failwith "not same type"

and check_same_binder (nal1,_,e1) (nal2,_,e2) =
  List.iter2 (fun (_,na1) (_,na2) ->
    if na1<>na2 then failwith "not same name") nal1 nal2;
  check_same_type e1 e2

and check_same_fix_binder bl1 bl2 =
  List.iter2 (fun b1 b2 ->
    match b1,b2 with
        LocalRawAssum(nal1,k,ty1), LocalRawAssum(nal2,k',ty2) ->
          check_same_binder (nal1,k,ty1) (nal2,k',ty2)
      | LocalRawDef(na1,def1), LocalRawDef(na2,def2) ->
          check_same_binder ([na1],default_binder_kind,def1) ([na2],default_binder_kind,def2)
      | _ -> failwith "not same binder") bl1 bl2

let is_same_type c d =
  try let () = check_same_type c d in true
  with Failure _ | Invalid_argument _ -> false

(**********************************************************************)
(* mapping patterns to cases_pattern_expr                                *)

let add_patt_for_params ind l =
    Util.List.addn (fst (Inductiveops.inductive_nargs ind)) (CPatAtom (Loc.ghost,None)) l

let drop_implicits_in_patt cst nb_expl args =
  let impl_st = (implicits_of_global cst) in
  let impl_data = extract_impargs_data impl_st in
  let rec impls_fit l = function
    |[],t -> Some (List.rev_append l t)
    |_,[] -> None
    |h::t,CPatAtom(_,None)::tt when is_status_implicit h -> impls_fit l (t,tt)
    |h::_,_ when is_status_implicit h -> None
    |_::t,hh::tt -> impls_fit (hh::l) (t,tt)
  in let rec aux = function
    |[] -> None
    |(_,imps)::t -> match impls_fit [] (imps,args) with
	|None -> aux t
	|x -> x
     in
     if Int.equal nb_expl 0 then aux impl_data
     else
       let imps = List.skipn_at_least nb_expl (select_stronger_impargs impl_st) in
       impls_fit [] (imps,args)

let has_curly_brackets ntn =
  String.length ntn >= 6 & (String.sub ntn 0 6 = "{ _ } " or
    String.sub ntn (String.length ntn - 6) 6 = " { _ }" or
    String.string_contains ~where:ntn ~what:" { _ } ")

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
    (* Special case to avoid writing "- 3" for e.g. (Z.opp 3) *)
    | "- _", [Some (Numeral p)] when Bigint.is_strictly_pos p ->
        mknot (loc,ntn,([mknot (loc,"( _ )",l)]))
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

let make_notation loc ntn (terms,termlists,binders as subst) =
  if termlists <> [] or binders <> [] then CNotation (loc,ntn,subst) else
  make_notation_gen loc ntn
    (fun (loc,ntn,l) -> CNotation (loc,ntn,(l,[],[])))
    (fun (loc,p) -> CPrim (loc,p))
    destPrim terms

let make_pat_notation loc ntn (terms,termlists as subst) args =
  if termlists <> [] then CPatNotation (loc,ntn,subst,args) else
  make_notation_gen loc ntn
    (fun (loc,ntn,l) -> CPatNotation (loc,ntn,(l,[]),args))
    (fun (loc,p) -> CPatPrim (loc,p))
    destPatPrim terms

let mkPat loc qid l =
  (* Normally irrelevant test with v8 syntax, but let's do it anyway *)
  if l = [] then CPatAtom (loc,Some qid) else CPatCstr (loc,qid,[],l)

let pattern_printable_in_both_syntax (ind,_ as c) =
  let impl_st = extract_impargs_data (implicits_of_global (ConstructRef c)) in
  let nb_params = Inductiveops.inductive_nparams ind in
  List.exists (fun (_,impls) ->
    (List.length impls >= nb_params) &&
      let params,args = Util.List.chop nb_params impls in
      (List.for_all is_status_implicit params)&&(List.for_all (fun x -> not (is_status_implicit x)) args)
  ) impl_st

 (* Better to use extern_glob_constr composed with injection/retraction ?? *)
let rec extern_cases_pattern_in_scope (scopes:local_scopes) vars pat =
  (* pboutill: There are letins in pat which is incompatible with notations and
     not explicit application. *)
  match pat with
    | PatCstr(loc,cstrsp,args,na)
	when !in_debugger||Inductiveops.mis_constructor_has_local_defs cstrsp ->
      let c = extern_reference loc Idset.empty (ConstructRef cstrsp) in
      let args = List.map (extern_cases_pattern_in_scope scopes vars) args in
      CPatCstr (loc, c, add_patt_for_params (fst cstrsp) args, [])
    | _ ->
  try
    if !Flags.raw_print or !print_no_symbol then raise No_match;
    let (na,sc,p) = uninterp_prim_token_cases_pattern pat in
    match availability_of_prim_token p sc scopes with
      | None -> raise No_match
      | Some key ->
	let loc = cases_pattern_loc pat in
	insert_pat_alias loc (insert_pat_delimiters loc (CPatPrim(loc,p)) key) na
  with No_match ->
    try
      if !Flags.raw_print or !print_no_symbol then raise No_match;
      extern_symbol_pattern scopes vars pat
	(uninterp_cases_pattern_notations pat)
    with No_match ->
      match pat with
	| PatVar (loc,Name id) -> CPatAtom (loc,Some (Ident (loc,id)))
	| PatVar (loc,Anonymous) -> CPatAtom (loc, None)
	| PatCstr(loc,cstrsp,args,na) ->
	  let args = List.map (extern_cases_pattern_in_scope scopes vars) args in
	  let p =
	    try
              if !in_debugger || !Flags.raw_print then raise Exit;
	      let projs = Recordops.lookup_projections (fst cstrsp) in
	      let rec ip projs args acc =
		match projs with
		  | [] -> acc
		  | None :: q -> ip q args acc
		  | Some c :: q ->
		    match args with
		      | [] -> raise No_match
		      | CPatAtom(_, None) :: tail -> ip q tail acc
		    (* we don't want to have 'x = _' in our patterns *)
		      | head :: tail -> ip q tail
		        ((extern_reference loc Idset.empty (ConstRef c), head) :: acc)
	      in
	      CPatRecord(loc, List.rev (ip projs args []))
	    with
		Not_found | No_match | Exit ->
                  let c = extern_reference loc Idset.empty (ConstructRef cstrsp) in
		  if !Topconstr.oldfashion_patterns then
		    if pattern_printable_in_both_syntax cstrsp
		    then CPatCstr (loc, c, [], args)
		    else CPatCstr (loc, c, add_patt_for_params (fst cstrsp) args, [])
		  else
		    let full_args = add_patt_for_params (fst cstrsp) args in
		    match drop_implicits_in_patt (ConstructRef cstrsp) 0 full_args with
		      |Some true_args -> CPatCstr (loc, c, [], true_args)
		      |None -> CPatCstr (loc, c, full_args, [])
	  in insert_pat_alias loc p na
and apply_notation_to_pattern loc gr ((subst,substlist),(nb_to_drop,more_args))
    (tmp_scope, scopes as allscopes) vars =
  function
    | NotationRule (sc,ntn) ->
      begin
	match availability_of_notation (sc,ntn) allscopes with
	  (* Uninterpretation is not allowed in current context *)
	  | None -> raise No_match
	  (* Uninterpretation is allowed in current context *)
	  | Some (scopt,key) ->
	    let scopes' = Option.List.cons scopt scopes in
	    let l =
	      List.map (fun (c,(scopt,scl)) ->
		extern_cases_pattern_in_scope (scopt,scl@scopes') vars c)
		subst in
	    let ll =
	      List.map (fun (c,(scopt,scl)) ->
		let subscope = (scopt,scl@scopes') in
		List.map (extern_cases_pattern_in_scope subscope vars) c)
		substlist in
	    let l2 = List.map (extern_cases_pattern_in_scope allscopes vars) more_args in
	    let l2' = if !Topconstr.oldfashion_patterns || ll <> [] then l2
	      else
		match drop_implicits_in_patt gr nb_to_drop l2 with
		  |Some true_args -> true_args
		  |None -> raise No_match
	    in
	    insert_pat_delimiters loc
	      (make_pat_notation loc ntn (l,ll) l2') key
      end
    | SynDefRule kn ->
      let qid = Qualid (loc, shortest_qualid_of_syndef vars kn) in
      let l1 =
	List.rev_map (fun (c,(scopt,scl)) ->
          extern_cases_pattern_in_scope (scopt,scl@scopes) vars c)
          subst in
      let l2 = List.map (extern_cases_pattern_in_scope allscopes vars) more_args in
      let l2' = if !Topconstr.oldfashion_patterns then l2
	else
	  match drop_implicits_in_patt gr (List.length l1) l2 with
	    |Some true_args -> true_args
	    |None -> raise No_match
      in
      assert (substlist = []);
      mkPat loc qid (List.rev_append l1 l2')
and extern_symbol_pattern (tmp_scope,scopes as allscopes) vars t = function
  | [] -> raise No_match
  | (keyrule,pat,n as _rule)::rules ->
    try
      match t with
	| PatCstr (loc,cstr,_,na) ->
	  let p = apply_notation_to_pattern loc (ConstructRef cstr)
	    (match_notation_constr_cases_pattern t pat) allscopes vars keyrule in
	  insert_pat_alias loc p na
	| PatVar (loc,Anonymous) -> CPatAtom (loc, None)
	| PatVar (loc,Name id) -> CPatAtom (loc, Some (Ident (loc,id)))
    with
	No_match -> extern_symbol_pattern allscopes vars t rules

let rec extern_symbol_ind_pattern allscopes vars ind args = function
  | [] -> raise No_match
  | (keyrule,pat,n as _rule)::rules ->
    try
      apply_notation_to_pattern Loc.ghost (IndRef ind)
	(match_notation_constr_ind_pattern ind args pat) allscopes vars keyrule
    with
	No_match -> extern_symbol_ind_pattern allscopes vars ind args rules

let extern_ind_pattern_in_scope (scopes:local_scopes) vars ind args =
  (* pboutill: There are letins in pat which is incompatible with notations and
     not explicit application. *)
  if !in_debugger||Inductiveops.inductive_has_local_defs ind then
    let c = extern_reference Loc.ghost vars (IndRef ind) in
    let args = List.map (extern_cases_pattern_in_scope scopes vars) args in
    CPatCstr (Loc.ghost, c, add_patt_for_params ind args, [])
  else
    try
      if !Flags.raw_print or !print_no_symbol then raise No_match;
      let (sc,p) = uninterp_prim_token_ind_pattern ind args in
      match availability_of_prim_token p sc scopes with
	| None -> raise No_match
	| Some key ->
	  insert_pat_delimiters Loc.ghost (CPatPrim(Loc.ghost,p)) key
    with No_match ->
      try
	if !Flags.raw_print or !print_no_symbol then raise No_match;
	extern_symbol_ind_pattern scopes vars ind args
	  (uninterp_ind_pattern_notations ind)
    with No_match ->
      let c = extern_reference Loc.ghost vars (IndRef ind) in
      let args = List.map (extern_cases_pattern_in_scope scopes vars) args in
      match drop_implicits_in_patt (IndRef ind) 0 args with
	   |Some true_args -> CPatCstr (Loc.ghost, c, [], true_args)
	   |None -> CPatCstr (Loc.ghost, c, args, [])

let extern_cases_pattern vars p =
  extern_cases_pattern_in_scope (None,[]) vars p

(**********************************************************************)
(* Externalising applications *)

let occur_name na aty =
  match na with
    | Name id -> occur_var_constr_expr id aty
    | Anonymous -> false

let is_projection nargs = function
  | Some r when not !Flags.raw_print & !print_projections ->
      (try
	let n = Recordops.find_projection_nparams r + 1 in
	if n <= nargs then Some n else None
      with Not_found -> None)
  | _ -> None

let is_hole = function CHole _ -> true | _ -> false

let is_significant_implicit a =
  not (is_hole a)

let is_needed_for_correct_partial_application tail imp =
  tail = [] & not (maximal_insertion_of imp)

(* Implicit args indexes are in ascending order *)
(* inctx is useful only if there is a last argument to be deduced from ctxt *)
let explicitize loc inctx impl (cf,f) args =
  let impl = if !Constrintern.parsing_explicit then [] else impl in
  let n = List.length args in
  let rec exprec q = function
    | a::args, imp::impl when is_status_implicit imp ->
        let tail = exprec (q+1) (args,impl) in
        let visible =
          !Flags.raw_print or
          (!print_implicits & !print_implicits_explicit_args) or
          (is_needed_for_correct_partial_application tail imp) or
	  (!print_implicits_defensive &
	   is_significant_implicit a &
	   not (is_inferable_implicit inctx n imp))
	in
        if visible then
	  (a,Some (Loc.ghost, ExplByName (name_of_implicit imp))) :: tail
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
	  let (args1,args2) = List.chop i args in
	  let (impl1,impl2) = if impl=[] then [],[] else List.chop i impl in
	  let args1 = exprec 1 (args1,impl1) in
	  let args2 = exprec (i+1) (args2,impl2) in
	  CApp (loc,(Some (List.length args1),f),args1@args2)
    | None ->
	let args = exprec 1 (args,impl) in
	if args = [] then f else CApp (loc, (None, f), args)

let extern_global loc impl f =
  if not !Constrintern.parsing_explicit &&
     impl <> [] && List.for_all is_status_implicit impl
  then
    CAppExpl (loc, (None, f), [])
  else
    CRef f

let extern_app loc inctx impl (cf,f) args =
  if args = [] then
    (* If coming from a notation "Notation a := @b" *)
    CAppExpl (loc, (None, f), [])
  else if not !Constrintern.parsing_explicit &&
    ((!Flags.raw_print or
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
  | GApp (loc,GRef (_,r),args) as c
      when  not (!Flags.raw_print or !print_coercions)
      ->
      let nargs = List.length args in
      (try match Classops.hide_coercion r with
	  | Some n when n < nargs && (inctx or n+1 < nargs) ->
	      (* We skip a coercion *)
	      let l = List.skipn n args in
	      let (a,l) = match l with a::l -> (a,l) | [] -> assert false in
              (* Recursively remove the head coercions *)
	      let a' = remove_coercions true a in
	      (* Don't flatten App's in case of funclass so that
		 (atomic) notations on [a] work; should be compatible
		 since printer does not care whether App's are
		 collapsed or not and notations with an implicit
		 coercion using funclass either would have already
		 been confused with ordinary application or would have need
                 a surrounding context and the coercion to funclass would
                 have been made explicit to match *)
	      if l = [] then a' else GApp (loc,a',l)
	  | _ -> c
      with Not_found -> c)
  | c -> c

let rec flatten_application = function
  | GApp (loc,GApp(_,a,l'),l) -> flatten_application (GApp (loc,a,l'@l))
  | a -> a

(**********************************************************************)
(* mapping glob_constr to numerals (in presence of coercions, choose the *)
(* one with no delimiter if possible)                                 *)

let extern_possible_prim_token scopes r =
  try
    let (sc,n) = uninterp_prim_token r in
    match availability_of_prim_token n sc scopes with
    | None -> None
    | Some key -> Some (insert_delimiters (CPrim (loc_of_glob_constr r,n)) key)
  with No_match ->
    None

let extern_optimal_prim_token scopes r r' =
  let c = extern_possible_prim_token scopes r in
  let c' = if r==r' then None else extern_possible_prim_token scopes r' in
  match c,c' with
  | Some n, (Some (CDelimiters _) | None) | _, Some n -> n
  | _ -> raise No_match

(**********************************************************************)
(* mapping glob_constr to constr_expr                                    *)

let extern_glob_sort = function
  | GProp -> GProp
  | GSet -> GSet
  | GType (Some _) as s when !print_universes -> s
  | GType _ -> GType None

let rec extern inctx scopes vars r =
  let r' = remove_coercions inctx r in
  try
    if !Flags.raw_print or !print_no_symbol then raise No_match;
    extern_optimal_prim_token scopes r r'
  with No_match ->
  try
    let r'' = flatten_application r' in
    if !Flags.raw_print or !print_no_symbol then raise No_match;
    extern_symbol scopes vars r'' (uninterp_notations r'')
  with No_match -> match r' with
  | GRef (loc,ref) ->
      extern_global loc (select_stronger_impargs (implicits_of_global ref))
        (extern_reference loc vars ref)

  | GVar (loc,id) -> CRef (Ident (loc,id))

  | GEvar (loc,n,None) when !print_meta_as_hole -> CHole (loc, None)

  | GEvar (loc,n,l) ->
      extern_evar loc n (Option.map (List.map (extern false scopes vars)) l)

  | GPatVar (loc,n) ->
      if !print_meta_as_hole then CHole (loc, None) else CPatVar (loc,n)

  | GApp (loc,f,args) ->
      (match f with
	 | GRef (rloc,ref) ->
	     let subscopes = find_arguments_scope ref in
	     let args =
	       extern_args (extern true) (snd scopes) vars args subscopes in
	     begin
	       try
                 if !Flags.raw_print then raise Exit;
		 let cstrsp = match ref with ConstructRef c -> c | _ -> raise Not_found in
		 let struc = Recordops.lookup_structure (fst cstrsp) in
                 if PrintingRecord.active (fst cstrsp) then
                   ()
                 else if PrintingConstructor.active (fst cstrsp) then
                   raise Exit
                 else if not !Flags.record_print then
                   raise Exit;
		 let projs = struc.Recordops.s_PROJ in
		 let locals = struc.Recordops.s_PROJKIND in
		 let rec cut args n =
		   if Int.equal n 0 then args
		   else
		     match args with
		     | [] -> raise No_match
		     | _ :: t -> cut t (n - 1) in
		 let args = cut args struc.Recordops.s_EXPECTEDPARAM in
		 let rec ip projs locs args acc =
		   match projs with
		     | [] -> acc
		     | None :: q -> raise No_match
		     | Some c :: q ->
		         match locs with
			   | [] -> anomaly "projections corruption [Constrextern.extern]"
			   | (_, false) :: locs' ->
			       (* we don't want to print locals *)
			       ip q locs' args acc
			   | (_, true) :: locs' ->
			       match args with
				 | [] -> raise No_match
				     (* we give up since the constructor is not complete *)
				 | head :: tail -> ip q locs' tail
				     ((extern_reference loc Idset.empty (ConstRef c), head) :: acc)
		   in
		 CRecord (loc, None, List.rev (ip projs locals args []))
	       with
		 | Not_found | No_match | Exit ->
		     extern_app loc inctx
		       (select_stronger_impargs (implicits_of_global ref))
		       (Some ref,extern_reference rloc vars ref) args
	     end
	 | _       ->
	     explicitize loc inctx [] (None,sub_extern false scopes vars f)
               (List.map (sub_extern true scopes vars) args))

  | GLetIn (loc,na,t,c) ->
      CLetIn (loc,(loc,na),sub_extern false scopes vars t,
              extern inctx scopes (add_vname vars na) c)

  | GProd (loc,na,bk,t,c) ->
      let t = extern_typ scopes vars (anonymize_if_reserved na t) in
      let (idl,c) = factorize_prod scopes (add_vname vars na) na bk t c in
      CProdN (loc,[(Loc.ghost,na)::idl,Default bk,t],c)

  | GLambda (loc,na,bk,t,c) ->
      let t = extern_typ scopes vars (anonymize_if_reserved na t) in
      let (idl,c) = factorize_lambda inctx scopes (add_vname vars na) na bk t c in
      CLambdaN (loc,[(Loc.ghost,na)::idl,Default bk,t],c)

  | GCases (loc,sty,rtntypopt,tml,eqns) ->
    let vars' =
      List.fold_right (name_fold Idset.add)
	(cases_predicate_names tml) vars in
    let rtntypopt' = Option.map (extern_typ scopes vars') rtntypopt in
    let tml = List.map (fun (tm,(na,x)) ->
      let na' = match na,tm with
          Anonymous, GVar (_,id) when
	      rtntypopt<>None & occur_glob_constr id (Option.get rtntypopt)
	      -> Some (Loc.ghost,Anonymous)
        | Anonymous, _ -> None
        | Name id, GVar (_,id') when id=id' -> None
        | Name _, _ -> Some (Loc.ghost,na) in
      (sub_extern false scopes vars tm,
       (na',Option.map (fun (loc,ind,nal) ->
	 let args = List.map (fun x -> PatVar (Loc.ghost, x)) nal in
	 let fullargs = Notation_ops.add_patterns_for_params ind args in
	 extern_ind_pattern_in_scope scopes vars ind fullargs
	) x))) tml in
    let eqns = List.map (extern_eqn inctx scopes vars) eqns in
    CCases (loc,sty,rtntypopt',tml,eqns)

  | GLetTuple (loc,nal,(na,typopt),tm,b) ->
      CLetTuple (loc,List.map (fun na -> (Loc.ghost,na)) nal,
        (Option.map (fun _ -> (Loc.ghost,na)) typopt,
         Option.map (extern_typ scopes (add_vname vars na)) typopt),
        sub_extern false scopes vars tm,
        extern inctx scopes (List.fold_left add_vname vars nal) b)

  | GIf (loc,c,(na,typopt),b1,b2) ->
      CIf (loc,sub_extern false scopes vars c,
        (Option.map (fun _ -> (Loc.ghost,na)) typopt,
         Option.map (extern_typ scopes (add_vname vars na)) typopt),
        sub_extern inctx scopes vars b1, sub_extern inctx scopes vars b2)

  | GRec (loc,fk,idv,blv,tyv,bv) ->
      let vars' = Array.fold_right Idset.add idv vars in
      (match fk with
	 | GFix (nv,n) ->
	     let listdecl =
	       Array.mapi (fun i fi ->
                 let (bl,ty,def) = blv.(i), tyv.(i), bv.(i) in
                 let (assums,ids,bl) = extern_local_binder scopes vars bl in
                 let vars0 = List.fold_right (name_fold Idset.add) ids vars in
                 let vars1 = List.fold_right (name_fold Idset.add) ids vars' in
		 let n =
		   match fst nv.(i) with
		     | None -> None
		     | Some x -> Some (Loc.ghost, out_name (List.nth assums x))
		 in
		 let ro = extern_recursion_order scopes vars (snd nv.(i)) in
		 ((Loc.ghost, fi), (n, ro), bl, extern_typ scopes vars0 ty,
                  extern false scopes vars1 def)) idv
	     in
	     CFix (loc,(loc,idv.(n)),Array.to_list listdecl)
	 | GCoFix n ->
	     let listdecl =
               Array.mapi (fun i fi ->
                 let (_,ids,bl) = extern_local_binder scopes vars blv.(i) in
                 let vars0 = List.fold_right (name_fold Idset.add) ids vars in
                 let vars1 = List.fold_right (name_fold Idset.add) ids vars' in
		 ((Loc.ghost, fi),bl,extern_typ scopes vars0 tyv.(i),
                  sub_extern false scopes vars1 bv.(i))) idv
	     in
	     CCoFix (loc,(loc,idv.(n)),Array.to_list listdecl))

  | GSort (loc,s) -> CSort (loc,extern_glob_sort s)

  | GHole (loc,e) -> CHole (loc, Some e)

  | GCast (loc,c, c') ->
      CCast (loc,sub_extern true scopes vars c,
	     Miscops.map_cast_type (extern_typ scopes vars) c')

and extern_typ (_,scopes) =
  extern true (Some Notation.type_scope,scopes)

and sub_extern inctx (_,scopes) = extern inctx (None,scopes)

and factorize_prod scopes vars na bk aty c =
  let c = extern_typ scopes vars c in
  match na, c with
  | Name id, CProdN (loc,[nal,Default bk',ty],c)
      when bk = bk' && is_same_type aty ty
      & not (occur_var_constr_expr id ty) (* avoid na in ty escapes scope *) ->
      nal,c
  | _ ->
      [],c

and factorize_lambda inctx scopes vars na bk aty c =
  let c = sub_extern inctx scopes vars c in
  match c with
  | CLambdaN (loc,[nal,Default bk',ty],c)
      when bk = bk' && is_same_type aty ty
      & not (occur_name na ty) (* avoid na in ty escapes scope *) ->
      nal,c
  | _ ->
      [],c

and extern_local_binder scopes vars = function
    [] -> ([],[],[])
  | (na,bk,Some bd,ty)::l ->
      let (assums,ids,l) =
        extern_local_binder scopes (name_fold Idset.add na vars) l in
      (assums,na::ids,
       LocalRawDef((Loc.ghost,na), extern false scopes vars bd) :: l)

  | (na,bk,None,ty)::l ->
      let ty = extern_typ scopes vars (anonymize_if_reserved na ty) in
      (match extern_local_binder scopes (name_fold Idset.add na vars) l with
          (assums,ids,LocalRawAssum(nal,k,ty')::l)
            when is_same_type ty ty' &
              match na with Name id -> not (occur_var_constr_expr id ty')
                | _ -> true ->
              (na::assums,na::ids,
               LocalRawAssum((Loc.ghost,na)::nal,k,ty')::l)
        | (assums,ids,l) ->
            (na::assums,na::ids,
             LocalRawAssum([(Loc.ghost,na)],Default bk,ty) :: l))

and extern_eqn inctx scopes vars (loc,ids,pl,c) =
  (loc,[loc,List.map (extern_cases_pattern_in_scope scopes vars) pl],
   extern inctx scopes vars c)

and extern_symbol (tmp_scope,scopes as allscopes) vars t = function
  | [] -> raise No_match
  | (keyrule,pat,n as _rule)::rules ->
      let loc = Glob_ops.loc_of_glob_constr t in
      try
	(* Adjusts to the number of arguments expected by the notation *)
	let (t,args,argsscopes,argsimpls) = match t,n with
	  | GApp (_,f,args), Some n
	      when List.length args >= n ->
	      let args1, args2 = List.chop n args in
              let subscopes, impls =
                match f with
                | GRef (_,ref) ->
	          let subscopes =
		    try List.skipn n (find_arguments_scope ref) with _ -> [] in
	          let impls =
		    let impls =
		      select_impargs_size
		        (List.length args) (implicits_of_global ref) in
		    try List.skipn n impls with _ -> [] in
                  subscopes,impls
                | _ ->
                  [], [] in
	      (if Int.equal n 0 then f else GApp (Loc.ghost,f,args1)),
	      args2, subscopes, impls
	  | GApp (_,(GRef (_,ref) as f),args), None ->
	      let subscopes = find_arguments_scope ref in
	      let impls =
		  select_impargs_size
		    (List.length args) (implicits_of_global ref) in
	      f, args, subscopes, impls
	  | GRef _, Some 0 -> GApp (Loc.ghost,t,[]), [], [], []
          | _, None -> t, [], [], []
          | _ -> raise No_match in
	(* Try matching ... *)
	let terms,termlists,binders =
          match_notation_constr !print_universes t pat in
	(* Try availability of interpretation ... *)
        let e =
          match keyrule with
          | NotationRule (sc,ntn) ->
	      (match availability_of_notation (sc,ntn) allscopes with
                  (* Uninterpretation is not allowed in current context *)
              | None -> raise No_match
                  (* Uninterpretation is allowed in current context *)
	      | Some (scopt,key) ->
	          let scopes' = Option.List.cons scopt scopes in
	          let l =
		    List.map (fun (c,(scopt,scl)) ->
		      extern (* assuming no overloading: *) true
		        (scopt,scl@scopes') vars c)
                      terms in
		  let ll =
		    List.map (fun (c,(scopt,scl)) ->
		      List.map (extern true (scopt,scl@scopes') vars) c)
                      termlists in
		  let bll =
		    List.map (fun (bl,(scopt,scl)) ->
		      pi3 (extern_local_binder (scopt,scl@scopes') vars bl))
                      binders in
	          insert_delimiters (make_notation loc ntn (l,ll,bll)) key)
          | SynDefRule kn ->
	      let l =
		List.map (fun (c,(scopt,scl)) ->
		  extern true (scopt,scl@scopes) vars c, None)
		  terms in
              let a = CRef (Qualid (loc, shortest_qualid_of_syndef vars kn)) in
	      if l = [] then a else CApp (loc,(None,a),l) in
 	if args = [] then e
	else
	  let args = extern_args (extern true) scopes vars args argsscopes in
	  explicitize loc false argsimpls (None,e) args
      with
	  No_match -> extern_symbol allscopes vars t rules

and extern_recursion_order scopes vars = function
    GStructRec -> CStructRec
  | GWfRec c -> CWfRec (extern true scopes vars c)
  | GMeasureRec (m,r) -> CMeasureRec (extern true scopes vars m,
				     Option.map (extern true scopes vars) r)


let extern_glob_constr vars c =
  extern false (None,[]) vars c

let extern_glob_type vars c =
  extern_typ (None,[]) vars c

(******************************************************************)
(* Main translation function from constr -> constr_expr *)

let loc = Loc.ghost (* for constr and pattern, locations are lost *)

let extern_constr_gen goal_concl_style scopt env t =
  (* "goal_concl_style" means do alpha-conversion using the "goal" convention *)
  (* i.e.: avoid using the names of goal/section/rel variables and the short *)
  (* names of global definitions of current module when computing names for *)
  (* bound variables. *)
  (* Not "goal_concl_style" means do alpha-conversion avoiding only *)
  (* those goal/section/rel variables that occurs in the subterm under *)
  (* consideration; see namegen.ml for further details *)
  let avoid = if goal_concl_style then ids_of_context env else [] in
  let rel_env_names = names_of_rel_context env in
  let r = Detyping.detype goal_concl_style avoid rel_env_names t in
  let vars = vars_of_env env in
  extern false (scopt,[]) vars r

let extern_constr_in_scope goal_concl_style scope env t =
  extern_constr_gen goal_concl_style (Some scope) env t

let extern_constr goal_concl_style env t =
  extern_constr_gen goal_concl_style None env t

let extern_type goal_concl_style env t =
  let avoid = if goal_concl_style then ids_of_context env else [] in
  let rel_env_names = names_of_rel_context env in
  let r = Detyping.detype goal_concl_style avoid rel_env_names t in
  extern_glob_type (vars_of_env env) r

let extern_sort s = extern_glob_sort (detype_sort s)

(******************************************************************)
(* Main translation function from pattern -> constr_expr *)

let any_any_branch =
  (* | _ => _ *)
  (loc,[],[PatVar (loc,Anonymous)],GHole (loc,Evar_kinds.InternalHole))

let rec glob_of_pat env = function
  | PRef ref -> GRef (loc,ref)
  | PVar id -> GVar (loc,id)
  | PEvar (n,l) -> GEvar (loc,n,Some (Array.map_to_list (glob_of_pat env) l))
  | PRel n ->
      let id = try match lookup_name_of_rel n env with
	| Name id   -> id
	| Anonymous ->
	    anomaly "glob_constr_of_pattern: index to an anonymous variable"
      with Not_found -> id_of_string ("_UNBOUND_REL_"^(string_of_int n)) in
      GVar (loc,id)
  | PMeta None -> GHole (loc,Evar_kinds.InternalHole)
  | PMeta (Some n) -> GPatVar (loc,(false,n))
  | PApp (f,args) ->
      GApp (loc,glob_of_pat env f,Array.map_to_list (glob_of_pat env) args)
  | PSoApp (n,args) ->
      GApp (loc,GPatVar (loc,(true,n)),
        List.map (glob_of_pat env) args)
  | PProd (na,t,c) ->
      GProd (loc,na,Explicit,glob_of_pat env t,glob_of_pat (na::env) c)
  | PLetIn (na,t,c) ->
      GLetIn (loc,na,glob_of_pat env t, glob_of_pat (na::env) c)
  | PLambda (na,t,c) ->
      GLambda (loc,na,Explicit,glob_of_pat env t, glob_of_pat (na::env) c)
  | PIf (c,b1,b2) ->
      GIf (loc, glob_of_pat env c, (Anonymous,None),
           glob_of_pat env b1, glob_of_pat env b2)
  | PCase ({cip_style=LetStyle; cip_ind_args=None},PMeta None,tm,[(0,n,b)]) ->
      let nal,b = it_destRLambda_or_LetIn_names n (glob_of_pat env b) in
      GLetTuple (loc,nal,(Anonymous,None),glob_of_pat env tm,b)
  | PCase (info,p,tm,bl) ->
      let mat = match bl, info.cip_ind with
	| [], _ -> []
	| _, Some ind ->
	  let bl' = List.map (fun (i,n,c) -> (i,n,glob_of_pat env c)) bl in
	  simple_cases_matrix_of_branches ind bl'
	| _, None -> anomaly "PCase with some branches but unknown inductive"
      in
      let mat = if info.cip_extensible then mat @ [any_any_branch] else mat
      in
      let indnames,rtn = match p, info.cip_ind, info.cip_ind_args with
	| PMeta None, _, _ -> (Anonymous,None),None
	| _, Some ind, Some nargs ->
	  return_type_of_predicate ind nargs (glob_of_pat env p)
	| _ -> anomaly "PCase with non-trivial predicate but unknown inductive"
      in
      GCases (loc,RegularStyle,rtn,[glob_of_pat env tm,indnames],mat)
  | PFix f -> Detyping.detype false [] env (mkFix f)
  | PCoFix c -> Detyping.detype false [] env (mkCoFix c)
  | PSort s -> GSort (loc,s)

let extern_constr_pattern env pat =
  extern true (None,[]) Idset.empty (glob_of_pat env pat)

let extern_rel_context where env sign =
  let a = detype_rel_context where [] (names_of_rel_context env) sign in
  let vars = vars_of_env env in
  pi3 (extern_local_binder (None,[]) vars a)
