(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Pcoq
open Constr
open Prim
open Rawterm
open Term
open Names
open Libnames
open Topconstr

open Util

let constr_kw =
  [ "fun"; "match"; "fix"; "cofix"; "with"; "in"; "for"; "end"; "as";
    "let"; "if"; "then"; "else"; "struct"; "Prop"; "Set"; "Type" ]
let _ = List.iter (fun s -> Lexer.add_token("",s)) constr_kw
let _ = Options.v7 := false

let pair loc =
  Qualid (loc, Libnames.qualid_of_string "Coq.Init.Datatypes.pair")

let mk_cast = function
    (c,(_,None)) -> c
  | (c,(_,Some ty)) -> CCast(join_loc (constr_loc c) (constr_loc ty), c, ty)

let mk_lam = function
    ([],c) -> c
  | (bl,c) -> CLambdaN(constr_loc c, bl,c)

let coerce_to_id c =
  match c with
      CRef(Ident(loc,id)) -> (loc,Name id)
    | CHole loc -> (loc,Anonymous)
    | _ -> error "ill-formed match type annotation"

let match_bind_of_pat loc (oid,ty) =
  let l2 =
    match oid with
        None -> []
      | Some x -> [([x],CHole loc)] in
  let l1 =
    match ty with
        None -> [] (* No: should lookup inductive arity! *)
      | Some (CApp(_,_,args)) -> (* parameters do not appear *)
          List.map (fun (c,_) -> ([coerce_to_id c],CHole loc)) args
      | _ -> error "ill-formed match type annotation" in
  l1@l2

let mk_match (loc,cil,rty,br) =
  let (lc,pargs) = List.split cil in
  let pr =
    match rty with
        None -> None
      | Some ty ->
          let idargs = (* TODO: not forget the list lengths for PP! *)
            List.flatten (List.map (match_bind_of_pat loc) pargs) in
          Some (CLambdaN(loc,idargs,ty)) in
  CCases(loc,pr,lc,br)

let mk_fixb (loc,id,bl,ann,body,(tloc,tyc)) =
  let n =
    match bl,ann with
        [([_],_)], None -> 0
      | _, Some x ->
          let ids = List.map snd (List.flatten (List.map fst bl)) in
          (try list_index (snd x) ids - 1
          with Not_found -> error "no such fix variable")
      | _ -> error "cannot find decreasing arg of fix" in
  let ty = match tyc with
      None -> CHole tloc
    | Some t -> CProdN(loc,bl,t) in
  (snd id,n,ty,CLambdaN(loc,bl,body))

let mk_cofixb (loc,id,bl,ann,body,(tloc,tyc)) =
  let _ = option_app (fun (aloc,_) ->
    Util.user_err_loc
      (aloc,"Constr:mk_cofixb",
       Pp.str"Annotation forbidden in cofix expression")) ann in
  let ty = match tyc with
      None -> CHole tloc
    | Some t -> CProdN(loc,bl,t) in
  (snd id,ty,CLambdaN(loc,bl,body))

let mk_fix(loc,kw,id,dcls) =
  if kw then 
    let fb = List.map mk_fixb dcls in
    CFix(loc,id,fb)
  else
    let fb = List.map mk_cofixb dcls in
    CCoFix(loc,id,fb)

let binder_constr =
  create_constr_entry (get_univ "constr") "binder_constr"

GEXTEND Gram
  GLOBAL: binder_constr lconstr constr operconstr sort global
  constr_pattern Constr.ident;
  Constr.ident:
    [ [ id = Prim.ident -> id

      (* This is used in quotations and Syntax *)
      | id = METAIDENT -> id_of_string id ] ]
  ;
  global:
    [ [ r = Prim.reference -> r

      (* This is used in quotations *)
      | id = METAIDENT -> Ident (loc,id_of_string id) ] ]
  ;
  constr_pattern:
    [ [ c = constr -> c ] ]
  ;
  sort:
    [ [ "Set"  -> RProp Pos
      | "Prop" -> RProp Null
      | "Type" -> RType None ] ]
  ;
  lconstr:
    [ [ c = operconstr -> c ] ]
  ;
  constr:
    [ [ c = operconstr LEVEL "9" -> c ] ]
  ;
  operconstr:
    [ "200" RIGHTA
      [ c = binder_constr -> c ]
    | "100" RIGHTA
      [ c1 = operconstr; ":"; c2 = binder_constr -> CCast(loc,c1,c2)
      | c1 = operconstr; ":"; c2 = operconstr    -> CCast(loc,c1,c2) ]
    | "80" RIGHTA
      [ c1 = operconstr; "->"; c2 = binder_constr -> CArrow(loc,c1,c2)
      | c1 = operconstr; "->"; c2 = operconstr    -> CArrow(loc,c1,c2) ]
    | "40L" LEFTA
      [ "-"; c = operconstr -> CNotation(loc,"- _",[c]) ]
    | "10L" LEFTA
      [ f=operconstr; args=LIST1 appl_arg -> CApp(loc,f,args)
      | "@"; f=global; args=LIST0 NEXT -> CAppExpl(loc,f,args) ]
    | "9" [ ]
    | "1L" LEFTA
      [ c=operconstr; "%"; key=IDENT -> CDelimiters (loc,key,c) ]
    | "0"
      [ c=atomic_constr -> c
      | c=match_constr -> c
      | "("; c=operconstr; ")" -> c ] ]
  ;
  binder_constr:
    [ [ "!"; bl = LIST1 binder; "."; c = operconstr LEVEL "200" ->
          CProdN(loc,bl,c)
      | "fun"; bl = LIST1 binder; ty = type_cstr; "=>";
        c = operconstr LEVEL "200" ->
          CLambdaN(loc,bl,mk_cast(c,ty))
      | "let"; id=name; bl = LIST0 binder; ty = type_cstr; ":=";
        c1 = operconstr; "in"; c2 = operconstr LEVEL "200" ->
          CLetIn(loc,id,mk_lam(bl,mk_cast(c1,ty)),c2)
      | "let"; "("; lb = LIST1 name SEP ","; ")"; ":=";
        c1 = operconstr; "in"; c2 = operconstr LEVEL "200" ->
          COrderedCase (loc, LetStyle, None, c1,
                        [CLambdaN (loc, [lb, CHole loc], c2)])
      | "if"; c1=operconstr; "then"; c2=operconstr LEVEL "200";
        "else"; c3=operconstr LEVEL "200" ->
          COrderedCase (loc, IfStyle, None, c1, [c2; c3])
      | c=fix_constr -> c ] ]
  ;
  appl_arg:
    [ [ "@"; n=INT; ":="; c=operconstr LEVEL "9" -> (c,Some(int_of_string n))
      | c=operconstr LEVEL "9" -> (c,None) ] ]
  ;
  atomic_constr:
    [ [ g=global -> CRef g
      | s=sort -> CSort(loc,s)
      | n=INT -> CNumeral (loc,Bignat.POS (Bignat.of_string n))
      | IDENT "_" -> CHole loc
      | "?"; n=Prim.natural -> CMeta(loc,n) ] ]
  ;
  fix_constr:
    [ [ kw=fix_kw; dcl=fix_decl ->
          let (_,n,_,_,_,_) = dcl in mk_fix(loc,kw,n,[dcl])
      | kw=fix_kw; dcl1=fix_decl; "with"; dcls=LIST1 fix_decl SEP "with";
        "for"; id=identref ->
          mk_fix(loc,kw,id,dcl1::dcls)
    ] ]
    ;
  fix_kw:
    [ [ "fix" -> true
      | "cofix" -> false ] ]
  ;
  fix_decl:
    [ [ id=identref; bl=LIST0 binder; ann=fixannot; ty=type_cstr; ":=";
        c=operconstr LEVEL "200" -> (loc,id,bl,ann,c,ty) ] ]
  ;
  fixannot:
    [ [ "{"; "struct"; id=name; "}" -> Some id
      | -> None ] ]
  ;
  match_constr:
    [ [ "match"; ci=LIST1 case_item SEP ","; ty=case_type; "with";
        br=branches; "end" -> mk_match (loc,ci,ty,br) ] ]
  ;
  case_item:
    [ [ c=operconstr LEVEL "80"; p=pred_pattern -> (c,p) ] ]
  ;
  pred_pattern:
    [ [ oid = OPT ["as"; id=name -> id];
        (_,ty) = type_cstr -> (oid,ty) ] ]
  ;
  case_type:
    [ [ ty = OPT [ "=>"; c = lconstr -> c ] -> ty ] ]
  ;
  branches:
    [ [ OPT"|"; br=LIST0 eqn SEP "|" -> br ] ]
  ;
  eqn:
    [ [ pl = LIST1 pattern SEP ","; "=>"; rhs = lconstr -> (loc,pl,rhs) ] ]
  ;
  simple_pattern:
    [ [ r = Prim.reference -> CPatAtom (loc,Some r)
      | IDENT "_" -> CPatAtom (loc,None)
      | "("; p = lpattern; ")" -> p
      | n = bigint -> CPatNumeral (loc,n)
    ] ]
  ;
  pattern:
    [ [ p = pattern ; lp = LIST1 simple_pattern ->
        (match p with
          | CPatAtom (_, Some r) -> CPatCstr (loc, r, lp)
          | _ -> Util.user_err_loc 
              (loc, "compound_pattern", Pp.str "Constructor expected"))
      | p = pattern; "as"; id = base_ident ->
	  CPatAlias (loc, p, id)
      | c = pattern; "%"; key=IDENT -> 
          CPatDelimiters (loc,key,c)
      | p = simple_pattern -> p ] ]
  ;
  lpattern:
    [ [ c = pattern -> c
      | p1=pattern; ","; p2=lpattern ->  CPatCstr (loc, pair loc, [p1;p2]) ] ]
  ;
  binder:
    [ [ id=name -> ([id],CHole loc)
      | "("; id=name; ")" -> ([id],CHole loc)
      | "("; id=name; ":"; c=lconstr; ")" -> ([id],c)
      | id=name; ":"; c=constr -> ([id],c) ] ] (* tolerance *)
  ;
  type_cstr:
    [ [ c=OPT [":"; c=lconstr -> c] -> (loc,c) ] ]
  ;
END;;
