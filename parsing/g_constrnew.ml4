(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

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
  [ "forall"; "fun"; "match"; "fix"; "cofix"; "with"; "in"; "for"; 
    "end"; "as"; "let"; "if"; "then"; "else"; "return";
    "Prop"; "Set"; "Type"; ".("; "_"; ".." ]

let _ = 
  if not !Options.v7 then
    List.iter (fun s -> Lexer.add_token("",s)) constr_kw

(* For Correctness syntax; doesn't work if in psyntax (freeze pb?)  *)
let _ = Lexer.add_token ("","!")

let mk_cast = function
    (c,(_,None)) -> c
  | (c,(_,Some ty)) -> CCast(join_loc (constr_loc c) (constr_loc ty), c, ty)

let mk_lam = function
    ([],c) -> c
  | (bl,c) -> CLambdaN(constr_loc c, bl,c)

let mk_match (loc,cil,rty,br) =
  CCases(loc,(None,rty),cil,br)

let loc_of_binder_let = function
  | LocalRawAssum ((loc,_)::_,_)::_ -> loc
  | LocalRawDef ((loc,_),_)::_ -> loc
  | _ -> dummy_loc

let rec mkCProdN loc bll c =
  match bll with
  | LocalRawAssum ((loc1,_)::_ as idl,t) :: bll -> 
      CProdN (loc,[idl,t],mkCProdN (join_loc loc1 loc) bll c)
  | LocalRawDef ((loc1,_) as id,b) :: bll -> 
      CLetIn (loc,id,b,mkCProdN (join_loc loc1 loc) bll c)
  | [] -> c
  | LocalRawAssum ([],_) :: bll -> mkCProdN loc bll c

let rec mkCLambdaN loc bll c =
  match bll with
  | LocalRawAssum ((loc1,_)::_ as idl,t) :: bll -> 
      CLambdaN (loc,[idl,t],mkCLambdaN (join_loc loc1 loc) bll c)
  | LocalRawDef ((loc1,_) as id,b) :: bll -> 
      CLetIn (loc,id,b,mkCLambdaN (join_loc loc1 loc) bll c)
  | [] -> c
  | LocalRawAssum ([],_) :: bll -> mkCLambdaN loc bll c

let rec index_of_annot loc bl ann =
  match names_of_local_assums bl,ann with
    | [_], None -> 0
    | lids, Some x ->
        let ids = List.map snd lids in
        (try list_index (snd x) ids - 1
        with Not_found ->
          user_err_loc(fst x,"index_of_annot", Pp.str"no such fix variable"))
    | _ -> user_err_loc(loc,"index_of_annot",
      Pp.str "cannot guess decreasing argument of fix")

let mk_fixb (id,bl,ann,body,(loc,tyc)) =
  let n = index_of_annot (fst id) bl ann in
  let ty = match tyc with
      Some ty -> ty
    | None -> CHole loc in
  (snd id,n,bl,ty,body)

let mk_cofixb (id,bl,ann,body,(loc,tyc)) =
  let _ = option_app (fun (aloc,_) ->
    Util.user_err_loc
      (aloc,"Constr:mk_cofixb",
       Pp.str"Annotation forbidden in cofix expression")) ann in
  let ty = match tyc with
      Some ty -> ty
    | None -> CHole loc in
  (snd id,bl,ty,body)

let mk_fix(loc,kw,id,dcls) =
  if kw then 
    let fb = List.map mk_fixb dcls in
    CFix(loc,id,fb)
  else
    let fb = List.map mk_cofixb dcls in
    CCoFix(loc,id,fb)

let mk_single_fix (loc,kw,dcl) =
  let (id,_,_,_,_) = dcl in mk_fix(loc,kw,id,[dcl])

let binder_constr =
  create_constr_entry (get_univ "constr") "binder_constr"

(* Hack to parse "(x:=t)" as an explicit argument without conflicts with the *)
(* admissible notation "(x t)" *)
let lpar_id_coloneq =
  Gram.Entry.of_parser "test_lpar_id_coloneq"
    (fun strm ->
      match Stream.npeek 1 strm with
        | [("","(")] ->
            (match Stream.npeek 2 strm with
	      | [_; ("IDENT",s)] ->
                  (match Stream.npeek 3 strm with
                    | [_; _; ("", ":=")] ->
                        Stream.junk strm; Stream.junk strm; Stream.junk strm;
                        Names.id_of_string s
	            | _ -> raise Stream.Failure)
              | _ -> raise Stream.Failure)
        | _ -> raise Stream.Failure)


if not !Options.v7 then
GEXTEND Gram
  GLOBAL: binder_constr lconstr constr operconstr sort global
  constr_pattern lconstr_pattern Constr.ident binder binder_let pattern;
  Constr.ident:
    [ [ id = Prim.ident -> id

      (* This is used in quotations and Syntax *)
      | id = METAIDENT -> id_of_string id ] ]
  ;
  Prim.name:
    [ [ "_" -> (loc, Anonymous) ] ]
  ;
  Prim.ast:
    [ [ "_" -> Coqast.Nvar(loc,id_of_string"_") ] ]
  ;
  global:
    [ [ r = Prim.reference -> r

      (* This is used in quotations *)
      | id = METAIDENT -> Ident (loc,id_of_string id) ] ]
  ;
  constr_pattern:
    [ [ c = constr -> c ] ]
  ;
  lconstr_pattern:
    [ [ c = lconstr -> c ] ]
  ;
  sort:
    [ [ "Set"  -> RProp Pos
      | "Prop" -> RProp Null
      | "Type" -> RType None ] ]
  ;
  lconstr:
    [ [ c = operconstr LEVEL "200" -> c ] ]
  ;
  constr:
    [ [ c = operconstr LEVEL "9" -> c ] ]
  ;
  operconstr:
    [ "200" RIGHTA
      [ c = binder_constr -> c ]
    | "100" RIGHTA
      [ c1 = operconstr; ":"; c2 = binder_constr -> CCast(loc,c1,c2)
      | c1 = operconstr; ":"; c2 = SELF -> CCast(loc,c1,c2) ]
    | "99" RIGHTA [ ]
    | "90" RIGHTA
      [ c1 = operconstr; "->"; c2 = binder_constr -> CArrow(loc,c1,c2)
      | c1 = operconstr; "->"; c2 = SELF -> CArrow(loc,c1,c2)]
    | "10" LEFTA
      [ f=operconstr; args=LIST1 appl_arg -> CApp(loc,(None,f),args)
      | "@"; f=global; args=LIST0 NEXT -> CAppExpl(loc,(None,f),args) ]
    | "9"
        [ ".."; c = operconstr LEVEL "0"; ".." ->
          CAppExpl (loc,(None,Ident (loc,Topconstr.ldots_var)),[c]) ]
    | "1" LEFTA
      [ c=operconstr; ".("; f=global; args=LIST0 appl_arg; ")" ->
	CApp(loc,(Some (List.length args+1),CRef f),args@[c,None])
      | c=operconstr; ".("; "@"; f=global;
        args=LIST0 (operconstr LEVEL "9"); ")" ->
        CAppExpl(loc,(Some (List.length args+1),f),args@[c]) 
      | c=operconstr; "%"; key=IDENT -> CDelimiters (loc,key,c) ]
    | "0"
      [ c=atomic_constr -> c
      | c=match_constr -> c
      | "("; c = operconstr LEVEL "200"; ")" ->
          (match c with
              CNumeral(_,Bignat.POS _) -> CNotation(loc,"( _ )",[c])
            | _ -> c) ] ]
  ;
  binder_constr:
    [ [ "forall"; bl = binder_list; ","; c = operconstr LEVEL "200" ->
          mkCProdN loc bl c
      | "fun"; bl = binder_list; "=>"; c = operconstr LEVEL "200" ->
          mkCLambdaN loc bl c
      | "let"; id=name; bl = LIST0 binder_let; ty = type_cstr; ":=";
        c1 = operconstr LEVEL "200"; "in"; c2 = operconstr LEVEL "200" ->
          let loc1 = loc_of_binder_let bl in
          CLetIn(loc,id,mkCLambdaN loc1 bl (mk_cast(c1,ty)),c2)
      | "let"; fx = single_fix; "in"; c = operconstr LEVEL "200" ->
          let fixp = mk_single_fix fx in
          let (li,id) = match fixp with
              CFix(_,id,_) -> id
            | CCoFix(_,id,_) -> id
            | _ -> assert false in
          CLetIn(loc,(li,Name id),fixp,c)
      | "let"; lb = ["("; l=LIST0 name SEP ","; ")" -> l | "()" -> []];
	  po = return_type;
	  ":="; c1 = operconstr LEVEL "200"; "in";
          c2 = operconstr LEVEL "200" ->
          CLetTuple (loc,List.map snd lb,po,c1,c2)
      | "if"; c=operconstr LEVEL "200"; po = return_type;
	"then"; b1=operconstr LEVEL "200";
        "else"; b2=operconstr LEVEL "200" ->
          CIf (loc, c, po, b1, b2)
      | c=fix_constr -> c ] ]
  ;
  appl_arg:
    [ [ id = lpar_id_coloneq; c=lconstr; ")" ->
	  (c,Some (loc,ExplByName id))
      | c=constr -> (c,None) ] ]
  ;
  atomic_constr:
    [ [ g=global -> CRef g
      | s=sort -> CSort(loc,s)
      | n=INT -> CNumeral (loc,Bignat.POS (Bignat.of_string n))
      | "_" -> CHole loc
      | "?"; id=ident -> CPatVar(loc,(false,id)) ] ]
  ;
  fix_constr:
    [ [ fx1=single_fix -> mk_single_fix fx1
      | (_,kw,dcl1)=single_fix; "with"; dcls=LIST1 fix_decl SEP "with";
        "for"; id=identref ->
          mk_fix(loc,kw,id,dcl1::dcls)
    ] ]
  ;
  single_fix:
    [ [ kw=fix_kw; dcl=fix_decl -> (loc,kw,dcl) ] ]
  ;
  fix_kw:
    [ [ "fix" -> true
      | "cofix" -> false ] ]
  ;
  fix_decl:
    [ [ id=identref; bl=LIST0 binder_let; ann=fixannot; ty=type_cstr; ":=";
        c=operconstr LEVEL "200" -> (id,bl,ann,c,ty) ] ]
  ;
  fixannot:
    [ [ "{"; IDENT "struct"; id=name; "}" -> Some id
      | -> None ] ]
  ;
  match_constr:
    [ [ "match"; ci=LIST1 case_item SEP ","; ty=OPT case_type; "with";
        br=branches; "end" -> mk_match (loc,ci,ty,br) ] ]
  ;
  case_item:
    [ [ c=operconstr LEVEL "100"; p=pred_pattern -> (c,p) ] ]
  ;
  pred_pattern:
    [ [ ona = OPT ["as"; id=name -> snd id];
        ty = OPT ["in"; t=lconstr -> t] -> (ona,ty) ] ]
  ;
  case_type:
    [ [ "return"; ty = operconstr LEVEL "100" -> ty ] ]
  ;
  return_type:
    [ [ a = OPT [ na = OPT["as"; id=name -> snd id];
                  ty = case_type -> (na,ty) ] -> 
        match a with 
          | None -> None, None
          | Some (na,t) -> (na, Some t)
    ] ]
  ;
  branches:
    [ [ OPT"|"; br=LIST0 eqn SEP "|" -> br ] ]
  ;
  eqn:
    [ [ pl = LIST1 pattern SEP ","; "=>"; rhs = lconstr -> (loc,pl,rhs) ] ]
  ;
  pattern:
    [ "200" RIGHTA [ ]
    | "10" LEFTA
      [ p = pattern ; lp = LIST1 (pattern LEVEL "0") ->
        (match p with
          | CPatAtom (_, Some r) -> CPatCstr (loc, r, lp)
          | _ -> Util.user_err_loc 
              (cases_pattern_loc p, "compound_pattern",
               Pp.str "Constructor expected"))
      | p = pattern; "as"; id = base_ident ->
	  CPatAlias (loc, p, id)
      | c = pattern; "%"; key=IDENT -> 
          CPatDelimiters (loc,key,c) ]
    | "0"
      [ r = Prim.reference -> CPatAtom (loc,Some r)
      | "_" -> CPatAtom (loc,None)
      | "("; p = pattern LEVEL "200"; ")" ->
          (match p with
              CPatNumeral(_,Bignat.POS _) -> CPatNotation(loc,"( _ )",[p])
            | _ -> p)
      | n = INT -> CPatNumeral (loc,Bignat.POS(Bignat.of_string n)) ] ]
  ;
  binder_list:
    [ [ idl=LIST1 name; bl=LIST0 binder_let -> 
          LocalRawAssum (idl,CHole loc)::bl
      | idl=LIST1 name; ":"; c=lconstr -> 
          [LocalRawAssum (idl,c)]
      | "("; idl=LIST1 name; ":"; c=lconstr; ")"; bl=LIST0 binder_let ->
          LocalRawAssum (idl,c)::bl ] ]
  ;
  binder_let:
    [ [ id=name ->
          LocalRawAssum ([id],CHole loc)
      | "("; id=name; idl=LIST1 name; ":"; c=lconstr; ")" -> 
          LocalRawAssum (id::idl,c)
      | "("; id=name; ":"; c=lconstr; ")" -> 
          LocalRawAssum ([id],c)
      | "("; id=name; ":="; c=lconstr; ")" ->
          LocalRawDef (id,c)
      | "("; id=name; ":"; t=lconstr; ":="; c=lconstr; ")" -> 
          LocalRawDef (id,CCast (join_loc (constr_loc t) loc,c,t))
    ] ]
  ;
  binder:
    [ [ id=name -> ([id],CHole loc)
      | "("; idl=LIST1 name; ":"; c=lconstr; ")" -> (idl,c) ] ]
  ;
  type_cstr:
    [ [ c=OPT [":"; c=lconstr -> c] -> (loc,c) ] ]
  ;
  END;;
