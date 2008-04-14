(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4use: "pa_extend.cmo" i*)

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
    "end"; "as"; "let"; "dest"; "if"; "then"; "else"; "return";
    "Prop"; "Set"; "Type"; ".("; "_"; ".." ]

let _ = List.iter (fun s -> Lexer.add_token("",s)) constr_kw

let mk_cast = function
    (c,(_,None)) -> c
  | (c,(_,Some ty)) -> CCast(join_loc (constr_loc c) (constr_loc ty), c, CastConv (DEFAULTcast, ty))

let mk_lam = function
    ([],c) -> c
  | (bl,c) -> CLambdaN(constr_loc c, bl,c)

let loc_of_binder_let = function
  | LocalRawAssum ((loc,_)::_,_,_)::_ -> loc
  | LocalRawDef ((loc,_),_)::_ -> loc
  | _ -> dummy_loc

let rec index_and_rec_order_of_annot loc bl ann =
  match names_of_local_assums bl,ann with
    | [_], (None, r) -> Some 0, r
    | lids, (Some x, ro) ->
        let ids = List.map snd lids in
        (try Some (list_index0 (snd x) ids), ro
        with Not_found ->
          user_err_loc(fst x,"index_of_annot", Pp.str"no such fix variable"))
    | _, (None, r) -> None, r

let mk_fixb (id,bl,ann,body,(loc,tyc)) =
  let n,ro = index_and_rec_order_of_annot (fst id) bl ann in
  let ty = match tyc with
      Some ty -> ty
    | None -> CHole (loc, None) in
  (snd id,(n,ro),bl,ty,body)

let mk_cofixb (id,bl,ann,body,(loc,tyc)) =
  let _ = Option.map (fun (aloc,_) ->
    Util.user_err_loc
      (aloc,"Constr:mk_cofixb",
       Pp.str"Annotation forbidden in cofix expression")) (fst ann) in
  let ty = match tyc with
      Some ty -> ty
    | None -> CHole (loc, None) in
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

let impl_ident =
  Gram.Entry.of_parser "impl_ident"
    (fun strm ->
      match Stream.npeek 1 strm with
	| [(_,"{")] -> 
	    (match Stream.npeek 2 strm with
	      | [_;("IDENT",("wf"|"struct"|"measure"))] ->
		  raise Stream.Failure
	      | [_;("IDENT",s)] -> 
		  Stream.junk strm; Stream.junk strm;
		  Names.id_of_string s
	      | _ -> raise Stream.Failure)
	| _ -> raise Stream.Failure)
    
let ident_eq =
  Gram.Entry.of_parser "ident_eq"
    (fun strm ->
      match Stream.npeek 1 strm with
	| [("IDENT",s)] ->
            (match Stream.npeek 2 strm with
              | [_; ("", ":")] ->
                  Stream.junk strm; Stream.junk strm;
                  Names.id_of_string s
              | _ -> raise Stream.Failure)
        | _ -> raise Stream.Failure)

let aliasvar = function CPatAlias (_, _, id) -> Some (Name id) | _ -> None

GEXTEND Gram
  GLOBAL: binder_constr lconstr constr operconstr sort global
  constr_pattern lconstr_pattern Constr.ident
  binder binder_let binders_let delimited_binder_let delimited_binders_let
  binders_let_fixannot typeclass_constraint pattern;
  Constr.ident:
    [ [ id = Prim.ident -> id

      (* This is used in quotations and Syntax *)
      | id = METAIDENT -> id_of_string id ] ]
  ;
  Prim.name:
    [ [ "_" -> (loc, Anonymous) ] ]
  ;
  global:
    [ [ r = Prim.reference -> r ] ]
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
    [ [ c = operconstr LEVEL "8" -> c 
      | "@"; f=global -> CAppExpl(loc,(None,f),[]) ] ]
  ;
  operconstr:
    [ "200" RIGHTA
      [ c = binder_constr -> c ]
    | "100" RIGHTA
      [ c1 = operconstr; "<:"; c2 = binder_constr -> 
                 CCast(loc,c1, CastConv (VMcast,c2))
      | c1 = operconstr; "<:"; c2 = SELF -> 
                 CCast(loc,c1, CastConv (VMcast,c2))
      | c1 = operconstr; ":";c2 = binder_constr -> 
                 CCast(loc,c1, CastConv (DEFAULTcast,c2))
      | c1 = operconstr; ":"; c2 = SELF -> 
                 CCast(loc,c1, CastConv (DEFAULTcast,c2)) 
      | c1 = operconstr; ":>" ->
                 CCast(loc,c1, CastCoerce) ]
    | "99" RIGHTA [ ]
    | "90" RIGHTA
      [ c1 = operconstr; "->"; c2 = binder_constr -> CArrow(loc,c1,c2)
      | c1 = operconstr; "->"; c2 = SELF -> CArrow(loc,c1,c2)]
    | "10" LEFTA
      [ f=operconstr; args=LIST1 appl_arg -> CApp(loc,(None,f),args)
      | "@"; f=global; args=LIST0 NEXT -> CAppExpl(loc,(None,f),args)
      | "@"; (locid,id) = pattern_identref; args=LIST1 identref ->
          let args = List.map (fun x -> CRef (Ident x), None) args in
          CApp(loc,(None,CPatVar(locid,(true,id))),args) ]
    | "9"
        [ ".."; c = operconstr LEVEL "0"; ".." ->
          CAppExpl (loc,(None,Ident (loc,Topconstr.ldots_var)),[c]) ]
    | "8" LEFTA [ ]
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
              CPrim (_,Numeral z) when Bigint.is_pos_or_zero z ->
                CNotation(loc,"( _ )",[c])
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
      | "let"; "'"; p=pattern; ":="; c1 = operconstr LEVEL "200";
          "in"; c2 = operconstr LEVEL "200" ->
	    CCases (loc, LetPatternStyle, None, [(c1,(None,None))], [(loc, [(loc,[p])], c2)])
      | "let"; "'"; p=pattern; ":="; c1 = operconstr LEVEL "200"; 
	  rt = case_type; "in"; c2 = operconstr LEVEL "200" ->
	    CCases (loc, LetPatternStyle, Some rt, [(c1, (aliasvar p, None))], [(loc, [(loc, [p])], c2)])
      | "let"; "'"; p=pattern; "in"; t = operconstr LEVEL "200"; 
	  ":="; c1 = operconstr LEVEL "200"; rt = case_type;
          "in"; c2 = operconstr LEVEL "200" ->
	    CCases (loc, LetPatternStyle, Some rt, [(c1, (aliasvar p, Some t))], [(loc, [(loc, [p])], c2)])
      | "if"; c=operconstr LEVEL "200"; po = return_type;
	"then"; b1=operconstr LEVEL "200";
        "else"; b2=operconstr LEVEL "200" ->
          CIf (loc, c, po, b1, b2)
      | c=fix_constr -> c ] ]
  ;
  appl_arg:
    [ [ id = lpar_id_coloneq; c=lconstr; ")" ->
	  (c,Some (loc,ExplByName id))
      | c=operconstr LEVEL "9" -> (c,None) ] ]
  ;
  atomic_constr:
    [ [ g=global -> CRef g
      | s=sort -> CSort (loc,s)
      | n=INT -> CPrim (loc, Numeral (Bigint.of_string n))
      | s=string -> CPrim (loc, String s)
      | "_" -> CHole (loc, None)
      | id=pattern_ident -> CPatVar(loc,(false,id)) ] ]
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
    [ [ id=identref; bl=binders_let_fixannot; ty=type_cstr; ":=";
        c=operconstr LEVEL "200" -> (id,fst bl,snd bl,c,ty) ] ]
  ;
(*   fixannot: *)
(*     [ [ "{"; IDENT "struct"; id=name; "}" -> (Some id, CStructRec) *)
(*       | "{"; IDENT "wf"; rel=constr; id=OPT name; "}" -> (id, CWfRec rel) *)
(*       | "{"; IDENT "measure"; rel=constr; id=OPT name; "}" -> (id, CMeasureRec rel) *)
(*       | ->  (None, CStructRec) *)
(*       ] ] *)
(*   ; *)
  match_constr:
    [ [ "match"; ci=LIST1 case_item SEP ","; ty=OPT case_type; "with";
        br=branches; "end" -> CCases(loc,RegularStyle,ty,ci,br) ] ]
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
  mult_pattern:
    [ [ pl = LIST1 pattern LEVEL "99" SEP "," -> (loc,pl) ] ]
  ;
  eqn:
    [ [ pll = LIST1 mult_pattern SEP "|";
        "=>"; rhs = lconstr -> (loc,pll,rhs) ] ]
  ;
  pattern:
    [ "200" RIGHTA [ ]
    | "100" RIGHTA
      [ p = pattern; "|"; pl = LIST1 pattern SEP "|" -> CPatOr (loc,p::pl) ]
    | "99" RIGHTA [ ]
    | "10" LEFTA
      [ p = pattern; lp = LIST1 NEXT ->
        (match p with
          | CPatAtom (_, Some r) -> CPatCstr (loc, r, lp)
          | _ -> Util.user_err_loc 
              (cases_pattern_expr_loc p, "compound_pattern",
               Pp.str "Constructor expected"))
      | p = pattern; "as"; id = ident ->
	  CPatAlias (loc, p, id) ]
    | "1" LEFTA
      [ c = pattern; "%"; key=IDENT -> CPatDelimiters (loc,key,c) ]
    | "0"
      [ r = Prim.reference -> CPatAtom (loc,Some r)
      | "_" -> CPatAtom (loc,None)
      | "("; p = pattern LEVEL "200"; ")" ->
          (match p with
              CPatPrim (_,Numeral z) when Bigint.is_pos_or_zero z ->
                CPatNotation(loc,"( _ )",[p])
            | _ -> p)
      | n = INT -> CPatPrim (loc, Numeral (Bigint.of_string n))
      | s = string -> CPatPrim (loc, String s) ] ]
  ;
  binder_list:
    [ [ idl=LIST1 name; bl=LIST0 binder_let -> 
          LocalRawAssum (idl,Default Explicit,CHole (loc, Some (Evd.BinderType (snd (List.hd idl)))))::bl
      | idl=LIST1 name; ":"; c=lconstr -> 
          [LocalRawAssum (idl,Default Explicit,c)]
      | cl = binders_let -> cl
    ] ]
  ;
  delimited_binders_let: 
    [ [ "["; ctx = LIST1 typeclass_constraint_binder SEP ","; "]"; bl=binders_let -> 
	  ctx @ bl
    | b = delimited_binder_let; cl = LIST0 binder_let -> b :: cl
    | -> [] ] ]
  ;
  binders_let: 
    [ [ "["; ctx = LIST1 typeclass_constraint_binder SEP ","; "]"; bl=binders_let -> 
	  ctx @ bl
    | cl = LIST0 binder_let -> cl ] ]
  ;
  binder_assum:
    [ [ "}" -> fun id -> LocalRawAssum([id], Default Implicit, CHole(loc, None))
    | idl=LIST1 name; ":"; c=lconstr; "}" ->
        (fun id -> LocalRawAssum (id::idl,Default Implicit,c))
    | idl=LIST1 name; "}" ->
        (fun id -> LocalRawAssum (id::idl,Default Implicit,CHole (loc, None)))
    | ":"; c=lconstr; "}" ->
	(fun id -> LocalRawAssum ([id],Default Implicit,c))
    ] ]
  ;
  fixannot:
    [ [ "{"; IDENT "struct"; id=name; "}" -> (Some id, CStructRec)
    | "{"; IDENT "wf"; rel=constr; id=OPT name; "}" -> (id, CWfRec rel)
    | "{"; IDENT "measure"; rel=constr; id=OPT name; "}" -> (id, CMeasureRec rel)
    ] ]
  ;
  binders_let_fixannot:
    [ [ id=impl_ident; assum=binder_assum; bl = binders_let_fixannot -> 
	(assum (loc, Name id) :: fst bl), snd bl
    | f = fixannot -> [], f
    | b = binder_let; bl = binders_let_fixannot -> 
	b :: fst bl, snd bl
    | -> [], (None, CStructRec)
    ] ]
  ;

  binder_let:
    [ [ id=name ->
          LocalRawAssum ([id],Default Explicit,CHole (loc, None))
      | "("; id=name; idl=LIST1 name; ":"; c=lconstr; ")" ->
          LocalRawAssum (id::idl,Default Explicit,c)
      | "("; id=name; ":"; c=lconstr; ")" ->
          LocalRawAssum ([id],Default Explicit,c)
      | "{"; id=name; "}" ->
          LocalRawAssum ([id],Default Implicit,CHole (loc, None))
      | "{"; id=name; idl=LIST1 name; ":"; c=lconstr; "}" ->
          LocalRawAssum (id::idl,Default Implicit,c)
      | "{"; id=name; ":"; c=lconstr; "}" ->
          LocalRawAssum ([id],Default Implicit,c)
      | "{"; id=name; idl=LIST1 name; "}" ->
          LocalRawAssum (id::idl,Default Implicit,CHole (loc, None))
      | "("; id=name; ":="; c=lconstr; ")" ->
          LocalRawDef (id,c)
      | "("; id=name; ":"; t=lconstr; ":="; c=lconstr; ")" ->
          LocalRawDef (id,CCast (join_loc (constr_loc t) loc,c, CastConv (DEFAULTcast,t)))
      | "["; tc = typeclass_constraint_binder; "]" -> tc
    ] ]
  ;
  delimited_binder_let:
    [ [ "("; id=name; idl=LIST1 name; ":"; c=lconstr; ")" -> 
          LocalRawAssum (id::idl,Default Explicit,c)
      | "("; id=name; ":"; c=lconstr; ")" -> 
          LocalRawAssum ([id],Default Explicit,c)
      | "("; id=name; ":="; c=lconstr; ")" ->
          LocalRawDef (id,c)
      | "("; id=name; ":"; t=lconstr; ":="; c=lconstr; ")" -> 
          LocalRawDef (id,CCast (join_loc (constr_loc t) loc,c, CastConv (DEFAULTcast,t)))
      | "{"; id=name; "}" ->
          LocalRawAssum ([id],Default Implicit,CHole (loc, None))
      | "{"; id=name; idl=LIST1 name; ":"; c=lconstr; "}" -> 
          LocalRawAssum (id::idl,Default Implicit,c)
      | "{"; id=name; ":"; c=lconstr; "}" -> 
          LocalRawAssum ([id],Default Implicit,c)
      | "{"; id=name; idl=LIST1 name; "}" -> 
          LocalRawAssum (id::idl,Default Implicit,CHole (loc, None))
      | "["; tc = typeclass_constraint_binder; "]" -> tc
    ] ]
  ;
  binder:
    [ [ id=name -> ([id],Default Explicit,CHole (loc, None))
      | "("; idl=LIST1 name; ":"; c=lconstr; ")" -> (idl,Default Explicit,c) 
      | "{"; idl=LIST1 name; ":"; c=lconstr; "}" -> (idl,Default Implicit,c) 
    ] ]
  ;
  typeclass_constraint_binder:
    [ [ tc = typeclass_constraint ->
      let (n,bk,t) = tc in
	LocalRawAssum ([n], TypeClass bk, t)
    ] ]
  ;
  typeclass_constraint:
    [ [ "!" ; qid=global ; cl = LIST0 typeclass_param -> 
	(loc, Anonymous), Explicit, CApp (loc, (None, mkRefC qid), cl)
    | iid=ident_eq ; qid=typeclass_name ; cl = LIST0 typeclass_param -> 
	(loc, Name iid), (fst qid), CApp (loc, (None, mkRefC (snd qid)), cl)
    | qid=global ; cl = LIST0 typeclass_param -> 
	(loc, Anonymous), Implicit, CApp (loc, (None, mkRefC qid), cl)
    ] ]
  ;
  typeclass_name:
    [ [ id=global -> (Implicit, id)
    | "!"; id=global -> (Explicit, id)
    ] ]
  ;

  typeclass_param: 
    [ [ id = global -> CRef id, None
    | c = sort -> CSort (loc, c), None
    | id = lpar_id_coloneq; c=lconstr; ")" ->
	(c,Some (loc,ExplByName id))
    | c=operconstr LEVEL "9" -> c, None
    ] ]
  ;
  type_cstr:
    [ [ c=OPT [":"; c=lconstr -> c] -> (loc,c) ] ]
  ;
  END;;
