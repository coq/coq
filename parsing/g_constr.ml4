(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Pcoq
open Constr
open Prim
open Rawterm
open Term
open Names
open Libnames
open Topconstr
open Util
open Tok
open Compat

let constr_kw =
  [ "forall"; "fun"; "match"; "fix"; "cofix"; "with"; "in"; "for";
    "end"; "as"; "let"; "if"; "then"; "else"; "return";
    "Prop"; "Set"; "Type"; ".("; "_"; "..";
    "`{"; "`("; "{|"; "|}" ]

let _ = List.iter Lexer.add_keyword constr_kw

let mk_cast = function
    (c,(_,None)) -> c
  | (c,(_,Some ty)) -> CCast(join_loc (constr_loc c) (constr_loc ty), c, CastConv (DEFAULTcast, ty))

let binders_of_lidents l =
  List.map (fun (loc, id) ->
    LocalRawAssum ([loc, Name id], Default Rawterm.Explicit,
		  CHole (loc, Some (Evd.BinderType (Name id))))) l

let mk_fixb (id,bl,ann,body,(loc,tyc)) =
  let ty = match tyc with
      Some ty -> ty
    | None -> CHole (loc, None) in
  (id,ann,bl,ty,body)

let mk_cofixb (id,bl,ann,body,(loc,tyc)) =
  let _ = Option.map (fun (aloc,_) ->
    Util.user_err_loc
      (aloc,"Constr:mk_cofixb",
       Pp.str"Annotation forbidden in cofix expression.")) (fst ann) in
  let ty = match tyc with
      Some ty -> ty
    | None -> CHole (loc, None) in
  (id,bl,ty,body)

let mk_fix(loc,kw,id,dcls) =
  if kw then
    let fb = List.map mk_fixb dcls in
    CFix(loc,id,fb)
  else
    let fb = List.map mk_cofixb dcls in
    CCoFix(loc,id,fb)

let mk_single_fix (loc,kw,dcl) =
  let (id,_,_,_,_) = dcl in mk_fix(loc,kw,id,[dcl])

let err () = raise Stream.Failure

(* Hack to parse "(x:=t)" as an explicit argument without conflicts with the *)
(* admissible notation "(x t)" *)
let lpar_id_coloneq =
  Gram.Entry.of_parser "test_lpar_id_coloneq"
    (fun strm ->
      match get_tok (stream_nth 0 strm) with
        | KEYWORD "(" ->
            (match get_tok (stream_nth 1 strm) with
	      | IDENT s ->
                  (match get_tok (stream_nth 2 strm) with
                    | KEYWORD ":=" ->
                        stream_njunk 3 strm;
                        Names.id_of_string s
	            | _ -> err ())
              | _ -> err ())
        | _ -> err ())

let impl_ident_head =
  Gram.Entry.of_parser "impl_ident_head"
    (fun strm ->
      match get_tok (stream_nth 0 strm) with
	| KEYWORD "{" ->
	    (match get_tok (stream_nth 1 strm) with
	      | IDENT ("wf"|"struct"|"measure") -> err ()
	      | IDENT s ->
		  stream_njunk 2 strm;
		  Names.id_of_string s
	      | _ -> err ())
	| _ -> err ())

let ident_colon =
  Gram.Entry.of_parser "ident_colon"
    (fun strm ->
      match get_tok (stream_nth 0 strm) with
	| IDENT s ->
            (match get_tok (stream_nth 1 strm) with
              | KEYWORD ":" ->
                  stream_njunk 2 strm;
                  Names.id_of_string s
              | _ -> err ())
        | _ -> err ())

let aliasvar = function CPatAlias (loc, _, id) -> Some (loc,Name id) | _ -> None

GEXTEND Gram
  GLOBAL: binder_constr lconstr constr operconstr sort global
  constr_pattern lconstr_pattern Constr.ident
  closed_binder open_binders binder binders binders_fixannot
  record_declaration typeclass_constraint pattern appl_arg;
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
    | "8" [ ]
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
                CNotation(loc,"( _ )",([c],[],[]))
            | _ -> c)
      | "{|"; c = record_declaration; "|}" -> c
      | "`{"; c = operconstr LEVEL "200"; "}" ->
	  CGeneralization (loc, Implicit, None, c)
      | "`("; c = operconstr LEVEL "200"; ")" ->
	  CGeneralization (loc, Explicit, None, c)
      ] ]
  ;
  forall:
    [ [ "forall" -> () ] ]
  ;
  lambda:
    [ [ "fun" -> () ] ]
  ;
  record_declaration:
    [ [ fs = LIST1 record_field_declaration SEP ";" -> CRecord (loc, None, fs)
(*       | c = lconstr; "with"; fs = LIST1 record_field_declaration SEP ";" -> *)
(* 	  CRecord (loc, Some c, fs) *)
    ] ]
  ;
  record_field_declaration:
    [ [ id = global; params = LIST0 identref; ":="; c = lconstr ->
      (id, Topconstr.abstract_constr_expr c (binders_of_lidents params)) ] ]
  ;
  binder_constr:
    [ [ forall; bl = open_binders; ","; c = operconstr LEVEL "200" ->
          mkCProdN loc bl c
      | lambda; bl = open_binders; [ "=>" | "," ]; c = operconstr LEVEL "200" ->
          mkCLambdaN loc bl c
      | "let"; id=name; bl = binders; ty = type_cstr; ":=";
        c1 = operconstr LEVEL "200"; "in"; c2 = operconstr LEVEL "200" ->
          let loc1 = join_loc (local_binders_loc bl) (constr_loc c1) in
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
          CLetTuple (loc,lb,po,c1,c2)
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
    [ [ id=identref; bl=binders_fixannot; ty=type_cstr; ":=";
        c=operconstr LEVEL "200" ->
          (id,fst bl,snd bl,c,ty) ] ]
  ;
  match_constr:
    [ [ "match"; ci=LIST1 case_item SEP ","; ty=OPT case_type; "with";
        br=branches; "end" -> CCases(loc,RegularStyle,ty,ci,br) ] ]
  ;
  case_item:
    [ [ c=operconstr LEVEL "100"; p=pred_pattern -> (c,p) ] ]
  ;
  pred_pattern:
    [ [ ona = OPT ["as"; id=name -> id];
        ty = OPT ["in"; t=lconstr -> t] -> (ona,ty) ] ]
  ;
  case_type:
    [ [ "return"; ty = operconstr LEVEL "100" -> ty ] ]
  ;
  return_type:
    [ [ a = OPT [ na = OPT["as"; na=name -> na];
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
  recordpattern:
    [ [ id = global; ":="; pat = pattern -> (id, pat) ] ]
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
               Pp.str "Constructor expected."))
      | p = pattern; "as"; id = ident ->
	  CPatAlias (loc, p, id) ]
    | "1" LEFTA
      [ c = pattern; "%"; key=IDENT -> CPatDelimiters (loc,key,c) ]
    | "0"
      [ r = Prim.reference -> CPatAtom (loc,Some r)
      | "{|"; pat = LIST0 recordpattern SEP ";" ; "|}" -> CPatRecord (loc, pat)
      | "_" -> CPatAtom (loc,None)
      | "("; p = pattern LEVEL "200"; ")" ->
          (match p with
              CPatPrim (_,Numeral z) when Bigint.is_pos_or_zero z ->
                CPatNotation(loc,"( _ )",([p],[]))
            | _ -> p)
      | n = INT -> CPatPrim (loc, Numeral (Bigint.of_string n))
      | s = string -> CPatPrim (loc, String s) ] ]
  ;
  impl_ident_tail:
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
    [ [ "{"; IDENT "struct"; id=identref; "}" -> (Some id, CStructRec)
    | "{"; IDENT "wf"; rel=constr; id=OPT identref; "}" -> (id, CWfRec rel)
    | "{"; IDENT "measure"; m=constr; id=OPT identref;
	rel=OPT constr; "}" -> (id, CMeasureRec (m,rel))
    ] ]
  ;
  binders_fixannot:
    [ [ id = impl_ident_head; assum = impl_ident_tail; bl = binders_fixannot ->
          (assum (loc, Name id) :: fst bl), snd bl
      | f = fixannot -> [], f
      | b = binder; bl = binders_fixannot -> b @ fst bl, snd bl
      | -> [], (None, CStructRec)
    ] ]
  ;
  open_binders:
    (* Same as binders but parentheses around a closed binder are optional if
       the latter is unique *)
    [ [ (* open binder *)
        id = name; idl = LIST0 name; ":"; c = lconstr ->
          [LocalRawAssum (id::idl,Default Explicit,c)]
	(* binders factorized with open binder *)
      | id = name; idl = LIST0 name; bl = binders ->
          let t = CHole (loc, Some (Evd.BinderType (snd id))) in
          LocalRawAssum (id::idl,Default Explicit,t)::bl
      | id1 = name; ".."; id2 = name ->
          [LocalRawAssum ([id1;(loc,Name ldots_var);id2],
	                  Default Explicit,CHole (loc,None))]
      | bl = closed_binder; bl' = binders ->
	  bl@bl'
    ] ]
  ;
  binders:
    [ [ l = LIST0 binder -> List.flatten l ] ]
  ;
  binder:
    [ [ id = name -> [LocalRawAssum ([id],Default Explicit,CHole (loc, None))]
      | bl = closed_binder -> bl ] ]
  ;
  closed_binder:
    [ [ "("; id=name; idl=LIST1 name; ":"; c=lconstr; ")" ->
          [LocalRawAssum (id::idl,Default Explicit,c)]
      | "("; id=name; ":"; c=lconstr; ")" ->
          [LocalRawAssum ([id],Default Explicit,c)]
      | "("; id=name; ":="; c=lconstr; ")" ->
          [LocalRawDef (id,c)]
      | "("; id=name; ":"; t=lconstr; ":="; c=lconstr; ")" ->
          [LocalRawDef (id,CCast (join_loc (constr_loc t) loc,c, CastConv (DEFAULTcast,t)))]
      | "{"; id=name; "}" ->
          [LocalRawAssum ([id],Default Implicit,CHole (loc, None))]
      | "{"; id=name; idl=LIST1 name; ":"; c=lconstr; "}" ->
          [LocalRawAssum (id::idl,Default Implicit,c)]
      | "{"; id=name; ":"; c=lconstr; "}" ->
          [LocalRawAssum ([id],Default Implicit,c)]
      | "{"; id=name; idl=LIST1 name; "}" ->
          List.map (fun id -> LocalRawAssum ([id],Default Implicit,CHole (loc, None))) (id::idl)
      | "`("; tc = LIST1 typeclass_constraint SEP "," ; ")" ->
	  List.map (fun (n, b, t) -> LocalRawAssum ([n], Generalized (Implicit, Explicit, b), t)) tc
      | "`{"; tc = LIST1 typeclass_constraint SEP "," ; "}" ->
	  List.map (fun (n, b, t) -> LocalRawAssum ([n], Generalized (Implicit, Implicit, b), t)) tc
    ] ]
  ;
  typeclass_constraint:
    [ [ "!" ; c = operconstr LEVEL "200" -> (loc, Anonymous), true, c
      | "{"; id = name; "}"; ":" ; expl = [ "!" -> true | -> false ] ; c = operconstr LEVEL "200" ->
	  id, expl, c
      | iid=ident_colon ; expl = [ "!" -> true | -> false ] ; c = operconstr LEVEL "200" ->
	  (loc, Name iid), expl, c
      | c = operconstr LEVEL "200" ->
	  (loc, Anonymous), false, c
    ] ]
  ;

  type_cstr:
    [ [ c=OPT [":"; c=lconstr -> c] -> (loc,c) ] ]
  ;
  END;;
