(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names
open Libnames
open Constrexpr
open Constrexpr_ops
open Util
open Tok
open Misctypes
open Decl_kinds

open Pcoq
open Pcoq.Prim
open Pcoq.Constr

(* TODO: avoid this redefinition without an extra dep to Notation_ops *)
let ldots_var = Id.of_string ".."

let constr_kw =
  [ "forall"; "fun"; "match"; "fix"; "cofix"; "with"; "in"; "for";
    "end"; "as"; "let"; "if"; "then"; "else"; "return";
    "Prop"; "Set"; "Type"; ".("; "_"; "..";
    "`{"; "`("; "{|"; "|}" ]

let _ = List.iter CLexer.add_keyword constr_kw

let mk_cast = function
    (c,(_,None)) -> c
  | (c,(_,Some ty)) ->
    let loc = Loc.merge_opt (constr_loc c) (constr_loc ty)
    in CAst.make ?loc @@ CCast(c, CastConv ty)

let binder_of_name expl (loc,na) =
  CLocalAssum ([loc, na], Default expl,
    CAst.make ?loc @@ CHole (Some (Evar_kinds.BinderType na), IntroAnonymous, None))

let binders_of_names l =
  List.map (binder_of_name Explicit) l

let mk_fixb (id,bl,ann,body,(loc,tyc)) =
  let ty = match tyc with
      Some ty -> ty
    | None    -> CAst.make @@ CHole (None, IntroAnonymous, None) in
  (id,ann,bl,ty,body)

let mk_cofixb (id,bl,ann,body,(loc,tyc)) =
  let _ = Option.map (fun (aloc,_) ->
    CErrors.user_err ?loc:aloc
      ~hdr:"Constr:mk_cofixb"
      (Pp.str"Annotation forbidden in cofix expression.")) (fst ann) in
  let ty = match tyc with
      Some ty -> ty
    | None -> CAst.make @@ CHole (None, IntroAnonymous, None) in
  (id,bl,ty,body)

let mk_fix(loc,kw,id,dcls) =
  if kw then
    let fb = List.map mk_fixb dcls in
    CAst.make ~loc @@ CFix(id,fb)
  else
    let fb = List.map mk_cofixb dcls in
    CAst.make ~loc @@ CCoFix(id,fb)

let mk_single_fix (loc,kw,dcl) =
  let (id,_,_,_,_) = dcl in mk_fix(loc,kw,id,[dcl])

let err () = raise Stream.Failure

(* Hack to parse "(x:=t)" as an explicit argument without conflicts with the *)
(* admissible notation "(x t)" *)
let lpar_id_coloneq =
  Gram.Entry.of_parser "test_lpar_id_coloneq"
    (fun strm ->
      match stream_nth 0 strm with
        | KEYWORD "(" ->
            (match stream_nth 1 strm with
	      | IDENT s ->
                  (match stream_nth 2 strm with
                    | KEYWORD ":=" ->
                        stream_njunk 3 strm;
                        Names.Id.of_string s
	            | _ -> err ())
              | _ -> err ())
        | _ -> err ())

let impl_ident_head =
  Gram.Entry.of_parser "impl_ident_head"
    (fun strm ->
      match stream_nth 0 strm with
	| KEYWORD "{" ->
	    (match stream_nth 1 strm with
	      | IDENT ("wf"|"struct"|"measure") -> err ()
	      | IDENT s ->
		  stream_njunk 2 strm;
		  Names.Id.of_string s
	      | _ -> err ())
	| _ -> err ())

let name_colon =
  Gram.Entry.of_parser "name_colon"
    (fun strm ->
      match stream_nth 0 strm with
	| IDENT s ->
            (match stream_nth 1 strm with
              | KEYWORD ":" ->
                  stream_njunk 2 strm;
                  Name (Names.Id.of_string s)
              | _ -> err ())
	| KEYWORD "_" ->
          (match stream_nth 1 strm with
              | KEYWORD ":" ->
                  stream_njunk 2 strm;
                  Anonymous
              | _ -> err ())
        | _ -> err ())

let aliasvar = function { CAst.loc = loc; CAst.v = CPatAlias (_, id) } -> Some (loc,Name id) | _ -> None

GEXTEND Gram
  GLOBAL: binder_constr lconstr constr operconstr universe_level sort global
  constr_pattern lconstr_pattern Constr.ident
  closed_binder open_binders binder binders binders_fixannot
  record_declaration typeclass_constraint pattern appl_arg;
  Constr.ident:
    [ [ id = Prim.ident -> id ] ]
  ;
  Prim.name:
    [ [ "_" -> Loc.tag ~loc:!@loc Anonymous ] ]
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
    [ [ "Set"  -> GSet
      | "Prop" -> GProp
      | "Type" -> GType []
      | "Type"; "@{"; u = universe; "}" -> GType u
      ] ]
  ;
  universe:
    [ [ IDENT "max"; "("; ids = LIST1 name SEP ","; ")" -> ids
      | id = name -> [id]
      ] ]
  ;
  lconstr:
    [ [ c = operconstr LEVEL "200" -> c ] ]
  ;
  constr:
    [ [ c = operconstr LEVEL "8" -> c
      | "@"; f=global; i = instance -> CAst.make ~loc:!@loc @@ CAppExpl((None,f,i),[]) ] ]
  ;
  operconstr:
    [ "200" RIGHTA
      [ c = binder_constr -> c ]
    | "100" RIGHTA
      [ c1 = operconstr; "<:"; c2 = binder_constr ->
                 CAst.make ~loc:(!@loc) @@ CCast(c1, CastVM c2)
      | c1 = operconstr; "<:"; c2 = SELF ->
                 CAst.make ~loc:(!@loc) @@ CCast(c1, CastVM c2)
      | c1 = operconstr; "<<:"; c2 = binder_constr ->
                 CAst.make ~loc:(!@loc) @@ CCast(c1, CastNative c2)
      | c1 = operconstr; "<<:"; c2 = SELF ->
                 CAst.make ~loc:(!@loc) @@ CCast(c1, CastNative c2)
      | c1 = operconstr; ":";c2 = binder_constr ->
                 CAst.make ~loc:(!@loc) @@ CCast(c1, CastConv c2)
      | c1 = operconstr; ":"; c2 = SELF ->
                 CAst.make ~loc:(!@loc) @@ CCast(c1, CastConv c2)
      | c1 = operconstr; ":>" ->
                 CAst.make ~loc:(!@loc) @@ CCast(c1, CastCoerce) ]
    | "99" RIGHTA [ ]
    | "90" RIGHTA [ ]
    | "10" LEFTA
      [ f=operconstr; args=LIST1 appl_arg -> CAst.make ~loc:(!@loc) @@ CApp((None,f),args)
      | "@"; f=global; i = instance; args=LIST0 NEXT -> CAst.make ~loc:!@loc @@ CAppExpl((None,f,i),args)
      | "@"; (locid,id) = pattern_identref; args=LIST1 identref ->
          let args = List.map (fun x -> CAst.make @@ CRef (Ident x,None), None) args in
          CAst.make ~loc:(!@loc) @@ CApp((None, CAst.make ?loc:locid @@ CPatVar id),args) ]
    | "9"
        [ ".."; c = operconstr LEVEL "0"; ".." ->
          CAst.make ~loc:!@loc @@ CAppExpl ((None, Ident (Loc.tag ~loc:!@loc ldots_var),None),[c]) ]
    | "8" [ ]
    | "1" LEFTA
      [ c=operconstr; ".("; f=global; args=LIST0 appl_arg; ")" ->
	CAst.make ~loc:(!@loc) @@ CApp((Some (List.length args+1), CAst.make @@ CRef (f,None)),args@[c,None])
      | c=operconstr; ".("; "@"; f=global;
        args=LIST0 (operconstr LEVEL "9"); ")" ->
        CAst.make ~loc:(!@loc) @@ CAppExpl((Some (List.length args+1),f,None),args@[c])
      | c=operconstr; "%"; key=IDENT -> CAst.make ~loc:(!@loc) @@ CDelimiters (key,c) ]
    | "0"
      [ c=atomic_constr -> c
      | c=match_constr -> c
      | "("; c = operconstr LEVEL "200"; ")" ->
          (match c.CAst.v with
            | CPrim (Numeral (n,true)) ->
                CAst.make ~loc:(!@loc) @@ CNotation("( _ )",([c],[],[]))
            | _ -> c)
      | "{|"; c = record_declaration; "|}" -> c
      | "`{"; c = operconstr LEVEL "200"; "}" ->
	  CAst.make ~loc:(!@loc) @@ CGeneralization (Implicit, None, c)
      | "`("; c = operconstr LEVEL "200"; ")" ->
	  CAst.make ~loc:(!@loc) @@ CGeneralization (Explicit, None, c)
      ] ]
  ;
  record_declaration:
    [ [ fs = record_fields -> CAst.make ~loc:(!@loc) @@ CRecord fs ] ]
  ;

  record_fields:
    [ [ f = record_field_declaration; ";"; fs = record_fields -> f :: fs
      | f = record_field_declaration -> [f]
      | -> []
    ] ]
  ;

  record_field_declaration:
    [ [ id = global; bl = binders; ":="; c = lconstr ->
      (id, mkCLambdaN ~loc:!@loc bl c) ] ]
  ;
  binder_constr:
    [ [ "forall"; bl = open_binders; ","; c = operconstr LEVEL "200" ->
          mkCProdN ~loc:!@loc bl c
      | "fun"; bl = open_binders; "=>"; c = operconstr LEVEL "200" ->
          mkCLambdaN ~loc:!@loc bl c
      | "let"; id=name; bl = binders; ty = type_cstr; ":=";
        c1 = operconstr LEVEL "200"; "in"; c2 = operconstr LEVEL "200" ->
          let ty,c1 = match ty, c1 with
          | (_,None), { CAst.v = CCast(c, CastConv t) } -> (Loc.tag ?loc:(constr_loc t) @@ Some t), c (* Tolerance, see G_vernac.def_body *)
          | _, _ -> ty, c1 in
          CAst.make ~loc:!@loc @@ CLetIn(id,mkCLambdaN ?loc:(constr_loc c1) bl c1,
                 Option.map (mkCProdN ?loc:(fst ty) bl) (snd ty), c2)
      | "let"; fx = single_fix; "in"; c = operconstr LEVEL "200" ->
          let fixp = mk_single_fix fx in
          let (li,id) = match fixp.CAst.v with
              CFix(id,_) -> id
            | CCoFix(id,_) -> id
            | _ -> assert false in
          CAst.make ~loc:!@loc @@ CLetIn((li,Name id),fixp,None,c)
      | "let"; lb = ["("; l=LIST0 name SEP ","; ")" -> l | "()" -> []];
	  po = return_type;
	  ":="; c1 = operconstr LEVEL "200"; "in";
          c2 = operconstr LEVEL "200" ->
          CAst.make ~loc:!@loc @@ CLetTuple (lb,po,c1,c2)
      | "let"; "'"; p=pattern; ":="; c1 = operconstr LEVEL "200";
          "in"; c2 = operconstr LEVEL "200" ->
	    CAst.make ~loc:!@loc @@
            CCases (LetPatternStyle, None,    [c1, None, None],       [Loc.tag ~loc:!@loc ([(Loc.tag ~loc:!@loc [p])], c2)])
      | "let"; "'"; p=pattern; ":="; c1 = operconstr LEVEL "200";
	  rt = case_type; "in"; c2 = operconstr LEVEL "200" ->
	    CAst.make ~loc:!@loc @@
            CCases (LetPatternStyle, Some rt, [c1, aliasvar p, None], [Loc.tag ~loc:!@loc ([(Loc.tag ~loc:!@loc [p])], c2)])

      | "let"; "'"; p=pattern; "in"; t = pattern LEVEL "200";
	  ":="; c1 = operconstr LEVEL "200"; rt = case_type;
          "in"; c2 = operconstr LEVEL "200" ->
	    CAst.make ~loc:!@loc @@
            CCases (LetPatternStyle, Some rt, [c1, aliasvar p, Some t], [Loc.tag ~loc:!@loc ([(Loc.tag ~loc:!@loc [p])], c2)])
      | "if"; c=operconstr LEVEL "200"; po = return_type;
	"then"; b1=operconstr LEVEL "200";
        "else"; b2=operconstr LEVEL "200" ->
          CAst.make ~loc:(!@loc) @@ CIf (c, po, b1, b2)
      | c=fix_constr -> c ] ]
  ;
  appl_arg:
    [ [ id = lpar_id_coloneq; c=lconstr; ")" ->
	  (c,Some (Loc.tag ~loc:!@loc @@ ExplByName id))
      | c=operconstr LEVEL "9" -> (c,None) ] ]
  ;
  atomic_constr:
    [ [ g=global; i=instance -> CAst.make ~loc:!@loc @@ CRef (g,i)
      | s=sort   -> CAst.make ~loc:!@loc @@  CSort s
      | n=INT    -> CAst.make ~loc:!@loc @@ CPrim (Numeral (n,true))
      | s=string -> CAst.make ~loc:!@loc @@ CPrim (String s)
      | "_"      -> CAst.make ~loc:!@loc @@ CHole (None, IntroAnonymous, None)
      | "?"; "["; id=ident; "]"  -> CAst.make ~loc:!@loc @@  CHole (None, IntroIdentifier id, None)
      | "?"; "["; id=pattern_ident; "]"  -> CAst.make ~loc:!@loc @@  CHole (None, IntroFresh id, None)
      | id=pattern_ident; inst = evar_instance -> CAst.make ~loc:!@loc @@ CEvar(id,inst) ] ]
  ;
  inst:
    [ [ id = ident; ":="; c = lconstr -> (id,c) ] ]
  ;
  evar_instance:
    [ [ "@{"; l = LIST1 inst SEP ";"; "}" -> l
      | -> [] ] ]
  ;
  instance:
    [ [ "@{"; l = LIST0 universe_level; "}" -> Some l
      | -> None ] ]
  ;
  universe_level:
    [ [ "Set" -> GSet
      | "Prop" -> GProp
      | "Type" -> GType None
      | id = name -> GType (Some id)
      ] ]
  ;
  fix_constr:
    [ [ fx1=single_fix -> mk_single_fix fx1
      | (_,kw,dcl1)=single_fix; "with"; dcls=LIST1 fix_decl SEP "with";
        "for"; id=identref ->
          mk_fix(!@loc,kw,id,dcl1::dcls)
    ] ]
  ;
  single_fix:
    [ [ kw=fix_kw; dcl=fix_decl -> (!@loc,kw,dcl) ] ]
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
        br=branches; "end" -> CAst.make ~loc:!@loc @@ CCases(RegularStyle,ty,ci,br) ] ]
  ;
  case_item:
    [ [ c=operconstr LEVEL "100";
        ona = OPT ["as"; id=name -> id];
	ty = OPT ["in"; t=pattern -> t] ->
	   (c,ona,ty) ] ]
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
    [ [ pl = LIST1 pattern LEVEL "99" SEP "," -> (Loc.tag ~loc:!@loc pl) ] ]
  ;
  eqn:
    [ [ pll = LIST1 mult_pattern SEP "|";
        "=>"; rhs = lconstr -> (Loc.tag ~loc:!@loc (pll,rhs)) ] ]
  ;
  record_pattern:
    [ [ id = global; ":="; pat = pattern -> (id, pat) ] ]
  ;
  record_patterns:
    [ [ p = record_pattern; ";"; ps = record_patterns -> p :: ps
      | p = record_pattern; ";" -> [p]
      | p = record_pattern-> [p]
      | -> []
    ] ]
  ;
  pattern:
    [ "200" RIGHTA [ ]
    | "100" RIGHTA
      [ p = pattern; "|"; pl = LIST1 pattern SEP "|" -> CAst.make ~loc:!@loc @@ CPatOr (p::pl) ]
    | "99" RIGHTA [ ]
    | "11" LEFTA
      [ p = pattern; "as"; id = ident ->
        CAst.make ~loc:!@loc @@ CPatAlias (p, id) ]
    | "10" RIGHTA
      [ p = pattern; lp = LIST1 NEXT ->
        (let open CAst in match p with
	  | { v = CPatAtom (Some r) } -> CAst.make ~loc:!@loc @@ CPatCstr (r, None, lp)
	  | { v = CPatCstr (r, None, l2); loc } ->
                 CErrors.user_err ?loc ~hdr:"compound_pattern"
                 (Pp.str "Nested applications not supported.")
	  | { v = CPatCstr (r, l1, l2) }  -> CAst.make ~loc:!@loc @@ CPatCstr (r, l1 , l2@lp)
	  | { v = CPatNotation (n, s, l) } -> CAst.make ~loc:!@loc @@ CPatNotation (n , s, l@lp)
          | _ -> CErrors.user_err
                 ?loc:(cases_pattern_expr_loc p) ~hdr:"compound_pattern"
                 (Pp.str "Such pattern cannot have arguments."))
      |"@"; r = Prim.reference; lp = LIST0 NEXT ->
        CAst.make ~loc:!@loc @@ CPatCstr (r, Some lp, []) ]
    | "1" LEFTA
      [ c = pattern; "%"; key=IDENT -> CAst.make ~loc:!@loc @@ CPatDelimiters (key,c) ]
    | "0"
      [ r = Prim.reference                -> CAst.make ~loc:!@loc @@ CPatAtom (Some r)
      | "{|"; pat = record_patterns; "|}" -> CAst.make ~loc:!@loc @@ CPatRecord pat
      | "_" -> CAst.make ~loc:!@loc @@ CPatAtom None
      | "("; p = pattern LEVEL "200"; ")" ->
          (match p.CAst.v with
            | CPatPrim (Numeral (n,true)) ->
                 CAst.make ~loc:!@loc @@ CPatNotation("( _ )",([p],[]),[])
            | _ -> p)
      | "("; p = pattern LEVEL "200"; ":"; ty = lconstr; ")" ->
          let p =
            match p with
            | { CAst.v = CPatPrim (Numeral (n,true)) } ->
                 CAst.make ~loc:!@loc @@ CPatNotation("( _ )",([p],[]),[])
            | _ -> p
          in
	  CAst.make ~loc:!@loc @@ CPatCast (p, ty)
      | n = INT    -> CAst.make ~loc:!@loc @@ CPatPrim (Numeral (n,true))
      | s = string -> CAst.make ~loc:!@loc @@ CPatPrim (String s) ] ]
  ;
  impl_ident_tail:
    [ [ "}" -> binder_of_name Implicit
    | nal=LIST1 name; ":"; c=lconstr; "}" ->
        (fun na -> CLocalAssum (na::nal,Default Implicit,c))
    | nal=LIST1 name; "}" ->
        (fun na -> CLocalAssum (na::nal,Default Implicit,
                                CAst.make ?loc:(Loc.merge_opt (fst na) (Some !@loc)) @@ CHole (Some (Evar_kinds.BinderType (snd na)), IntroAnonymous, None)))
    | ":"; c=lconstr; "}" ->
	(fun na -> CLocalAssum ([na],Default Implicit,c))
    ] ]
  ;
  fixannot:
    [ [ "{"; IDENT "struct"; id=identref; "}" -> (Some id, CStructRec)
    | "{"; IDENT "wf"; rel=constr; id=OPT identref; "}" -> (id, CWfRec rel)
    | "{"; IDENT "measure"; m=constr; id=OPT identref;
	rel=OPT constr; "}" -> (id, CMeasureRec (m,rel))
    ] ]
  ;
  impl_name_head:
    [ [ id = impl_ident_head -> (Loc.tag ~loc:!@loc @@ Name id) ] ]
  ;
  binders_fixannot:
    [ [ na = impl_name_head; assum = impl_ident_tail; bl = binders_fixannot ->
          (assum na :: fst bl), snd bl
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
          [CLocalAssum (id::idl,Default Explicit,c)]
	(* binders factorized with open binder *)
      | id = name; idl = LIST0 name; bl = binders ->
          binders_of_names (id::idl) @ bl
      | id1 = name; ".."; id2 = name ->
          [CLocalAssum ([id1;(Loc.tag ~loc:!@loc (Name ldots_var));id2],
	                  Default Explicit, CAst.make ~loc:!@loc @@ CHole (None, IntroAnonymous, None))]
      | bl = closed_binder; bl' = binders ->
	  bl@bl'
    ] ]
  ;
  binders:
    [ [ l = LIST0 binder -> List.flatten l ] ]
  ;
  binder:
    [ [ id = name -> [CLocalAssum ([id],Default Explicit, CAst.make ~loc:!@loc @@ CHole (None, IntroAnonymous, None))]
      | bl = closed_binder -> bl ] ]
  ;
  closed_binder:
    [ [ "("; id=name; idl=LIST1 name; ":"; c=lconstr; ")" ->
          [CLocalAssum (id::idl,Default Explicit,c)]
      | "("; id=name; ":"; c=lconstr; ")" ->
          [CLocalAssum ([id],Default Explicit,c)]
      | "("; id=name; ":="; c=lconstr; ")" ->
          (match c.CAst.v with
          | CCast(c, CastConv t) -> [CLocalDef (id,c,Some t)]
          | _ -> [CLocalDef (id,c,None)])
      | "("; id=name; ":"; t=lconstr; ":="; c=lconstr; ")" ->
          [CLocalDef (id,c,Some t)]
      | "{"; id=name; "}" ->
          [CLocalAssum ([id],Default Implicit, CAst.make ~loc:!@loc @@ CHole (None, IntroAnonymous, None))]
      | "{"; id=name; idl=LIST1 name; ":"; c=lconstr; "}" ->
          [CLocalAssum (id::idl,Default Implicit,c)]
      | "{"; id=name; ":"; c=lconstr; "}" ->
          [CLocalAssum ([id],Default Implicit,c)]
      | "{"; id=name; idl=LIST1 name; "}" ->
          List.map (fun id -> CLocalAssum ([id],Default Implicit, CAst.make ~loc:!@loc @@ CHole (None, IntroAnonymous, None))) (id::idl)
      | "`("; tc = LIST1 typeclass_constraint SEP "," ; ")" ->
	  List.map (fun (n, b, t) -> CLocalAssum ([n], Generalized (Implicit, Explicit, b), t)) tc
      | "`{"; tc = LIST1 typeclass_constraint SEP "," ; "}" ->
	  List.map (fun (n, b, t) -> CLocalAssum ([n], Generalized (Implicit, Implicit, b), t)) tc
      | "'"; p = pattern LEVEL "0" ->
          let (p, ty) =
            match p.CAst.v with
            | CPatCast (p, ty) -> (p, Some ty)
            | _ -> (p, None)
          in
          [CLocalPattern (Loc.tag ~loc:!@loc (p, ty))]
    ] ]
  ;
  typeclass_constraint:
    [ [ "!" ; c = operconstr LEVEL "200" -> (Loc.tag ~loc:!@loc Anonymous), true, c
      | "{"; id = name; "}"; ":" ; expl = [ "!" -> true | -> false ] ; c = operconstr LEVEL "200" ->
	  id, expl, c
      | iid=name_colon ; expl = [ "!" -> true | -> false ] ; c = operconstr LEVEL "200" ->
	  (Loc.tag ~loc:!@loc iid), expl, c
      | c = operconstr LEVEL "200" ->
	  (Loc.tag ~loc:!@loc Anonymous), false, c
    ] ]
  ;

  type_cstr:
    [ [ c=OPT [":"; c=lconstr -> c] -> Loc.tag ~loc:!@loc c ] ]
  ;
  END;;
