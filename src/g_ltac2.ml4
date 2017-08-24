(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Util
open Names
open Tok
open Pcoq
open Constrexpr
open Misctypes
open Tac2expr
open Tac2qexpr
open Ltac_plugin

let err () = raise Stream.Failure

(* lookahead for (x:=t), (?x:=t) and (1:=t) *)
let test_lpar_idnum_coloneq =
  Gram.Entry.of_parser "test_lpar_idnum_coloneq"
    (fun strm ->
      match stream_nth 0 strm with
        | KEYWORD "(" ->
            (match stream_nth 1 strm with
              | IDENT _ | INT _ ->
                  (match stream_nth 2 strm with
                    | KEYWORD ":=" -> ()
                    | _ -> err ())
              | KEYWORD "$" ->
                (match stream_nth 2 strm with
                  | IDENT _ ->
                      (match stream_nth 3 strm with
                        | KEYWORD ":=" -> ()
                        | _ -> err ())
                  | _ -> err ())
              | _ -> err ())
        | _ -> err ())

(* Hack to recognize "(x)" *)
let test_lpar_id_rpar =
  Gram.Entry.of_parser "lpar_id_coloneq"
    (fun strm ->
      match stream_nth 0 strm with
        | KEYWORD "(" ->
            (match stream_nth 1 strm with
              | IDENT _ ->
                  (match stream_nth 2 strm with
	            | KEYWORD ")" -> ()
	            | _ -> err ())
	      | _ -> err ())
	| _ -> err ())

let tac2expr = Tac2entries.Pltac.tac2expr
let tac2type = Gram.entry_create "tactic:tac2type"
let tac2def_val = Gram.entry_create "tactic:tac2def_val"
let tac2def_typ = Gram.entry_create "tactic:tac2def_typ"
let tac2def_ext = Gram.entry_create "tactic:tac2def_ext"
let tac2def_syn = Gram.entry_create "tactic:tac2def_syn"
let tac2mode = Gram.entry_create "vernac:ltac2_command"

let inj_wit wit loc x = CTacExt (loc, Genarg.in_gen (Genarg.rawwit wit) x)
let inj_open_constr loc c = inj_wit Stdarg.wit_open_constr loc c
let inj_pattern loc c = inj_wit Tac2env.wit_pattern loc c
let inj_reference loc c = inj_wit Tac2env.wit_reference loc c

let pattern_of_qualid loc id =
  if Tac2env.is_constructor (snd id) then CPatRef (loc, RelId id, [])
  else
    let (dp, id) = Libnames.repr_qualid (snd id) in
    if DirPath.is_empty dp then CPatVar (Some loc, Name id)
    else
      CErrors.user_err ~loc (Pp.str "Syntax error")

GEXTEND Gram
  GLOBAL: tac2expr tac2type tac2def_val tac2def_typ tac2def_ext tac2def_syn;
  tac2pat:
    [ "1" LEFTA
      [ id = Prim.qualid; pl = LIST1 tac2pat LEVEL "0" ->
        if Tac2env.is_constructor (snd id) then
          CPatRef (!@loc, RelId id, pl)
        else
          CErrors.user_err ~loc:!@loc (Pp.str "Syntax error")
      | id = Prim.qualid -> pattern_of_qualid !@loc id
      | "["; "]" -> CPatRef (!@loc, AbsKn (Other Tac2core.Core.c_nil), [])
      | p1 = tac2pat; "::"; p2 = tac2pat ->
        CPatRef (!@loc, AbsKn (Other Tac2core.Core.c_cons), [p1; p2])
      ]
    | "0"
      [ "_" -> CPatVar (Some !@loc, Anonymous)
      | "()" -> CPatRef (!@loc, AbsKn (Tuple 0), [])
      | id = Prim.qualid -> pattern_of_qualid !@loc id
      | "("; pl = LIST0 tac2pat LEVEL "1" SEP ","; ")" ->
        CPatRef (!@loc, AbsKn (Tuple (List.length pl)), pl) ]
    ]
  ;
  tac2expr:
    [ "6" RIGHTA
        [ e1 = SELF; ";"; e2 = SELF -> CTacSeq (!@loc, e1, e2) ]
    | "5"
      [ "fun"; it = LIST1 input_fun ; "=>"; body = tac2expr LEVEL "6" -> CTacFun (!@loc, it, body)
      | "let"; isrec = rec_flag;
          lc = LIST1 let_clause SEP "with"; "in";
          e = tac2expr LEVEL "6" -> CTacLet (!@loc, isrec, lc, e)
      | "match"; e = tac2expr LEVEL "5"; "with"; bl = branches; "end" ->
         CTacCse (!@loc, e, bl)
      ]
    | "4" LEFTA [ ]
    | "::" RIGHTA
      [ e1 = tac2expr; "::"; e2 = tac2expr ->
        CTacApp (!@loc, CTacCst (!@loc, AbsKn (Other Tac2core.Core.c_cons)), [e1; e2])
      ]
    | [ e0 = SELF; ","; el = LIST1 NEXT SEP "," ->
        let el = e0 :: el in
        CTacApp (!@loc, CTacCst (!@loc, AbsKn (Tuple (List.length el))), el) ]
    | "1" LEFTA
      [ e = tac2expr; el = LIST1 tac2expr LEVEL "0" -> CTacApp (!@loc, e, el)
      | e = SELF; ".("; qid = Prim.qualid; ")" -> CTacPrj (!@loc, e, RelId qid)
      | e = SELF; ".("; qid = Prim.qualid; ")"; ":="; r = tac2expr LEVEL "5" -> CTacSet (!@loc, e, RelId qid, r) ]
    | "0"
      [ "("; a = SELF; ")" -> a
      | "("; a = SELF; ":"; t = tac2type; ")" -> CTacCnv (!@loc, a, t)
      | "()" -> CTacCst (!@loc, AbsKn (Tuple 0))
      | "("; ")" -> CTacCst (!@loc, AbsKn (Tuple 0))
      | "["; a = LIST0 tac2expr LEVEL "5" SEP ";"; "]" -> CTacLst (Loc.tag ~loc:!@loc a)
      | "{"; a = tac2rec_fieldexprs; "}" -> CTacRec (!@loc, a)
      | a = tactic_atom -> a ]
    ]
  ;
  branches:
  [ [ -> []
    | "|"; bl = LIST1 branch SEP "|" -> bl
    | bl = LIST1 branch SEP "|" -> bl ]
  ]
  ;
  branch:
  [ [ pat = tac2pat LEVEL "1"; "=>"; e = tac2expr LEVEL "6" -> (pat, e) ] ]
  ;
  rec_flag:
    [ [ IDENT "rec" -> true
      | -> false ] ]
  ;
  typ_param:
    [ [ "'"; id = Prim.ident -> id ] ]
  ;
  tactic_atom:
    [ [ n = Prim.integer -> CTacAtm (Loc.tag ~loc:!@loc (AtmInt n))
      | s = Prim.string -> CTacAtm (Loc.tag ~loc:!@loc (AtmStr s))
      | id = Prim.qualid ->
        if Tac2env.is_constructor (snd id) then CTacCst (!@loc, RelId id) else CTacRef (RelId id)
      | "@"; id = Prim.ident -> Tac2quote.of_ident (Loc.tag ~loc:!@loc id)
      | "&"; id = lident -> Tac2quote.of_hyp ~loc:!@loc id
      | "'"; c = Constr.constr -> inj_open_constr !@loc c
      | IDENT "constr"; ":"; "("; c = Constr.lconstr; ")" -> Tac2quote.of_constr c
      | IDENT "open_constr"; ":"; "("; c = Constr.lconstr; ")" -> Tac2quote.of_open_constr c
      | IDENT "ident"; ":"; "("; c = lident; ")" -> Tac2quote.of_ident c
      | IDENT "pattern"; ":"; "("; c = Constr.lconstr_pattern; ")" -> inj_pattern !@loc c
      | IDENT "reference"; ":"; "("; c = globref; ")" -> inj_reference !@loc c
    ] ]
  ;
  let_clause:
    [ [ binder = let_binder; ":="; te = tac2expr ->
        let (pat, fn) = binder in
        let te = match fn with None -> te | Some args -> CTacFun (!@loc, args, te) in
        (pat, None, te)
    ] ]
  ;
  let_binder:
    [ [ pats = LIST1 input_fun ->
        match pats with
        | [CPatVar _ as pat, None] -> (pat, None)
        | (CPatVar (_, Name id) as pat, None) :: args -> (pat, Some args)
        | [pat, None] -> (pat, None)
        | _ -> CErrors.user_err ~loc:!@loc (str "Invalid pattern")
    ] ]
  ;
  tac2type:
    [ "5" RIGHTA
      [ t1 = tac2type; "->"; t2 = tac2type -> CTypArrow (!@loc, t1, t2) ]
    | "2"
      [ t = tac2type; "*"; tl = LIST1 tac2type LEVEL "1" SEP "*" ->
        let tl = t :: tl in
        CTypRef (!@loc, AbsKn (Tuple (List.length tl)), tl) ]
    | "1" LEFTA
      [ t = SELF; qid = Prim.qualid -> CTypRef (!@loc, RelId qid, [t]) ]
    | "0"
      [ "("; t = tac2type LEVEL "5"; ")"  -> t
      | id = typ_param -> CTypVar (Loc.tag ~loc:!@loc (Name id))
      | "_" -> CTypVar (Loc.tag ~loc:!@loc Anonymous)
      | qid = Prim.qualid -> CTypRef (!@loc, RelId qid, [])
      | "("; p = LIST1 tac2type LEVEL "5" SEP ","; ")"; qid = Prim.qualid ->
        CTypRef (!@loc, RelId qid, p) ]
    ];
  locident:
    [ [ id = Prim.ident -> Loc.tag ~loc:!@loc id ] ]
  ;
  binder:
    [ [ "_" -> Loc.tag ~loc:!@loc Anonymous
      | l = Prim.ident -> Loc.tag ~loc:!@loc (Name l) ] ]
  ;
  input_fun:
    [ [ b = tac2pat LEVEL "0" -> (b, None)
      | "("; b = tac2pat; t = OPT [ ":"; t = tac2type -> t ]; ")" -> (b, t) ] ]
  ;
  tac2def_body:
    [ [ name = binder; it = LIST0 input_fun; ":="; e = tac2expr ->
        let e = if List.is_empty it then e else CTacFun (!@loc, it, e) in
        (name, e)
    ] ]
  ;
  tac2def_val:
    [ [ isrec = rec_flag; l = LIST1 tac2def_body SEP "with" ->
        StrVal (isrec, l)
    ] ]
  ;
  tac2typ_knd:
    [ [ t = tac2type -> CTydDef (Some t)
      | "["; ".."; "]" -> CTydOpn
      | "["; t = tac2alg_constructors; "]" -> CTydAlg t
      | "{"; t = tac2rec_fields; "}"-> CTydRec t ] ]
  ;
  tac2alg_constructors:
    [ [ "|"; cs = LIST1 tac2alg_constructor SEP "|" -> cs
      | cs = LIST0 tac2alg_constructor SEP "|" -> cs ] ]
  ;
  tac2alg_constructor:
    [ [ c = Prim.ident -> (c, [])
      | c = Prim.ident; "("; args = LIST0 tac2type SEP ","; ")"-> (c, args) ] ]
  ;
  tac2rec_fields:
    [ [ f = tac2rec_field; ";"; l = tac2rec_fields -> f :: l
      | f = tac2rec_field; ";" -> [f]
      | f = tac2rec_field -> [f]
      | -> [] ] ]
  ;
  tac2rec_field:
    [ [ mut = [ -> false | IDENT "mutable" -> true]; id = Prim.ident; ":"; t = tac2type -> (id, mut, t) ] ]
  ;
  tac2rec_fieldexprs:
    [ [ f = tac2rec_fieldexpr; ";"; l = tac2rec_fieldexprs -> f :: l
      | f = tac2rec_fieldexpr; ";" -> [f]
      | f = tac2rec_fieldexpr-> [f]
      | -> [] ] ]
  ;
  tac2rec_fieldexpr:
    [ [ qid = Prim.qualid; ":="; e = tac2expr LEVEL "1" -> RelId qid, e ] ]
  ;
  tac2typ_prm:
    [ [ -> []
      | id = typ_param -> [Loc.tag ~loc:!@loc id]
      | "("; ids = LIST1 [ id = typ_param -> Loc.tag ~loc:!@loc id ] SEP "," ;")" -> ids
    ] ]
  ;
  tac2typ_def:
    [ [ prm = tac2typ_prm; id = Prim.qualid; (r, e) = tac2type_body -> (id, r, (prm, e)) ] ]
  ;
  tac2type_body:
    [ [ -> false, CTydDef None
      | ":="; e = tac2typ_knd -> false, e
      | "::="; e = tac2typ_knd -> true, e
    ] ]
  ;
  tac2def_typ:
    [ [ "Type"; isrec = rec_flag; l = LIST1 tac2typ_def SEP "with" ->
        StrTyp (isrec, l)
    ] ]
  ;
  tac2def_ext:
    [ [ "@"; IDENT "external"; id = locident; ":"; t = tac2type LEVEL "5"; ":=";
        plugin = Prim.string; name = Prim.string ->
        let ml = { mltac_plugin = plugin; mltac_tactic = name } in
        StrPrm (id, t, ml)
    ] ]
  ;
  syn_node:
    [ [ "_" -> Loc.tag ~loc:!@loc None
      | id = Prim.ident -> Loc.tag ~loc:!@loc (Some id)
    ] ]
  ;
  sexpr:
    [ [ s = Prim.string -> SexprStr (Loc.tag ~loc:!@loc s)
      | n = Prim.integer -> SexprInt (Loc.tag ~loc:!@loc n)
      | id = syn_node -> SexprRec (!@loc, id, [])
      | id = syn_node; "("; tok = LIST1 sexpr SEP "," ; ")" ->
        SexprRec (!@loc, id, tok)
    ] ]
  ;
  syn_level:
    [ [ -> None
      | ":"; n = Prim.integer -> Some n
    ] ]
  ;
  tac2def_syn:
    [ [ "Notation"; toks = LIST1 sexpr; n = syn_level; ":=";
        e = tac2expr ->
        StrSyn (toks, n, e)
    ] ]
  ;
  lident:
    [ [ id = Prim.ident -> Loc.tag ~loc:!@loc id ] ]
  ;
  globref:
    [ [ "&"; id = Prim.ident -> Libnames.Ident (Loc.tag ~loc:!@loc id)
      | qid = Prim.qualid -> Libnames.Qualid qid
    ] ]
  ;
END

(** Quotation scopes used by notations *)

open Tac2entries.Pltac

let loc_of_ne_list l = Loc.merge_opt (fst (List.hd l)) (fst (List.last l))

GEXTEND Gram
  GLOBAL: q_ident q_bindings q_intropattern q_intropatterns q_induction_clause
          q_rewriting q_clause q_dispatch q_occurrences;
  anti:
    [ [ "$"; id = Prim.ident -> QAnti (Loc.tag ~loc:!@loc id) ] ]
  ;
  ident_or_anti:
    [ [ id = lident -> QExpr id
      | "$"; id = Prim.ident -> QAnti (Loc.tag ~loc:!@loc id)
    ] ]
  ;
  lident:
    [ [ id = Prim.ident -> Loc.tag ~loc:!@loc id ] ]
  ;
  lnatural:
    [ [ n = Prim.natural -> Loc.tag ~loc:!@loc n ] ]
  ;
  q_ident:
    [ [ id = ident_or_anti -> id ] ]
  ;
  qhyp:
    [ [ x = anti -> x
      | n = lnatural -> QExpr (Loc.tag ~loc:!@loc @@ QAnonHyp n)
      | id = lident -> QExpr (Loc.tag ~loc:!@loc @@ QNamedHyp id)
    ] ]
  ;
  simple_binding:
    [ [ "("; h = qhyp; ":="; c = Constr.lconstr; ")" ->
        Loc.tag ~loc:!@loc (h, c)
    ] ]
  ;
  bindings:
    [ [ test_lpar_idnum_coloneq; bl = LIST1 simple_binding ->
        Loc.tag ~loc:!@loc @@ QExplicitBindings bl
      | bl = LIST1 Constr.constr ->
        Loc.tag ~loc:!@loc @@ QImplicitBindings bl
    ] ]
  ;
  q_bindings:
    [ [ bl = with_bindings -> bl ] ]
  ;
  intropatterns:
    [ [ l = LIST0 nonsimple_intropattern -> Loc.tag ~loc:!@loc l ]]
  ;
(*   ne_intropatterns: *)
(*     [ [ l = LIST1 nonsimple_intropattern -> l ]] *)
(*   ; *)
  or_and_intropattern:
    [ [ "["; tc = LIST1 intropatterns SEP "|"; "]" -> Loc.tag ~loc:!@loc @@ QIntroOrPattern tc
      | "()" -> Loc.tag ~loc:!@loc @@ QIntroAndPattern (Loc.tag ~loc:!@loc [])
      | "("; si = simple_intropattern; ")" -> Loc.tag ~loc:!@loc @@ QIntroAndPattern (Loc.tag ~loc:!@loc [si])
      | "("; si = simple_intropattern; ",";
             tc = LIST1 simple_intropattern SEP "," ; ")" ->
             Loc.tag ~loc:!@loc @@ QIntroAndPattern (Loc.tag ~loc:!@loc (si::tc))
      | "("; si = simple_intropattern; "&";
	     tc = LIST1 simple_intropattern SEP "&" ; ")" ->
	  (* (A & B & C) is translated into (A,(B,C)) *)
	  let rec pairify = function
	    | ([]|[_]|[_;_]) as l -> Loc.tag ~loc:!@loc l
	    | t::q ->
              let q =
                Loc.tag ~loc:!@loc @@
                  QIntroAction (Loc.tag ~loc:!@loc @@
                    QIntroOrAndPattern (Loc.tag ~loc:!@loc @@
                      QIntroAndPattern (pairify q)))
              in
              Loc.tag ~loc:!@loc [t; q]
	  in Loc.tag ~loc:!@loc @@ QIntroAndPattern (pairify (si::tc)) ] ]
  ;
  equality_intropattern:
    [ [ "->" -> Loc.tag ~loc:!@loc @@ QIntroRewrite true
      | "<-" -> Loc.tag ~loc:!@loc @@ QIntroRewrite false
      | "[="; tc = intropatterns; "]" -> Loc.tag ~loc:!@loc @@ QIntroInjection tc ] ]
  ;
  naming_intropattern:
    [ [ LEFTQMARK; id = lident ->
        Loc.tag ~loc:!@loc @@ QIntroFresh (QExpr id)
      | "?$"; id = lident ->
        Loc.tag ~loc:!@loc @@ QIntroFresh (QAnti id)
      | "?" ->
        Loc.tag ~loc:!@loc @@ QIntroAnonymous
      | id = ident_or_anti ->
        Loc.tag ~loc:!@loc @@ QIntroIdentifier id
    ] ]
  ;
  nonsimple_intropattern:
    [ [ l = simple_intropattern -> l
      | "*"  -> Loc.tag ~loc:!@loc @@ QIntroForthcoming true
      | "**" -> Loc.tag ~loc:!@loc @@ QIntroForthcoming false ]]
  ;
  simple_intropattern:
    [ [ pat = simple_intropattern_closed ->
(*         l = LIST0 ["%"; c = operconstr LEVEL "0" -> c] -> *)
        (** TODO: handle %pat *)
        pat
    ] ]
  ;
  simple_intropattern_closed:
    [ [ pat = or_and_intropattern ->
        Loc.tag ~loc:!@loc @@ QIntroAction (Loc.tag ~loc:!@loc @@ QIntroOrAndPattern pat)
      | pat = equality_intropattern ->
        Loc.tag ~loc:!@loc @@ QIntroAction pat
      | "_" ->
        Loc.tag ~loc:!@loc @@ QIntroAction (Loc.tag ~loc:!@loc @@ QIntroWildcard)
      | pat = naming_intropattern ->
        Loc.tag ~loc:!@loc @@ QIntroNaming pat
    ] ]
  ;
  q_intropatterns:
    [ [ ipat = intropatterns -> ipat ] ]
  ;
  q_intropattern:
    [ [ ipat = simple_intropattern -> ipat ] ]
  ;
  nat_or_anti:
    [ [ n = lnatural -> QExpr n
      | "$"; id = Prim.ident -> QAnti (Loc.tag ~loc:!@loc id)
    ] ]
  ;
  eqn_ipat:
    [ [ IDENT "eqn"; ":"; pat = naming_intropattern -> Some pat
      | -> None
    ] ]
  ;
  with_bindings:
    [ [ "with"; bl = bindings -> bl | -> Loc.tag ~loc:!@loc @@ QNoBindings ] ]
  ;
  constr_with_bindings:
    [ [ c = Constr.constr; l = with_bindings -> Loc.tag ~loc:!@loc @@ (c, l) ] ]
  ;
  destruction_arg:
    [ [ n = lnatural -> QElimOnAnonHyp n
      | c = constr_with_bindings -> QElimOnConstr c
    ] ]
  ;
  as_or_and_ipat:
    [ [ "as"; ipat = or_and_intropattern -> Some ipat
      | -> None
    ] ]
  ;
  occs_nums:
    [ [ nl = LIST1 nat_or_anti -> Loc.tag ~loc:!@loc @@ QOnlyOccurrences nl
      | "-"; n = nat_or_anti; nl = LIST0 nat_or_anti ->
        Loc.tag ~loc:!@loc @@ QAllOccurrencesBut (n::nl)
    ] ]
  ;
  occs:
    [ [ "at"; occs = occs_nums -> occs | -> Loc.tag ~loc:!@loc QAllOccurrences ] ]
  ;
  hypident:
    [ [ id = ident_or_anti ->
          id,Locus.InHyp
      | "("; IDENT "type"; IDENT "of"; id = ident_or_anti; ")" ->
	  id,Locus.InHypTypeOnly
      | "("; IDENT "value"; IDENT "of"; id = ident_or_anti; ")" ->
	  id,Locus.InHypValueOnly
    ] ]
  ;
  hypident_occ:
    [ [ (id,l)=hypident; occs=occs -> ((occs,id),l) ] ]
  ;
  in_clause:
    [ [ "*"; occs=occs ->
        { q_onhyps = None; q_concl_occs = occs }
      | "*"; "|-"; occs = concl_occ ->
        { q_onhyps = None; q_concl_occs = occs }
      | hl = LIST0 hypident_occ SEP ","; "|-"; occs = concl_occ ->
        { q_onhyps = Some hl; q_concl_occs = occs }
      | hl = LIST0 hypident_occ SEP "," ->
        { q_onhyps = Some hl; q_concl_occs = Loc.tag ~loc:!@loc QNoOccurrences }
    ] ]
  ;
  clause:
    [ [ "in"; cl = in_clause -> Loc.tag ~loc:!@loc @@ cl
      | "at"; occs = occs_nums ->
        Loc.tag ~loc:!@loc @@ { q_onhyps = Some []; q_concl_occs = occs }
    ] ]
  ;
  q_clause:
    [ [ cl = clause -> cl ] ]
  ;
  concl_occ:
    [ [ "*"; occs = occs -> occs
      | -> Loc.tag ~loc:!@loc QNoOccurrences
    ] ]
  ;
  induction_clause:
    [ [ c = destruction_arg; pat = as_or_and_ipat; eq = eqn_ipat;
        cl = OPT clause ->
        Loc.tag ~loc:!@loc @@ {
          indcl_arg = c;
          indcl_eqn = eq;
          indcl_as = pat;
          indcl_in = cl;
        }
    ] ]
  ;
  q_induction_clause:
    [ [ cl = induction_clause -> cl ] ]
  ;
  orient:
    [ [ "->" -> Loc.tag ~loc:!@loc (Some true)
      | "<-" -> Loc.tag ~loc:!@loc (Some false)
      | -> Loc.tag ~loc:!@loc None
    ]]
  ;
  rewriter:
    [ [ "!"; c = constr_with_bindings ->
        (Loc.tag ~loc:!@loc @@ QRepeatPlus,c)
      | ["?"| LEFTQMARK]; c = constr_with_bindings ->
        (Loc.tag ~loc:!@loc @@ QRepeatStar,c)
      | n = lnatural; "!"; c = constr_with_bindings ->
        (Loc.tag ~loc:!@loc @@ QPrecisely n,c)
      |	n = lnatural; ["?" | LEFTQMARK]; c = constr_with_bindings ->
        (Loc.tag ~loc:!@loc @@ QUpTo n,c)
      | n = lnatural; c = constr_with_bindings ->
        (Loc.tag ~loc:!@loc @@ QPrecisely n,c)
      | c = constr_with_bindings ->
        (Loc.tag ~loc:!@loc @@ QPrecisely (Loc.tag 1), c)
      ] ]
  ;
  oriented_rewriter:
    [ [ b = orient; (m, c) = rewriter ->
      Loc.tag ~loc:!@loc @@ {
        rew_orient = b;
        rew_repeat = m;
        rew_equatn = c;
      }
    ] ]
  ;
  q_rewriting:
    [ [ r = oriented_rewriter -> r ] ]
  ;
  tactic_then_last:
    [ [ "|"; lta = LIST0 OPT tac2expr LEVEL "6" SEP "|" -> lta
      | -> []
    ] ]
  ;
  tactic_then_gen:
    [ [ ta = tac2expr; "|"; (first,last) = tactic_then_gen -> (Some ta :: first, last)
      | ta = tac2expr; ".."; l = tactic_then_last -> ([], Some (Some ta, l))
      | ".."; l = tactic_then_last -> ([], Some (None, l))
      | ta = tac2expr -> ([Some ta], None)
      | "|"; (first,last) = tactic_then_gen -> (None :: first, last)
      | -> ([None], None)
    ] ]
  ;
  q_dispatch:
    [ [ d = tactic_then_gen -> Loc.tag ~loc:!@loc d ] ]
  ;
  q_occurrences:
    [ [ occs = occs -> occs ] ]
  ;
END

(** Extension of constr syntax *)

GEXTEND Gram
  Pcoq.Constr.operconstr: LEVEL "0"
    [ [ IDENT "ltac2"; ":"; "("; tac = tac2expr; ")" ->
        let arg = Genarg.in_gen (Genarg.rawwit Tac2env.wit_ltac2) tac in
        CAst.make ~loc:!@loc (CHole (None, IntroAnonymous, Some arg))
      | "&"; id = [ id = Prim.ident -> Loc.tag ~loc:!@loc id ] ->
        let tac = Tac2quote.of_exact_hyp ~loc:!@loc id in
        let arg = Genarg.in_gen (Genarg.rawwit Tac2env.wit_ltac2) tac in
        CAst.make ~loc:!@loc (CHole (None, IntroAnonymous, Some arg))
    ] ]
  ;
END

let pr_ltac2entry _ = mt () (** FIXME *)
let pr_ltac2expr _ = mt () (** FIXME *)

VERNAC ARGUMENT EXTEND ltac2_entry
PRINTED BY pr_ltac2entry
| [ tac2def_val(v) ] -> [ v ]
| [ tac2def_typ(t) ] -> [ t ]
| [ tac2def_ext(e) ] -> [ e ]
| [ tac2def_syn(e) ] -> [ e ]
END

let classify_ltac2 = function
| StrSyn _ -> Vernacexpr.VtUnknown, Vernacexpr.VtNow
| StrVal _ | StrPrm _  | StrTyp _ -> Vernac_classifier.classify_as_sideeff

VERNAC COMMAND EXTEND VernacDeclareTactic2Definition
| [ "Ltac2" ltac2_entry(e) ] => [ classify_ltac2 e ] -> [
    let local = Locality.LocalityFixme.consume () in
    Tac2entries.register_struct ?local e
  ]
END

let _ =
  let mode = {
    Proof_global.name = "Ltac2";
    set = (fun () -> set_command_entry tac2mode);
    reset = (fun () -> set_command_entry Pcoq.Vernac_.noedit_mode);
  } in
  Proof_global.register_proof_mode mode

VERNAC ARGUMENT EXTEND ltac2_expr
PRINTED BY pr_ltac2expr
| [ tac2expr(e) ] -> [ e ]
END

open G_ltac
open Vernac_classifier

VERNAC tac2mode EXTEND VernacLtac2
| [ - ltac2_expr(t) ltac_use_default(default) ] =>
    [ classify_as_proofstep ] -> [
(*     let g = Option.default (Proof_global.get_default_goal_selector ()) g in *)
    Tac2entries.call ~default t
  ]
END

open Stdarg

VERNAC COMMAND EXTEND Ltac2Print CLASSIFIED AS SIDEFF
| [ "Print" "Ltac2" reference(tac) ] -> [ Tac2entries.print_ltac tac ]
END
