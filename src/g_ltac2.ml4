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
open Tac2expr
open Tac2qexpr
open Ltac_plugin

let err () = raise Stream.Failure

type lookahead = int -> Tok.t Stream.t -> int option

let entry_of_lookahead s (lk : lookahead) =
  let run strm = match lk 0 strm with None -> err () | Some _ -> () in
  Gram.Entry.of_parser s run

let (>>) (lk1 : lookahead) lk2 n strm = match lk1 n strm with
| None -> None
| Some n -> lk2 n strm

let (<+>) (lk1 : lookahead) lk2 n strm = match lk1 n strm with
| None -> lk2 n strm
| Some n -> Some n

let lk_kw kw n strm = match stream_nth n strm with
| KEYWORD kw' | IDENT kw' -> if String.equal kw kw' then Some (n + 1) else None
| _ -> None

let lk_ident n strm = match stream_nth n strm with
| IDENT _ -> Some (n + 1)
| _ -> None

let lk_int n strm = match stream_nth n strm with
| INT _ -> Some (n + 1)
| _ -> None

let lk_ident_or_anti = lk_ident <+> (lk_kw "$" >> lk_ident)

(* lookahead for (x:=t), (?x:=t) and (1:=t) *)
let test_lpar_idnum_coloneq =
  entry_of_lookahead "test_lpar_idnum_coloneq" begin
    lk_kw "(" >> (lk_ident_or_anti <+> lk_int) >> lk_kw ":="
  end

(* lookahead for (x:t), (?x:t) *)
let test_lpar_id_colon =
  entry_of_lookahead "test_lpar_id_colon" begin
    lk_kw "(" >> lk_ident_or_anti >> lk_kw ":"
  end

(* Hack to recognize "(x := t)" and "($x := t)" *)
let test_lpar_id_coloneq =
  entry_of_lookahead "test_lpar_id_coloneq" begin
    lk_kw "(" >> lk_ident_or_anti >> lk_kw ":="
  end

(* Hack to recognize "(x)" *)
let test_lpar_id_rpar =
  entry_of_lookahead "test_lpar_id_rpar" begin
    lk_kw "(" >> lk_ident >> lk_kw ")"
  end

let test_ampersand_ident =
  entry_of_lookahead "test_ampersand_ident" begin
    lk_kw "&" >> lk_ident
  end

let test_dollar_ident =
  entry_of_lookahead "test_dollar_ident" begin
    lk_kw "$" >> lk_ident
  end

let tac2expr = Tac2entries.Pltac.tac2expr
let tac2type = Entry.create "tactic:tac2type"
let tac2def_val = Entry.create "tactic:tac2def_val"
let tac2def_typ = Entry.create "tactic:tac2def_typ"
let tac2def_ext = Entry.create "tactic:tac2def_ext"
let tac2def_syn = Entry.create "tactic:tac2def_syn"
let tac2def_mut = Entry.create "tactic:tac2def_mut"
let tac2def_run = Entry.create "tactic:tac2def_run"
let tac2mode = Entry.create "vernac:ltac2_command"

let ltac1_expr = Pltac.tactic_expr

let inj_wit wit loc x = CAst.make ~loc @@ CTacExt (wit, x)
let inj_open_constr loc c = inj_wit Tac2quote.wit_open_constr loc c
let inj_pattern loc c = inj_wit Tac2quote.wit_pattern loc c
let inj_reference loc c = inj_wit Tac2quote.wit_reference loc c
let inj_ltac1 loc e = inj_wit Tac2quote.wit_ltac1 loc e

let pattern_of_qualid qid =
  if Tac2env.is_constructor qid then CAst.make ?loc:qid.CAst.loc @@ CPatRef (RelId qid, [])
  else
    let open Libnames in
    if qualid_is_ident qid then CAst.make ?loc:qid.CAst.loc @@ CPatVar (Name (qualid_basename qid))
    else
      CErrors.user_err ?loc:qid.CAst.loc (Pp.str "Syntax error")

GEXTEND Gram
  GLOBAL: tac2expr tac2type tac2def_val tac2def_typ tac2def_ext tac2def_syn
          tac2def_mut tac2def_run;
  tac2pat:
    [ "1" LEFTA
      [ qid = Prim.qualid; pl = LIST1 tac2pat LEVEL "0" ->
        if Tac2env.is_constructor qid then
          CAst.make ~loc:!@loc @@ CPatRef (RelId qid, pl)
        else
          CErrors.user_err ~loc:!@loc (Pp.str "Syntax error")
      | qid = Prim.qualid -> pattern_of_qualid qid
      | "["; "]" -> CAst.make ~loc:!@loc @@ CPatRef (AbsKn (Other Tac2core.Core.c_nil), [])
      | p1 = tac2pat; "::"; p2 = tac2pat ->
        CAst.make ~loc:!@loc @@ CPatRef (AbsKn (Other Tac2core.Core.c_cons), [p1; p2])
      ]
    | "0"
      [ "_" -> CAst.make ~loc:!@loc @@ CPatVar Anonymous
      | "()" -> CAst.make ~loc:!@loc @@ CPatRef (AbsKn (Tuple 0), [])
      | qid = Prim.qualid -> pattern_of_qualid qid
      | "("; p = atomic_tac2pat; ")" -> p
    ] ]
  ;
  atomic_tac2pat:
    [ [ ->
        CAst.make ~loc:!@loc @@ CPatRef (AbsKn (Tuple 0), [])
      | p = tac2pat; ":"; t = tac2type ->
        CAst.make ~loc:!@loc @@ CPatCnv (p, t)
      | p = tac2pat; ","; pl = LIST0 tac2pat SEP "," ->
        let pl = p :: pl in
        CAst.make ~loc:!@loc @@ CPatRef (AbsKn (Tuple (List.length pl)), pl)
      | p = tac2pat -> p
    ] ]
  ;
  tac2expr:
    [ "6" RIGHTA
        [ e1 = SELF; ";"; e2 = SELF -> CAst.make ~loc:!@loc @@ CTacSeq (e1, e2) ]
    | "5"
      [ "fun"; it = LIST1 input_fun ; "=>"; body = tac2expr LEVEL "6" ->
        CAst.make ~loc:!@loc @@ CTacFun (it, body)
      | "let"; isrec = rec_flag;
          lc = LIST1 let_clause SEP "with"; "in";
          e = tac2expr LEVEL "6" ->
        CAst.make ~loc:!@loc @@ CTacLet (isrec, lc, e)
      | "match"; e = tac2expr LEVEL "5"; "with"; bl = branches; "end" ->
        CAst.make ~loc:!@loc @@ CTacCse (e, bl)
      ]
    | "4" LEFTA [ ]
    | "::" RIGHTA
      [ e1 = tac2expr; "::"; e2 = tac2expr ->
        CAst.make ~loc:!@loc @@ CTacApp (CAst.make ~loc:!@loc @@ CTacCst (AbsKn (Other Tac2core.Core.c_cons)), [e1; e2])
      ]
    | [ e0 = SELF; ","; el = LIST1 NEXT SEP "," ->
        let el = e0 :: el in
        CAst.make ~loc:!@loc @@ CTacApp (CAst.make ~loc:!@loc @@ CTacCst (AbsKn (Tuple (List.length el))), el) ]
    | "1" LEFTA
      [ e = tac2expr; el = LIST1 tac2expr LEVEL "0" ->
        CAst.make ~loc:!@loc @@ CTacApp (e, el)
      | e = SELF; ".("; qid = Prim.qualid; ")" ->
        CAst.make ~loc:!@loc @@ CTacPrj (e, RelId qid)
      | e = SELF; ".("; qid = Prim.qualid; ")"; ":="; r = tac2expr LEVEL "5" ->
        CAst.make ~loc:!@loc @@ CTacSet (e, RelId qid, r) ]
    | "0"
      [ "("; a = SELF; ")" -> a
      | "("; a = SELF; ":"; t = tac2type; ")" ->
        CAst.make ~loc:!@loc @@ CTacCnv (a, t)
      | "()" ->
        CAst.make ~loc:!@loc @@ CTacCst (AbsKn (Tuple 0))
      | "("; ")" ->
        CAst.make ~loc:!@loc @@ CTacCst (AbsKn (Tuple 0))
      | "["; a = LIST0 tac2expr LEVEL "5" SEP ";"; "]" ->
        Tac2quote.of_list ~loc:!@loc (fun x -> x) a
      | "{"; a = tac2rec_fieldexprs; "}" ->
        CAst.make ~loc:!@loc @@ CTacRec a
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
  mut_flag:
    [ [ IDENT "mutable" -> true
      | -> false ] ]
  ;
  typ_param:
    [ [ "'"; id = Prim.ident -> id ] ]
  ;
  tactic_atom:
    [ [ n = Prim.integer -> CAst.make ~loc:!@loc @@ CTacAtm (AtmInt n)
      | s = Prim.string -> CAst.make ~loc:!@loc @@ CTacAtm (AtmStr s)
      | qid = Prim.qualid ->
        if Tac2env.is_constructor qid then
          CAst.make ~loc:!@loc @@ CTacCst (RelId qid)
        else
          CAst.make ~loc:!@loc @@ CTacRef (RelId qid)
      | "@"; id = Prim.ident -> Tac2quote.of_ident (CAst.make ~loc:!@loc id)
      | "&"; id = lident -> Tac2quote.of_hyp ~loc:!@loc id
      | "'"; c = Constr.constr -> inj_open_constr !@loc c
      | IDENT "constr"; ":"; "("; c = Constr.lconstr; ")" -> Tac2quote.of_constr c
      | IDENT "open_constr"; ":"; "("; c = Constr.lconstr; ")" -> Tac2quote.of_open_constr c
      | IDENT "ident"; ":"; "("; c = lident; ")" -> Tac2quote.of_ident c
      | IDENT "pattern"; ":"; "("; c = Constr.lconstr_pattern; ")" -> inj_pattern !@loc c
      | IDENT "reference"; ":"; "("; c = globref; ")" -> inj_reference !@loc c
      | IDENT "ltac1"; ":"; "("; qid = ltac1_expr; ")" -> inj_ltac1 !@loc qid
    ] ]
  ;
  let_clause:
    [ [ binder = let_binder; ":="; te = tac2expr ->
        let (pat, fn) = binder in
        let te = match fn with
        | None -> te
        | Some args -> CAst.make ~loc:!@loc @@ CTacFun (args, te)
        in
        (pat, te)
    ] ]
  ;
  let_binder:
    [ [ pats = LIST1 input_fun ->
        match pats with
        | [{CAst.v=CPatVar _} as pat] -> (pat, None)
        | ({CAst.v=CPatVar (Name id)} as pat) :: args -> (pat, Some args)
        | [pat] -> (pat, None)
        | _ -> CErrors.user_err ~loc:!@loc (str "Invalid pattern")
    ] ]
  ;
  tac2type:
    [ "5" RIGHTA
      [ t1 = tac2type; "->"; t2 = tac2type -> CAst.make ~loc:!@loc @@ CTypArrow (t1, t2) ]
    | "2"
      [ t = tac2type; "*"; tl = LIST1 tac2type LEVEL "1" SEP "*" ->
        let tl = t :: tl in
        CAst.make ~loc:!@loc @@ CTypRef (AbsKn (Tuple (List.length tl)), tl) ]
    | "1" LEFTA
      [ t = SELF; qid = Prim.qualid -> CAst.make ~loc:!@loc @@ CTypRef (RelId qid, [t]) ]
    | "0"
      [ "("; t = tac2type LEVEL "5"; ")"  -> t
      | id = typ_param -> CAst.make ~loc:!@loc @@ CTypVar (Name id)
      | "_" -> CAst.make ~loc:!@loc @@ CTypVar Anonymous
      | qid = Prim.qualid -> CAst.make ~loc:!@loc @@ CTypRef (RelId qid, [])
      | "("; p = LIST1 tac2type LEVEL "5" SEP ","; ")"; qid = Prim.qualid ->
        CAst.make ~loc:!@loc @@ CTypRef (RelId qid, p) ]
    ];
  locident:
    [ [ id = Prim.ident -> CAst.make ~loc:!@loc id ] ]
  ;
  binder:
    [ [ "_" -> CAst.make ~loc:!@loc Anonymous
      | l = Prim.ident -> CAst.make ~loc:!@loc (Name l) ] ]
  ;
  input_fun:
    [ [ b = tac2pat LEVEL "0" -> b ] ]
  ;
  tac2def_body:
    [ [ name = binder; it = LIST0 input_fun; ":="; e = tac2expr ->
        let e = if List.is_empty it then e else CAst.make ~loc:!@loc @@ CTacFun (it, e) in
        (name, e)
    ] ]
  ;
  tac2def_val:
    [ [ mut = mut_flag; isrec = rec_flag; l = LIST1 tac2def_body SEP "with" ->
        StrVal (mut, isrec, l)
    ] ]
  ;
  tac2def_mut:
    [ [ "Set"; qid = Prim.qualid; ":="; e = tac2expr -> StrMut (qid, e) ] ]
  ;
  tac2def_run:
    [ [ "Eval"; e = tac2expr -> StrRun e ] ]
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
    [ [ mut = mut_flag; id = Prim.ident; ":"; t = tac2type -> (id, mut, t) ] ]
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
      | id = typ_param -> [CAst.make ~loc:!@loc id]
      | "("; ids = LIST1 [ id = typ_param -> CAst.make ~loc:!@loc id ] SEP "," ;")" -> ids
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
    [ [ "_" -> CAst.make ~loc:!@loc None
      | id = Prim.ident -> CAst.make ~loc:!@loc (Some id)
    ] ]
  ;
  sexpr:
    [ [ s = Prim.string -> SexprStr (CAst.make ~loc:!@loc s)
      | n = Prim.integer -> SexprInt (CAst.make ~loc:!@loc n)
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
    [ [ id = Prim.ident -> CAst.make ~loc:!@loc id ] ]
  ;
  globref:
    [ [ "&"; id = Prim.ident -> CAst.make ~loc:!@loc (QHypothesis id)
      | qid = Prim.qualid -> CAst.make ~loc:!@loc @@ QReference qid
    ] ]
  ;
END

(** Quotation scopes used by notations *)

open Tac2entries.Pltac

let loc_of_ne_list l = Loc.merge_opt (fst (List.hd l)) (fst (List.last l))

GEXTEND Gram
  GLOBAL: q_ident q_bindings q_intropattern q_intropatterns q_induction_clause
          q_conversion q_rewriting q_clause q_dispatch q_occurrences q_strategy_flag
          q_destruction_arg q_reference q_with_bindings q_constr_matching
          q_goal_matching q_hintdb q_move_location q_pose q_assert;
  anti:
    [ [ "$"; id = Prim.ident -> QAnti (CAst.make ~loc:!@loc id) ] ]
  ;
  ident_or_anti:
    [ [ id = lident -> QExpr id
      | "$"; id = Prim.ident -> QAnti (CAst.make ~loc:!@loc id)
    ] ]
  ;
  lident:
    [ [ id = Prim.ident -> CAst.make ~loc:!@loc id ] ]
  ;
  lnatural:
    [ [ n = Prim.natural -> CAst.make ~loc:!@loc n ] ]
  ;
  q_ident:
    [ [ id = ident_or_anti -> id ] ]
  ;
  qhyp:
    [ [ x = anti -> x
      | n = lnatural -> QExpr (CAst.make ~loc:!@loc @@ QAnonHyp n)
      | id = lident -> QExpr (CAst.make ~loc:!@loc @@ QNamedHyp id)
    ] ]
  ;
  simple_binding:
    [ [ "("; h = qhyp; ":="; c = Constr.lconstr; ")" ->
        CAst.make ~loc:!@loc (h, c)
    ] ]
  ;
  bindings:
    [ [ test_lpar_idnum_coloneq; bl = LIST1 simple_binding ->
        CAst.make ~loc:!@loc @@ QExplicitBindings bl
      | bl = LIST1 Constr.constr ->
        CAst.make ~loc:!@loc @@ QImplicitBindings bl
    ] ]
  ;
  q_bindings:
    [ [ bl = bindings -> bl ] ]
  ;
  q_with_bindings:
    [ [ bl = with_bindings -> bl ] ]
  ;
  intropatterns:
    [ [ l = LIST0 nonsimple_intropattern -> CAst.make ~loc:!@loc l ]]
  ;
(*   ne_intropatterns: *)
(*     [ [ l = LIST1 nonsimple_intropattern -> l ]] *)
(*   ; *)
  or_and_intropattern:
    [ [ "["; tc = LIST1 intropatterns SEP "|"; "]" -> CAst.make ~loc:!@loc @@ QIntroOrPattern tc
      | "()" -> CAst.make ~loc:!@loc @@ QIntroAndPattern (CAst.make ~loc:!@loc [])
      | "("; si = simple_intropattern; ")" -> CAst.make ~loc:!@loc @@ QIntroAndPattern (CAst.make ~loc:!@loc [si])
      | "("; si = simple_intropattern; ",";
             tc = LIST1 simple_intropattern SEP "," ; ")" ->
             CAst.make ~loc:!@loc @@ QIntroAndPattern (CAst.make ~loc:!@loc (si::tc))
      | "("; si = simple_intropattern; "&";
	     tc = LIST1 simple_intropattern SEP "&" ; ")" ->
	  (* (A & B & C) is translated into (A,(B,C)) *)
	  let rec pairify = function
	    | ([]|[_]|[_;_]) as l -> CAst.make ~loc:!@loc l
	    | t::q ->
              let q =
                CAst.make ~loc:!@loc @@
                  QIntroAction (CAst.make ~loc:!@loc @@
                    QIntroOrAndPattern (CAst.make ~loc:!@loc @@
                      QIntroAndPattern (pairify q)))
              in
              CAst.make ~loc:!@loc [t; q]
	  in CAst.make ~loc:!@loc @@ QIntroAndPattern (pairify (si::tc)) ] ]
  ;
  equality_intropattern:
    [ [ "->" -> CAst.make ~loc:!@loc @@ QIntroRewrite true
      | "<-" -> CAst.make ~loc:!@loc @@ QIntroRewrite false
      | "[="; tc = intropatterns; "]" -> CAst.make ~loc:!@loc @@ QIntroInjection tc ] ]
  ;
  naming_intropattern:
    [ [ LEFTQMARK; id = lident ->
        CAst.make ~loc:!@loc @@ QIntroFresh (QExpr id)
      | "?$"; id = lident ->
        CAst.make ~loc:!@loc @@ QIntroFresh (QAnti id)
      | "?" ->
        CAst.make ~loc:!@loc @@ QIntroAnonymous
      | id = ident_or_anti ->
        CAst.make ~loc:!@loc @@ QIntroIdentifier id
    ] ]
  ;
  nonsimple_intropattern:
    [ [ l = simple_intropattern -> l
      | "*"  -> CAst.make ~loc:!@loc @@ QIntroForthcoming true
      | "**" -> CAst.make ~loc:!@loc @@ QIntroForthcoming false ]]
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
        CAst.make ~loc:!@loc @@ QIntroAction (CAst.make ~loc:!@loc @@ QIntroOrAndPattern pat)
      | pat = equality_intropattern ->
        CAst.make ~loc:!@loc @@ QIntroAction pat
      | "_" ->
        CAst.make ~loc:!@loc @@ QIntroAction (CAst.make ~loc:!@loc @@ QIntroWildcard)
      | pat = naming_intropattern ->
        CAst.make ~loc:!@loc @@ QIntroNaming pat
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
      | "$"; id = Prim.ident -> QAnti (CAst.make ~loc:!@loc id)
    ] ]
  ;
  eqn_ipat:
    [ [ IDENT "eqn"; ":"; pat = naming_intropattern -> Some pat
      | -> None
    ] ]
  ;
  with_bindings:
    [ [ "with"; bl = bindings -> bl | -> CAst.make ~loc:!@loc @@ QNoBindings ] ]
  ;
  constr_with_bindings:
    [ [ c = Constr.constr; l = with_bindings -> CAst.make ~loc:!@loc @@ (c, l) ] ]
  ;
  destruction_arg:
    [ [ n = lnatural -> CAst.make ~loc:!@loc @@ QElimOnAnonHyp n
      | id = lident -> CAst.make ~loc:!@loc @@ QElimOnIdent id
      | c = constr_with_bindings -> CAst.make ~loc:!@loc @@ QElimOnConstr c
    ] ]
  ;
  q_destruction_arg:
    [ [ arg = destruction_arg -> arg ] ]
  ;
  as_or_and_ipat:
    [ [ "as"; ipat = or_and_intropattern -> Some ipat
      | -> None
    ] ]
  ;
  occs_nums:
    [ [ nl = LIST1 nat_or_anti -> CAst.make ~loc:!@loc @@ QOnlyOccurrences nl
      | "-"; n = nat_or_anti; nl = LIST0 nat_or_anti ->
        CAst.make ~loc:!@loc @@ QAllOccurrencesBut (n::nl)
    ] ]
  ;
  occs:
    [ [ "at"; occs = occs_nums -> occs | -> CAst.make ~loc:!@loc QAllOccurrences ] ]
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
        { q_onhyps = Some hl; q_concl_occs = CAst.make ~loc:!@loc QNoOccurrences }
    ] ]
  ;
  clause:
    [ [ "in"; cl = in_clause -> CAst.make ~loc:!@loc @@ cl
      | "at"; occs = occs_nums ->
        CAst.make ~loc:!@loc @@ { q_onhyps = Some []; q_concl_occs = occs }
    ] ]
  ;
  q_clause:
    [ [ cl = clause -> cl ] ]
  ;
  concl_occ:
    [ [ "*"; occs = occs -> occs
      | -> CAst.make ~loc:!@loc QNoOccurrences
    ] ]
  ;
  induction_clause:
    [ [ c = destruction_arg; pat = as_or_and_ipat; eq = eqn_ipat;
        cl = OPT clause ->
        CAst.make ~loc:!@loc @@ {
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
  conversion:
    [ [ c = Constr.constr ->
        CAst.make ~loc:!@loc @@ QConvert c
      | c1 = Constr.constr; "with"; c2 = Constr.constr ->
        CAst.make ~loc:!@loc @@ QConvertWith (c1, c2)
    ] ]
  ;
  q_conversion:
    [ [ c = conversion -> c ] ]
  ;
  orient:
    [ [ "->" -> CAst.make ~loc:!@loc (Some true)
      | "<-" -> CAst.make ~loc:!@loc (Some false)
      | -> CAst.make ~loc:!@loc None
    ]]
  ;
  rewriter:
    [ [ "!"; c = constr_with_bindings ->
        (CAst.make ~loc:!@loc @@ QRepeatPlus,c)
      | ["?"| LEFTQMARK]; c = constr_with_bindings ->
        (CAst.make ~loc:!@loc @@ QRepeatStar,c)
      | n = lnatural; "!"; c = constr_with_bindings ->
        (CAst.make ~loc:!@loc @@ QPrecisely n,c)
      |	n = lnatural; ["?" | LEFTQMARK]; c = constr_with_bindings ->
        (CAst.make ~loc:!@loc @@ QUpTo n,c)
      | n = lnatural; c = constr_with_bindings ->
        (CAst.make ~loc:!@loc @@ QPrecisely n,c)
      | c = constr_with_bindings ->
        (CAst.make ~loc:!@loc @@ QPrecisely (CAst.make 1), c)
      ] ]
  ;
  oriented_rewriter:
    [ [ b = orient; (m, c) = rewriter ->
      CAst.make ~loc:!@loc @@ {
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
    [ [ d = tactic_then_gen -> CAst.make ~loc:!@loc d ] ]
  ;
  q_occurrences:
    [ [ occs = occs -> occs ] ]
  ;
  red_flag:
    [ [ IDENT "beta" -> CAst.make ~loc:!@loc @@ QBeta
      | IDENT "iota" -> CAst.make ~loc:!@loc @@ QIota
      | IDENT "match" -> CAst.make ~loc:!@loc @@ QMatch
      | IDENT "fix" -> CAst.make ~loc:!@loc @@ QFix
      | IDENT "cofix" -> CAst.make ~loc:!@loc @@ QCofix
      | IDENT "zeta" -> CAst.make ~loc:!@loc @@ QZeta
      | IDENT "delta"; d = delta_flag -> d
    ] ]
  ;
  refglobal:
    [ [ "&"; id = Prim.ident -> QExpr (CAst.make ~loc:!@loc @@ QHypothesis id)
      | qid = Prim.qualid -> QExpr (CAst.make ~loc:!@loc @@ QReference qid)
      | "$"; id = Prim.ident -> QAnti (CAst.make ~loc:!@loc id)
    ] ]
  ;
  q_reference:
    [ [ r = refglobal -> r ] ]
  ;
  refglobals:
    [ [ gl = LIST1 refglobal -> CAst.make ~loc:!@loc gl ] ]
  ;
  delta_flag:
    [ [ "-"; "["; idl = refglobals; "]" -> CAst.make ~loc:!@loc @@ QDeltaBut idl
      | "["; idl = refglobals; "]" -> CAst.make ~loc:!@loc @@ QConst idl
      | -> CAst.make ~loc:!@loc @@ QDeltaBut (CAst.make ~loc:!@loc [])
    ] ]
  ;
  strategy_flag:
    [ [ s = LIST1 red_flag -> CAst.make ~loc:!@loc s
      | d = delta_flag ->
        CAst.make ~loc:!@loc
          [CAst.make ~loc:!@loc QBeta; CAst.make ~loc:!@loc QIota; CAst.make ~loc:!@loc QZeta; d]
    ] ]
  ;
  q_strategy_flag:
    [ [ flag = strategy_flag -> flag ] ]
  ;
  hintdb:
    [ [ "*" -> CAst.make ~loc:!@loc @@ QHintAll
      | l = LIST1 ident_or_anti -> CAst.make ~loc:!@loc @@ QHintDbs l
    ] ]
  ;
  q_hintdb:
    [ [ db = hintdb -> db ] ]
  ;
  match_pattern:
    [ [ IDENT "context";  id = OPT Prim.ident;
          "["; pat = Constr.lconstr_pattern; "]" -> CAst.make ~loc:!@loc @@ QConstrMatchContext (id, pat)
      | pat = Constr.lconstr_pattern -> CAst.make ~loc:!@loc @@ QConstrMatchPattern pat ] ]
  ;
  match_rule:
    [ [ mp = match_pattern; "=>"; tac = tac2expr ->
        CAst.make ~loc:!@loc @@ (mp, tac)
    ] ]
  ;
  match_list:
    [ [ mrl = LIST1 match_rule SEP "|" -> CAst.make ~loc:!@loc @@ mrl
      | "|"; mrl = LIST1 match_rule SEP "|" -> CAst.make ~loc:!@loc @@ mrl ] ]
  ;
  q_constr_matching:
    [ [ m = match_list -> m ] ]
  ;
  gmatch_hyp_pattern:
    [ [ na = Prim.name; ":"; pat = match_pattern -> (na, pat) ] ]
  ;
  gmatch_pattern:
    [ [ "["; hl = LIST0 gmatch_hyp_pattern SEP ","; "|-"; p = match_pattern; "]" ->
        CAst.make ~loc:!@loc @@ {
          q_goal_match_concl = p;
          q_goal_match_hyps = hl;
        }
    ] ]
  ;
  gmatch_rule:
    [ [ mp = gmatch_pattern; "=>"; tac = tac2expr ->
        CAst.make ~loc:!@loc @@ (mp, tac)
    ] ]
  ;
  gmatch_list:
    [ [ mrl = LIST1 gmatch_rule SEP "|" -> CAst.make ~loc:!@loc @@ mrl
      | "|"; mrl = LIST1 gmatch_rule SEP "|" -> CAst.make ~loc:!@loc @@ mrl ] ]
  ;
  q_goal_matching:
    [ [ m = gmatch_list -> m ] ]
  ;
  move_location:
    [ [ "at"; IDENT "top" -> CAst.make ~loc:!@loc @@ QMoveFirst
      | "at"; IDENT "bottom" -> CAst.make ~loc:!@loc @@ QMoveLast
      | IDENT "after"; id = ident_or_anti -> CAst.make ~loc:!@loc @@ QMoveAfter id
      | IDENT "before"; id = ident_or_anti -> CAst.make ~loc:!@loc @@ QMoveBefore id
    ] ]
  ;
  q_move_location:
    [ [ mv = move_location -> mv ] ]
  ;
  as_name:
    [ [ -> None
      | "as"; id = ident_or_anti -> Some id
    ] ]
  ;
  pose:
    [ [ test_lpar_id_coloneq; "("; id = ident_or_anti; ":="; c = Constr.lconstr; ")" ->
        CAst.make ~loc:!@loc (Some id, c)
      | c = Constr.constr; na = as_name -> CAst.make ~loc:!@loc (na, c)
    ] ]
  ;
  q_pose:
    [ [ p = pose -> p ] ]
  ;
  as_ipat:
    [ [ "as"; ipat = simple_intropattern -> Some ipat
      | -> None
    ] ]
  ;
  by_tactic:
    [ [ "by"; tac = tac2expr -> Some tac
      | -> None
    ] ]
  ;
  assertion:
    [ [ test_lpar_id_coloneq; "("; id = ident_or_anti; ":="; c = Constr.lconstr; ")" ->
        CAst.make ~loc:!@loc (QAssertValue (id, c))
      | test_lpar_id_colon; "("; id = ident_or_anti; ":"; c = Constr.lconstr; ")"; tac = by_tactic ->
        let loc = !@loc in
        let ipat = CAst.make ~loc @@ QIntroNaming (CAst.make ~loc @@ QIntroIdentifier id) in
        CAst.make ~loc (QAssertType (Some ipat, c, tac))
      | c = Constr.constr; ipat = as_ipat; tac = by_tactic ->
        CAst.make ~loc:!@loc (QAssertType (ipat, c, tac))
    ] ]
  ;
  q_assert:
    [ [ a = assertion -> a ] ]
  ;
END

(** Extension of constr syntax *)

let () = Hook.set Tac2entries.register_constr_quotations begin fun () ->
GEXTEND Gram
  Pcoq.Constr.operconstr: LEVEL "0"
    [ [ IDENT "ltac2"; ":"; "("; tac = tac2expr; ")" ->
        let arg = Genarg.in_gen (Genarg.rawwit Tac2env.wit_ltac2) tac in
        CAst.make ~loc:!@loc (CHole (None, Namegen.IntroAnonymous, Some arg))
      | test_ampersand_ident; "&"; id = Prim.ident ->
        let tac = Tac2quote.of_exact_hyp ~loc:!@loc (CAst.make ~loc:!@loc id) in
        let arg = Genarg.in_gen (Genarg.rawwit Tac2env.wit_ltac2) tac in
        CAst.make ~loc:!@loc (CHole (None, Namegen.IntroAnonymous, Some arg))
      | test_dollar_ident; "$"; id = Prim.ident ->
        let id = Loc.tag ~loc:!@loc id in
        let arg = Genarg.in_gen (Genarg.rawwit Tac2env.wit_ltac2_quotation) id in
        CAst.make ~loc:!@loc (CHole (None, Namegen.IntroAnonymous, Some arg))
    ] ]
  ;
END
end

let pr_ltac2entry _ = mt () (** FIXME *)
let pr_ltac2expr _ = mt () (** FIXME *)

VERNAC ARGUMENT EXTEND ltac2_entry
PRINTED BY pr_ltac2entry
| [ tac2def_val(v) ] -> [ v ]
| [ tac2def_typ(t) ] -> [ t ]
| [ tac2def_ext(e) ] -> [ e ]
| [ tac2def_syn(e) ] -> [ e ]
| [ tac2def_mut(e) ] -> [ e ]
| [ tac2def_run(e) ] -> [ e ]
END

let classify_ltac2 = function
| StrSyn _ -> Vernacexpr.VtUnknown, Vernacexpr.VtNow
| StrMut _ | StrVal _ | StrPrm _  | StrTyp _ | StrRun _ -> Vernac_classifier.classify_as_sideeff

VERNAC COMMAND FUNCTIONAL EXTEND VernacDeclareTactic2Definition
| [ "Ltac2" ltac2_entry(e) ] => [ classify_ltac2 e ] -> [
    fun ~atts ~st -> let open Vernacinterp in
    Tac2entries.register_struct ?local:atts.locality e;
    st
  ]
END

let _ =
  let mode = {
    Proof_global.name = "Ltac2";
    set = (fun () -> Pvernac.set_command_entry tac2mode);
    reset = (fun () -> Pvernac.(set_command_entry Vernac_.noedit_mode));
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
