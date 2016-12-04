(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Util
open Genarg
open Names
open Pcoq
open Tac2expr
open Ltac_plugin

let tac2expr = Gram.entry_create "tactic:tac2expr"
let tac2type = Gram.entry_create "tactic:tac2type"
let tac2def_val = Gram.entry_create "tactic:tac2def_val"
let tac2def_typ = Gram.entry_create "tactic:tac2def_typ"
let tac2def_ext = Gram.entry_create "tactic:tac2def_ext"
let tac2mode = Gram.entry_create "vernac:ltac2_command"

let inj_wit wit loc x = CTacExt (loc, Genarg.in_gen (Genarg.rawwit wit) x)
let inj_constr loc c = inj_wit Stdarg.wit_constr loc c

GEXTEND Gram
  GLOBAL: tac2expr tac2type tac2def_val tac2def_typ tac2def_ext;
  tac2pat:
    [ "1" LEFTA
      [ id = Prim.qualid; pl = LIST1 tac2pat LEVEL "0" -> CPatRef (!@loc, id, pl)
      | id = Prim.qualid -> CPatRef (!@loc, id, []) ]
    | "0"
      [ "_" -> CPatAny (!@loc)
      | "()" -> CPatTup (!@loc, [])
      | id = Prim.qualid -> CPatRef (!@loc, id, [])
      | "("; pl = LIST0 tac2pat LEVEL "1" SEP ","; ")" -> CPatTup (!@loc, pl) ]
    ]
  ;
  tac2expr:
    [ "5"
      [ "fun"; it = LIST1 input_fun ; "=>"; body = tac2expr LEVEL "5" -> CTacFun (!@loc, it, body)
      | "let"; isrec = rec_flag;
          lc = LIST1 let_clause SEP "with"; "in";
          e = tac2expr LEVEL "5" -> CTacLet (!@loc, isrec, lc, e)
      | "match"; e = tac2expr LEVEL "5"; "with"; bl = branches ;"end" ->
         CTacCse (!@loc, e, bl)
      ]
    | "2" LEFTA
      [ e1 = tac2expr; ";"; e2 = tac2expr -> CTacSeq (!@loc, e1, e2) ]
    | "1" LEFTA
      [ e = tac2expr; el = LIST1 tac2expr LEVEL "0" -> CTacApp (!@loc, e, el)
      | e = SELF; ".("; qid = Prim.qualid; ")" -> CTacPrj (!@loc, e, qid)
      | e = SELF; ".("; qid = Prim.qualid; ")"; ":="; r = tac2expr LEVEL "1" -> CTacSet (!@loc, e, qid, r)
      | e0 = tac2expr; ","; el = LIST1 tac2expr LEVEL "0" SEP "," -> CTacTup (!@loc, e0 :: el) ]
    | "0"
      [ "("; a = tac2expr LEVEL "5"; ")" -> a
      | "("; a = tac2expr; ":"; t = tac2type; ")" -> CTacCnv (!@loc, a, t)
      | "()" -> CTacTup (!@loc, [])
      | "("; ")" -> CTacTup (!@loc, [])
      | "["; a = LIST0 tac2expr LEVEL "1" SEP ";"; "]" -> CTacLst (!@loc, a)
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
  [ [ pat = tac2pat LEVEL "1"; "=>"; e = tac2expr LEVEL "5" -> (pat, e) ] ]
  ;
  rec_flag:
    [ [ IDENT "rec" -> true
      | -> false ] ]
  ;
  typ_param:
    [ [ "'"; id = Prim.ident -> id ] ]
  ;
  tactic_atom:
    [ [ n = Prim.integer -> CTacAtm (!@loc, AtmInt n)
      | s = Prim.string -> CTacAtm (!@loc, AtmStr s)
      | id = Prim.qualid -> CTacRef id
      | IDENT "constr"; ":"; "("; c = Constr.lconstr; ")" -> inj_constr !@loc c
    ] ]
  ;
  let_clause:
    [ [ id = binder; ":="; te = tac2expr ->
         (id, None, te)
      | id = binder; args = LIST1 input_fun; ":="; te = tac2expr ->
         (id, None, CTacFun (!@loc, args, te)) ] ]
  ;
  tac2type:
    [ "5" RIGHTA
      [ t1 = tac2type; "->"; t2 = tac2type -> CTypArrow (!@loc, t1, t2) ]
    | "2"
      [ t = tac2type; "*"; tl = LIST1 tac2type SEP "*" -> CTypTuple (!@loc, t :: tl) ]
    | "1"
      [ "("; p = LIST1 tac2type LEVEL "5" SEP ","; ")"; qid = Prim.qualid -> CTypRef (!@loc, qid, p) ]
    | "0"
      [ "("; t = tac2type; ")"  -> t
      | id = typ_param -> CTypVar (!@loc, Name id)
      | "_" -> CTypVar (!@loc, Anonymous)
      | qid = Prim.qualid -> CTypRef (!@loc, qid, []) ]
    ];
  locident:
    [ [ id = Prim.ident -> (!@loc, id) ] ]
  ;
  binder:
    [ [ "_" -> (!@loc, Anonymous)
      | l = Prim.ident -> (!@loc, Name l) ] ]
  ;
  input_fun:
    [ [ b = binder -> (b, None)
      | "("; b = binder; ":"; t = tac2type; ")" -> (b, Some t) ] ]
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
    [ [ qid = Prim.qualid; ":="; e = tac2expr LEVEL "1" -> qid, e ] ]
  ;
  tac2typ_prm:
    [ [ -> []
      | id = typ_param -> [!@loc, id]
      | "("; ids = LIST1 [ id = typ_param -> (!@loc, id) ] SEP "," ;")" -> ids
    ] ]
  ;
  tac2typ_def:
    [ [ prm = tac2typ_prm; id = locident; ":="; e = tac2typ_knd ->
        (id, (prm, e))
      | prm = tac2typ_prm; id = locident -> (id, (prm, CTydDef None))
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
END

let pr_ltac2entry _ = mt () (** FIXME *)
let pr_ltac2expr _ = mt () (** FIXME *)

VERNAC ARGUMENT EXTEND ltac2_entry
PRINTED BY pr_ltac2entry
| [ tac2def_val(v) ] -> [ v ]
| [ tac2def_typ(t) ] -> [ t ]
| [ tac2def_ext(e) ] -> [ e ]
END

VERNAC COMMAND EXTEND VernacDeclareTactic2Definition CLASSIFIED AS SIDEFF
| [ "Ltac2" ltac2_entry(e) ] -> [
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
