(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Coqast
open Extend
open Ppextend
open Vernacexpr
open Pcoq
open Vernac_
open Goptions
open Constr
open Prim

GEXTEND Gram
  GLOBAL: class_rawexpr;

  class_rawexpr:
    [ [ IDENT "FUNCLASS" -> FunClass
      | IDENT "SORTCLASS" -> SortClass
      | qid = global -> RefClass qid ] ]
  ;
END;

GEXTEND Gram
  GLOBAL: command;

  comment:
    [ [ c = constr -> CommentConstr c
      | s = STRING -> CommentString s
      | n = natural -> CommentInt n ] ]
  ;
  command:
    [ [ IDENT "Comments"; l = LIST0 comment -> VernacComments l

      (* System directory *)
      | IDENT "Pwd" -> VernacChdir None
      | IDENT "Cd" -> VernacChdir None
      | IDENT "Cd"; dir = STRING -> VernacChdir (Some dir)

      (* Toplevel control *)
      | IDENT "Drop" -> VernacToplevelControl Drop
      | IDENT "ProtectedLoop" -> VernacToplevelControl ProtectedLoop
      | "Quit" -> VernacToplevelControl Quit

      (* Dump of the universe graph - to file or to stdout *) 
      | IDENT "Dump"; IDENT "Universes"; fopt = OPT STRING ->
	  VernacPrint (PrintUniverses fopt)

      | IDENT "Locate"; qid = global -> VernacLocate (LocateTerm qid)
      | IDENT "Locate"; IDENT "File"; f = STRING -> VernacLocate (LocateFile f)
      | IDENT "Locate"; IDENT "Library"; qid = global ->
	  VernacLocate (LocateLibrary  qid)

      (* Managing load paths *)
      | IDENT "Add"; IDENT "LoadPath"; dir = STRING; alias = as_dirpath ->
	  VernacAddLoadPath (false, dir, alias)
      | IDENT "Add"; IDENT "Rec"; IDENT "LoadPath"; dir = STRING; 
	  alias = as_dirpath -> VernacAddLoadPath (true, dir, alias)
      | IDENT "Remove"; IDENT "LoadPath"; dir = STRING ->
	  VernacRemoveLoadPath dir

       (* For compatibility *)
      | IDENT "AddPath"; dir = STRING; "as"; alias = as_dirpath ->
	  VernacAddLoadPath (false, dir, alias)
      | IDENT "AddRecPath"; dir = STRING; "as"; alias = as_dirpath ->
	  VernacAddLoadPath (true, dir, alias)
      | IDENT "DelPath"; dir = STRING ->
	  VernacRemoveLoadPath dir

      (* Printing (careful factorization of entries) *)
      | IDENT "Print"; p = printable -> VernacPrint p
      | IDENT "Print"; qid = global -> VernacPrint (PrintName qid)
      | IDENT "Print" -> VernacPrint PrintLocalContext 
      | IDENT "Print"; IDENT "Module"; "Type"; qid = global -> 
	  VernacPrint (PrintModuleType qid)
      | IDENT "Print"; IDENT "Module"; qid = global -> 
	  VernacPrint (PrintModule qid)
      | IDENT "Inspect"; n = natural -> VernacPrint (PrintInspect n)

      (* Searching the environment *)
      | IDENT "Search"; qid = global; l = in_or_out_modules -> 
	  VernacSearch (SearchHead qid, l)
      | IDENT "SearchPattern"; c = constr_pattern; l = in_or_out_modules ->
	  VernacSearch (SearchPattern c, l)
      | IDENT "SearchRewrite"; c = constr_pattern; l = in_or_out_modules ->
	  VernacSearch (SearchRewrite c, l)

      (* TODO: rapprocher Eval et Check *)
      | IDENT "Eval"; r = Tactic.red_expr; "in";
	  c = constr -> VernacCheckMayEval (Some r, None, c)
      | IDENT "Check"; c = constr ->
	  VernacCheckMayEval (None, None, c)
      | "Type"; c = constr -> VernacGlobalCheck c      (* pas dans le RefMan *)

      | IDENT "Add"; IDENT "ML"; IDENT "Path"; dir = STRING ->
	  VernacAddMLPath (false, dir)
      | IDENT "Add"; IDENT "Rec"; IDENT "ML"; IDENT "Path"; dir = STRING ->
	  VernacAddMLPath (true, dir)
(*
      | IDENT "SearchIsos"; c = constr -> VernacSearch (SearchIsos c)
*)

      (* Pour intervenir sur les tables de paramètres *)

      | "Set"; table = IDENT; field = IDENT; v = option_value ->
  	  VernacSetOption (SecondaryTable (table,field),v)
      | "Set"; table = IDENT; field = IDENT; lv = LIST1 option_ref_value ->
  	  VernacAddOption (SecondaryTable (table,field),lv)
      | "Set"; table = IDENT; field = IDENT ->
  	  VernacSetOption (SecondaryTable (table,field),BoolValue true)
      | IDENT "Unset"; table = IDENT; field = IDENT ->
  	  VernacUnsetOption (SecondaryTable (table,field))
      | IDENT "Unset"; table = IDENT; field = IDENT; lv = LIST1 option_ref_value ->
  	  VernacRemoveOption (SecondaryTable (table,field),lv)
      | "Set"; table = IDENT; value = option_value ->
  	  VernacSetOption (PrimaryTable table, value)
      | "Set"; table = IDENT ->
  	  VernacSetOption (PrimaryTable table, BoolValue true)
      | IDENT "Unset"; table = IDENT ->
  	  VernacUnsetOption (PrimaryTable table)

      | IDENT "Print"; IDENT "Table"; table = IDENT; field = IDENT ->
	  VernacPrintOption (SecondaryTable (table,field))
      | IDENT "Print"; IDENT "Table"; table = IDENT ->
	  VernacPrintOption (PrimaryTable table)

      | IDENT "Add"; table = IDENT; field = IDENT; v = LIST1 option_ref_value
        -> VernacAddOption (SecondaryTable (table,field), v)

      (* Un value global ci-dessous va être caché par un field au dessus! *)
      | IDENT "Add"; table = IDENT; v = LIST1 option_ref_value ->
          VernacAddOption (PrimaryTable table, v)

      | IDENT "Test"; table = IDENT; field = IDENT; v = LIST1 option_ref_value
        -> VernacMemOption (SecondaryTable (table,field), v)
      | IDENT "Test"; table = IDENT; field = IDENT ->
          VernacPrintOption (SecondaryTable (table,field))
      | IDENT "Test"; table = IDENT; v = LIST1 option_ref_value ->
          VernacMemOption (PrimaryTable table, v)
      | IDENT "Test"; table = IDENT ->
          VernacPrintOption (PrimaryTable table)

      | IDENT "Remove"; table = IDENT; field = IDENT; v= LIST1 option_ref_value
        -> VernacRemoveOption (SecondaryTable (table,field), v)
      | IDENT "Remove"; table = IDENT; v = LIST1 option_ref_value ->
	  VernacRemoveOption (PrimaryTable table, v) ] ]
  ;
  printable:
    [ [ IDENT "Term"; qid = global -> PrintName qid
      | IDENT "All" -> PrintFullContext
      | IDENT "Section"; s = global -> PrintSectionContext s
      | "Grammar"; uni = IDENT; ent = IDENT ->
          (* This should be in "syntax" section but is here for factorization*)
	  PrintGrammar (uni, ent)
      | IDENT "LoadPath" -> PrintLoadPath
      | IDENT "Modules" -> PrintModules

      | IDENT "ML"; IDENT "Path" -> PrintMLLoadPath
      | IDENT "ML"; IDENT "Modules" -> PrintMLModules
      | IDENT "Graph" -> PrintGraph
      | IDENT "Classes" ->  PrintClasses
      | IDENT "Coercions" -> PrintCoercions
      | IDENT "Coercion"; IDENT "Paths"; s = class_rawexpr; t = class_rawexpr
         -> PrintCoercionPaths (s,t)
      | IDENT "Tables" -> PrintTables
      | "Proof"; qid = global -> PrintOpaqueName qid
      | IDENT "Hint" -> PrintHintGoal
      | IDENT "Hint"; qid = global -> PrintHint qid
      | IDENT "Hint"; "*" -> PrintHintDb
      | IDENT "HintDb"; s = IDENT -> PrintHintDbName s
      | IDENT "Scope"; s = IDENT -> PrintScope s ] ]
  ;
  option_value:
    [ [ n  = integer   -> IntValue n
      | s  = STRING    -> StringValue s ] ]
  ;
  option_ref_value:
    [ [ id = global   -> QualidRefValue id
      | s  = STRING   -> StringRefValue s ] ]
  ;
  as_dirpath:
    [ [ d = OPT [ "as"; d = dirpath -> d ] -> d ] ]
  ;
  in_or_out_modules:
    [ [ IDENT "inside"; l = LIST1 global -> SearchInside l
      | IDENT "outside"; l = LIST1 global -> SearchOutside l
      | -> SearchOutside [] ] ]
  ;
END;

(* Grammar extensions *)
	  
GEXTEND Gram
  GLOBAL: syntax;

  univ:
  [ [ univ = IDENT ->
        set_default_action_parser (parser_type_from_name univ); univ ] ]
  ;
  syntax:
   [ [ IDENT "Token"; s = STRING ->
       Pp.warning "Token declarations are now useless"; VernacNop

     | "Grammar"; IDENT "tactic"; IDENT "simple_tactic";
        OPT [ ":"; IDENT "tactic" ]; ":=";
        OPT "|"; tl = LIST0 grammar_tactic_rule SEP "|" -> 
	  VernacTacticGrammar tl

     | "Grammar"; u = univ;
         tl = LIST1 grammar_entry SEP "with" -> 
	   VernacGrammar (rename_command_entry u,tl)

     | "Syntax"; u = univ; el = LIST1 syntax_entry SEP ";" ->
         VernacSyntax (u,el)

     | "Uninterpreted"; IDENT "Notation"; s = STRING; 
	 l = [ "("; l = LIST1 syntax_modifier SEP ","; ")" -> l | -> [] ]
	 -> VernacSyntaxExtension (s,l)

     | IDENT "Open"; IDENT "Scope"; sc = IDENT -> VernacOpenScope sc

     | IDENT "Delimits"; IDENT "Scope"; sc = IDENT; "with"; key = IDENT ->
	 VernacDelimiters (sc,key)

     | IDENT "Arguments"; IDENT "Scope"; qid = global;
         "["; scl = LIST0 opt_scope; "]" -> VernacArgumentsScope (qid,scl)

     | IDENT "Infix"; a = entry_prec; n = natural; op = STRING; p = global;
	 sc = OPT [ ":"; sc = IDENT -> sc ] -> VernacInfix (a,n,op,p,sc)
     | IDENT "Distfix"; a = entry_prec; n = natural; s = STRING; p = global;
	 sc = OPT [ ":"; sc = IDENT -> sc ] -> VernacDistfix (a,n,s,p,sc)
     | IDENT "Notation"; s = IDENT; ":="; c = constr ->
	 VernacNotation ("'"^s^"'",c,[],None)
     | IDENT "Notation"; s = STRING; ":="; c = constr;
         modl = [ "("; l = LIST1 syntax_modifier SEP ","; ")" -> l | -> [] ];
	 sc = OPT [ ":"; sc = IDENT -> sc ] -> VernacNotation (s,c,modl,sc)

     (* "Print" "Grammar" should be here but is in "command" entry in order 
        to factorize with other "Print"-based vernac entries *)
  ] ]
  ;
  syntax_modifier:
    [ [ x = IDENT; IDENT "at"; IDENT "level"; n = natural -> 
        SetItemLevel ([x],n)
      | x = IDENT; ","; l = LIST1 IDENT SEP ","; IDENT "at"; IDENT "level";
        n = natural -> SetItemLevel (x::l,n)
      | IDENT "at"; IDENT "level"; n = natural -> SetLevel n
      | IDENT "left"; IDENT "associativity" -> SetAssoc Gramext.LeftA
      | IDENT "right"; IDENT "associativity" -> SetAssoc Gramext.RightA
      | IDENT "no"; IDENT "associativity" -> SetAssoc Gramext.NonA
      | x = IDENT; typ = syntax_extension_type -> SetEntryType (x,typ)
      | IDENT "only"; IDENT "parsing" -> SetOnlyParsing ] ]
  ;
  syntax_extension_type:
    [ [ IDENT "ident" -> ETIdent | IDENT "global" -> ETReference ] ]
  ;
  opt_scope:
    [ [ IDENT "_" -> None | sc = IDENT -> Some sc ] ]
  ;
  (* Syntax entries for Grammar. Only grammar_entry is exported *)
  grammar_entry:
    [[ nont = IDENT; set_entry_type; ":=";
       ep = entry_prec; OPT "|"; rl = LIST0 grammar_rule SEP "|" ->
	 (nont,ep,rl) ]]
  ;
  entry_prec:
    [[ IDENT "LEFTA" -> Some Gramext.LeftA
     | IDENT "RIGHTA" -> Some Gramext.RightA
     | IDENT "NONA" -> Some Gramext.NonA
     | -> None  ]]
  ;
  grammar_tactic_rule:
    [[ name = rule_name; "["; s = STRING; pil = LIST0 production_item; "]";
       "->"; "["; t = Tactic.tactic; "]"  -> (name, (s,pil), t) ]]
  ;
  grammar_rule:
    [[ name = rule_name; "["; pil = LIST0 production_item; "]"; "->";
       a = action -> (name, pil, a) ]]
  ;
  rule_name:
    [[ name = IDENT -> name ]]
  ;
  production_item:
    [[ s = STRING -> VTerm s
     | nt = non_terminal; po = OPT [ "("; p = METAIDENT; ")" -> p ] ->
         match po with
           | Some p -> VNonTerm (loc,nt,Some (Names.id_of_string p))
           | _ -> VNonTerm (loc,nt,None) ]]
  ;
  non_terminal:
    [[ u = IDENT; ":"; nt = IDENT ->
        NtQual(rename_command_entry u, rename_command_entry nt)
     | nt = IDENT -> NtShort (rename_command_entry nt) ]]
  ;


  (* Syntax entries for Syntax. Only syntax_entry is exported *)
  syntax_entry:
    [ [ IDENT "level"; p = precedence; ":";
	OPT "|"; rl = LIST1 syntax_rule SEP "|" -> (p,rl) ] ]
  ;
  syntax_rule:
    [ [ nm = IDENT; "["; s = astpat; "]"; "->"; u = unparsing -> (nm,s,u) ] ]
  ;
  precedence:
    [ [ a = natural -> a
(*      | "["; a1 = natural; a2 = natural; a3 = natural; "]" -> (a1,a2,a3)*)
    ] ]
  ;
  unparsing:
    [ [ "["; ll = LIST0 next_hunks; "]" -> ll ] ]
  ;
  next_hunks:
    [ [ IDENT "FNL" -> UNP_FNL
      | IDENT "TAB" -> UNP_TAB
      | c = STRING -> RO c
      | "[";
        x =
          [ b = box; ll = LIST0 next_hunks -> UNP_BOX (b,ll)
          | n = natural; m = natural -> UNP_BRK (n, m)
          | IDENT "TBRK"; n = natural; m = natural -> UNP_TBRK (n, m) ];
        "]" -> x
      | e = Prim.ast; oprec = OPT [ ":"; pr = paren_reln_or_extern -> pr ] ->
          match oprec with
	    | Some (ext,pr) -> PH (e,ext,pr)
            | None -> PH (e,None,Any)
 ]]
  ;
  box:
    [ [ "<"; bk = box_kind; ">" -> bk ] ]
  ;
  box_kind:
    [ [ IDENT "h"; n = natural -> PpHB n
      | IDENT "v"; n = natural -> PpVB n
      | IDENT "hv"; n = natural -> PpHVB n
      | IDENT "hov"; n = natural -> PpHOVB n
      | IDENT "t" -> PpTB ] ]
  ;
  paren_reln_or_extern:
    [ [ IDENT "L" -> None, L
      | IDENT "E" -> None, E
      | pprim = STRING; precrec = OPT [ ":"; p = precedence -> p ] ->
	  match precrec with
	    | Some p -> Some pprim, Prec p
            | None -> Some pprim, Any ] ]
  ;
  (* meta-syntax entries *)
  astpat:
    [ [ "<<" ; a = Prim.ast; ">>" -> a 
      | a = Constr.constr -> 
	  Termast.ast_of_rawconstr 
	  (Constrintern.interp_rawconstr Evd.empty (Global.env()) a)
    ] ]
  ; 
  action:
    [ [ IDENT "let"; p = Prim.astlist; et = set_internal_entry_type;
        "="; e1 = action; "in"; e = action -> Ast.CaseAction (loc,e1,et,[p,e])
      | IDENT "case"; a = action; et = set_internal_entry_type; "of";
        cl = LIST1 case SEP "|"; IDENT "esac" -> Ast.CaseAction (loc,a,et,cl)
      | "["; a = default_action_parser; "]" -> Ast.SimpleAction (loc,a) ] ]
  ;
  case:
    [[ p = Prim.astlist; "->"; a = action -> (p,a) ]]
  ;
  set_internal_entry_type:
    [[ ":"; IDENT "ast"; IDENT "list" -> Ast.ETastl
     | [ ":"; IDENT "ast" -> () | -> () ] -> Ast.ETast ]]
  ;
  set_entry_type:
    [[ ":"; et = entry_type -> set_default_action_parser et
     | -> () ]]
  ;
  entry_type:
    [[ IDENT "ast"; IDENT "list" -> Util.error "type ast list no longer supported"
     | IDENT "ast" -> Util.error "type ast no longer supported"
     | IDENT "constr" -> ConstrParser
     | IDENT "pattern" -> CasesPatternParser
     | IDENT "tactic" -> assert false
     | IDENT "vernac" -> Util.error "vernac extensions no longer supported" ] ]
  ;
END
