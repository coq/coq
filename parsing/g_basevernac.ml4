
(* $Id$ *)

open Coqast
open Pcoq

open Vernac

GEXTEND Gram
  GLOBAL: identarg ne_identarg_list numarg ne_numarg_list numarg_list
          stringarg ne_stringarg_list constrarg sortarg tacarg;

  identarg:
    [ [ id = IDENT -> <:ast< ($VAR $id) >> ] ]
  ;
  ne_identarg_list:
    [ [ l = LIST1 identarg -> l ] ]
  ;
  numarg:
    [ [ n = Prim.number -> n 
       |  "-"; n = Prim.number -> Num (loc, ( - Ast.num_of_ast n)) ] ]
  ;
  ne_numarg_list:
    [ [ n = numarg; l = ne_numarg_list -> n::l
      | n = numarg -> [n] ] ]
  ;
  numarg_list:
    [ [ l = ne_numarg_list -> l
      |  -> [] ] ]
  ;
  stringarg:
    [ [ s = Prim.string -> s ] ]
  ;
  ne_stringarg_list:
    [ [ n = stringarg; l = ne_stringarg_list -> n::l
      | n = stringarg -> [n] ] ]
  ;
  constrarg:
    [ [ c = Constr.constr -> <:ast< (CONSTR $c) >> ] ]
  ;
  sortarg:
    [ [ c = Constr.sort -> <:ast< (CONSTR $c) >> ] ]
  ;
  tacarg:
    [ [ tcl = Tactic.tactic_com_list -> tcl ] ]
  ;
END;

GEXTEND Gram
  GLOBAL: command;

  command:
    [ [ IDENT "Pwd"; "." -> <:ast< (PWD) >>
      | IDENT "Cd"; "." -> <:ast< (CD) >>
      | IDENT "Cd"; dir = stringarg; "." -> <:ast< (CD $dir) >>

      | IDENT "Drop"; "." -> <:ast< (DROP) >>
      | IDENT "ProtectedLoop"; "." -> <:ast< (PROTECTEDLOOP)>>
      | "Quit"; "." -> <:ast< (QUIT) >>

      | IDENT "Print"; IDENT "All"; "." -> <:ast< (PrintAll) >>
      | IDENT "Print"; "." -> <:ast< (PRINT) >>
      | IDENT "Print"; IDENT "Hint"; "*"; "." 
	                    -> <:ast< (PrintHint) >>
      | IDENT "Print"; IDENT "Hint"; s = identarg; "." ->
          <:ast< (PrintHintId $s) >>
      | IDENT "Print"; IDENT "Hint"; "." ->
          <:ast< (PrintHintGoal) >>
      | IDENT "Print"; IDENT "HintDb"; s = identarg ; "." ->
	  <:ast< (PrintHintDb $s) >>
      | IDENT "Print"; IDENT "Section"; s = identarg; "." ->
          <:ast< (PrintSec $s) >>
      | IDENT "Print"; IDENT "States"; "." -> <:ast< (PrintStates) >>
      | IDENT "Locate"; IDENT "File"; f = stringarg; "." ->
	  <:ast< (LocateFile $f) >>
      | IDENT "Locate"; IDENT "Library"; id = identarg; "." ->
	  <:ast< (LocateLibrary $id) >>
      | IDENT "Locate"; id = identarg; "." ->
	  <:ast< (Locate $id) >>
      | IDENT "Print"; IDENT "LoadPath"; "." -> <:ast< (PrintPath) >>
      | IDENT "AddPath"; dir = stringarg; "." -> <:ast< (ADDPATH $dir) >>
      | IDENT "DelPath"; dir = stringarg; "." -> <:ast< (DELPATH $dir) >>
      | IDENT "AddRecPath"; dir = stringarg; "." ->
          <:ast< (RECADDPATH $dir) >>
      | IDENT "Print"; IDENT "Modules"; "." -> <:ast< (PrintModules) >>
      | IDENT "Print"; "Proof"; id = identarg; "." ->
          <:ast< (PrintOpaqueId $id) >>
(* Pris en compte dans PrintOption ci-dessous 
      | IDENT "Print"; id = identarg; "." -> <:ast< (PrintId $id) >> *)
      | IDENT "Search"; id = identarg; "." -> <:ast< (SEARCH $id) >>
      | IDENT "Inspect"; n = numarg; "." -> <:ast< (INSPECT $n) >>
      (* TODO: rapprocher Eval et Check *)
      | IDENT "Eval"; r = Tactic.red_tactic; "in"; c = constrarg; "." ->
          <:ast< (Eval (TACTIC_ARG (REDEXP $r)) $c) >>
      | IDENT "Eval"; g = numarg; r = Tactic.red_tactic;
        "in"; c = constrarg; "." ->
          <:ast< (Eval (TACTIC_ARG (REDEXP $r)) $c $g) >>
      | check = check_tok; c = constrarg; "." -> <:ast< (Check $check $c) >>
      | check = check_tok; g = numarg; c = constrarg; "." ->
          <:ast< (Check $check $c $g) >>
      | IDENT "Print"; IDENT "ML"; IDENT "Path"; "." ->
          <:ast< (PrintMLPath) >>
      | IDENT "Print"; IDENT "ML"; IDENT "Modules"; "." ->
          <:ast< (PrintMLModules) >>
      | IDENT "Add"; IDENT "ML"; IDENT "Path"; dir = stringarg; "." ->
          <:ast< (AddMLPath $dir) >>
      | IDENT "Add"; IDENT "Rec"; IDENT "ML"; IDENT "Path";
        dir = stringarg; "." ->
          <:ast< (RecAddMLPath $dir) >>
      | IDENT "Print"; IDENT "Graph"; "." -> <:ast< (PrintGRAPH) >>
      | IDENT "Print"; IDENT "Classes"; "." -> <:ast< (PrintCLASSES) >>
      | IDENT "Print"; IDENT "Coercions"; "." -> <:ast< (PrintCOERCIONS) >>
      | IDENT "Print"; IDENT "Path"; c = identarg; d = identarg; "." ->
          <:ast< (PrintPATH $c $d) >>

(*      | IDENT "Time"; "." -> <:ast< (Time) >>
      | IDENT "Untime"; "." -> <:ast< (Untime) >> *)

      | IDENT "Time"; v = vernac -> <:ast< (Time $v)>>
      | IDENT "SearchIsos"; com = constrarg; "." ->
          <:ast< (Searchisos $com) >>
      | "Set"; IDENT "Undo"; n = numarg; "." ->
          <:ast< (SETUNDO $n) >>
      | IDENT "Unset"; IDENT "Undo"; "." -> <:ast< (UNSETUNDO) >>
      | "Set"; IDENT "Hyps_limit"; n = numarg; "." ->
          <:ast< (SETHYPSLIMIT $n) >>
      | IDENT "Unset"; IDENT "Hyps_limit"; "." ->
          <:ast< (UNSETHYPSLIMIT) >>

      (* Pour intervenir sur les tables de paramètres *)
      | "Set"; table = identarg; field = identarg;
                      value = option_value; "." ->
          <:ast< (SetTableField $table $field $value) >>
      | "Set"; table = identarg; field = identarg; "." ->
          <:ast< (SetTableField $table $field) >>
      | IDENT "Unset"; table = identarg; field = identarg; "." ->
          <:ast< (UnsetTableField $table $field) >>
      | "Set"; table = identarg; value = option_value; "." ->
          <:ast< (SetTableField $table $value) >>
      | "Set"; table = identarg; "." ->
          <:ast< (SetTableField $table) >>
      | IDENT "Unset"; table = identarg; "." ->
          <:ast< (UnsetTableField $table) >>
      | IDENT "Print"; table = identarg; field = identarg; "." ->
          <:ast< (PrintOption $table $field) >>
      (* Le cas suivant inclut aussi le "Print id" standard *)
      | IDENT "Print"; table = identarg; "." ->
          <:ast< (PrintOption $table) >>
      | IDENT "Add"; table = identarg; field = identarg; id = identarg; "."
        -> <:ast< (AddTableField $table $field $id) >>
      | IDENT "Add"; table = identarg; id = identarg; "."
        -> <:ast< (AddTableField $table $id) >>
      | IDENT "Test"; table = identarg; field = identarg; id = identarg; "."
        -> <:ast< (MemTableField $table $field $id) >>
      | IDENT "Test"; table = identarg; id = identarg; "."
        -> <:ast< (MemTableField $table $id) >>
      | IDENT "Remove"; table = identarg; field = identarg; id = identarg; "." ->
          <:ast< (RemoveTableField $table $field $id) >>
      | IDENT "Remove"; table = identarg; id = identarg; "." ->
          <:ast< (RemoveTableField $table $id) >> ] ]
  ;
  option_value:
    [ [ id = identarg    -> id
      | n  = numarg      -> n
      | s  = stringarg   -> s ] ]
  ;
  check_tok:
    [ [ IDENT "Check" -> <:ast< "CHECK" >>
      | "Type" -> <:ast< "PRINTTYPE" >> ] ] (* pas dans le RefMan *)
  ;
END;

(* Grammar extensions *)
	  
GEXTEND Gram
  GLOBAL: syntax Prim.syntax_entry Prim.grammar_entry;

  syntax:
   [ [ "Token"; s = STRING; "." -> <:ast< (TOKEN ($STR $s)) >>

     | "Grammar"; univ=IDENT; tl=LIST1 Prim.grammar_entry SEP "with"; "." ->
         <:ast< (GRAMMAR ($VAR univ) (ASTLIST ($LIST tl))) >>

     | "Syntax"; whatfor=IDENT; el=LIST1 Prim.syntax_entry SEP ";"; "." ->
         <:ast< (SYNTAX ($VAR whatfor) (ASTLIST ($LIST el))) >>
     | IDENT "Infix"; as_ = entry_prec; n = numarg; op = Prim.string;
       p = identarg; "." -> <:ast< (INFIX (AST $as_) $n $op $p) >>
     | IDENT "Distfix"; as_ = entry_prec; n = numarg; s = Prim.string;
       p = identarg; "." -> <:ast< (DISTFIX (AST $as_) $n $s $p) >>
     | IDENT "Print"; "Grammar"; uni = identarg; ent = identarg; "." ->
         <:ast< (PrintGrammar $uni $ent) >>
  ] ]
  ;

  (* Syntax entries for Grammar. Only grammar_entry is exported *)
  Prim.grammar_entry:
    [[ nont = Prim.ident; etyp = Prim.entry_type; ":=";
       ep = entry_prec; OPT "|"; rl = LIST0 grammar_rule SEP "|" ->
         <:ast< (GRAMMARENTRY $nont $etyp $ep ($LIST rl)) >> ]]
  ;
  entry_prec:
    [[ IDENT "LEFTA" -> <:ast< {LEFTA} >>
     | IDENT "RIGHTA" -> <:ast< {RIGHTA} >>
     | IDENT "NONA" -> <:ast< {NONA} >>
     | ->  <:ast< {NONE} >> ] ]
  ;
  grammar_rule:
    [[ name = rule_name; "["; pil = LIST0 production_item; "]"; "->";
       a = Prim.astact ->
        <:ast< (GRAMMARRULE ($ID name) $a ($LIST pil)) >> ]]
  ;
  rule_name:
    [[ name = IDENT -> name ]]
  ;
  production_item:
    [[ s = STRING -> <:ast< ($STR $s) >>
     | nt = non_terminal; po = OPT [ "("; p = Prim.ident; ")" -> p ] ->
         match po with
           | Some p -> <:ast< (NT $nt $p) >>
           | _ -> <:ast< (NT $nt) >> ]]
  ;
  non_terminal:
    [[ u = Prim.ident; ":"; nt = Prim.ident -> <:ast< (QUAL $u $nt) >>
     | nt = Prim.ident -> <:ast< $nt >> ]]
  ;


  (* Syntax entries for Syntax. Only syntax_entry is exported *)
  Prim.syntax_entry:
    [ [ IDENT "level"; p = precedence; ":";
	OPT "|"; rl = LIST1 syntax_rule SEP "|" ->
          <:ast< (SYNTAXENTRY $p ($LIST $rl)) >> ] ]
  ;
  syntax_rule:
    [ [ nm = IDENT; "["; s = Prim.astpat; "]"; "->"; u = unparsing ->
          <:ast< (SYNTAXRULE ($ID $nm) $s $u) >> ] ]
  ;
  precedence:
    [ [ a = Prim.number ->  <:ast< (PREC $a 0 0) >>
      | "["; a1 = Prim.number; a2 = Prim.number; a3 = Prim.number; "]" ->
          <:ast< (PREC $a1 $a2 $a3) >> ] ]
  ;
  unparsing:
    [ [ "["; ll = LIST0 next_hunks; "]" -> <:ast< (UNPARSING ($LIST $ll))>> ] ]
  ;
  next_hunks:
    [ [ IDENT "FNL" -> <:ast< (UNP_FNL) >>
      | IDENT "TAB" -> <:ast< (UNP_TAB) >>
      | c = STRING -> <:ast< (RO ($STR $c)) >>
      | "[";
        x =
          [ b = box; ll = LIST0 next_hunks -> <:ast<(UNP_BOX $b ($LIST $ll))>>
          | n = Prim.number; m = Prim.number -> <:ast< (UNP_BRK $n $m) >>
          | IDENT "TBRK";
            n = Prim.number; m = Prim.number -> <:ast< (UNP_TBRK $n $m) >> ];
        "]" -> x
      | e = Prim.ast; oprec = OPT [ ":"; pr = paren_reln_or_extern -> pr ] ->
          match oprec with
	    | Some pr -> <:ast< (PH $e $pr) >>
            | None -> <:ast< (PH $e {Any}) >> ]]
  ;
  box:
    [ [ "<"; bk = box_kind; ">" -> bk ] ]
  ;
  box_kind:
    [ [ IDENT "h"; n = Prim.number -> <:ast< (PpHB $n) >>
      | IDENT "v"; n = Prim.number -> <:ast< (PpVB $n) >>
      | IDENT "hv"; n = Prim.number -> <:ast< (PpHVB $n) >>
      | IDENT "hov"; n = Prim.number -> <:ast< (PpHOVB $n) >>
      | IDENT "t" -> <:ast< (PpTB) >> ] ]
  ;
  paren_reln_or_extern:
    [ [ IDENT "L" -> <:ast< {L} >>
      | IDENT "E" -> <:ast< {E} >>
      | pprim = STRING; precrec = OPT [ ":"; p = precedence -> p ] ->
	  match precrec with
	    | Some p -> <:ast< (EXTERN ($STR $pprim) $p) >>
            | None -> <:ast< (EXTERN ($STR $pprim)) >> ] ]
  ;
END
