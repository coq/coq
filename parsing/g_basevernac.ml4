
(* $Id$ *)

open Coqast
open Pcoq

open Vernac

GEXTEND Gram
  identarg:
    [ [ id = IDENT -> <:ast< ($VAR $id) >> ] ]
  ;
  ne_identarg_list:
    [ [ l = LIST1 identarg -> l ] ]
  ;

  ne_identarg_comma_list:
    [ [ id = identarg; ","; idl = ne_identarg_comma_list -> id::idl
      | id = identarg -> [id] ] ]
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
  comarg:
    [ [ c = Constr.constr -> <:ast< (CONSTR $c) >> ] ]
  ;
  lcomarg:
    [ [ c = Constr.lconstr -> <:ast< (CONSTR $c) >> ] ]
  ;
  lvernac:
    [ [ v = vernac; l = lvernac -> v::l
      |  -> [] ] ]
  ;
  ne_stringarg_list:
    [ [ n = stringarg; l = ne_stringarg_list -> n::l
      | n = stringarg -> [n] ] ]
  ;
  varg_ne_stringarg_list:
    [ [ l = ne_stringarg_list -> <:ast< (VERNACARGLIST ($LIST $l)) >> ] ]
  ;
  vernac:
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
      | IDENT "Eval"; r = Tactic.red_tactic; "in"; c = comarg; "." ->
          <:ast< (Eval (TACTIC_ARG (REDEXP $r)) $c) >>
      | IDENT "Eval"; g = numarg; r = Tactic.red_tactic;
        "in"; c = comarg; "." ->
          <:ast< (Eval (TACTIC_ARG (REDEXP $r)) $c $g) >>
      | check = check_tok; c = comarg; "." -> <:ast< (Check $check $c) >>
      | check = check_tok; g = numarg; c = comarg; "." ->
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
      | IDENT "SearchIsos"; com = comarg; "." ->
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
