(****************************************************************************)
(*                 The Calculus of Inductive Constructions                  *)
(*                                                                          *)
(*                                Projet Coq                                *)
(*                                                                          *)
(*                     INRIA                        ENS-CNRS                *)
(*              Rocquencourt                        Lyon                    *)
(*                                                                          *)
(*                                 Coq V6.3                                 *)
(*                              Jul 10th 1997                               *)
(*                                                                          *)
(****************************************************************************)
(*                             g_basevernac.ml4                             *)
(****************************************************************************)

(* camlp4o pa_extend.cmo ./q_ast.cma *)

open CoqAst;;
open Pcoq;;

open Vernac;;
GEXTEND Gram
  identarg:
    [ [ id = LIDENT -> <:ast< ($VAR $id) >> ] ]
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
    [ [ c = Command.command -> <:ast< (COMMAND $c) >> ] ]
  ;
  lcomarg:
    [ [ c = Command.lcommand -> <:ast< (COMMAND $c) >> ] ]
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
    [ [ LIDENT "Pwd"; "." -> <:ast< (PWD) >>
      | LIDENT "Cd"; "." -> <:ast< (CD) >>
      | LIDENT "Cd"; dir = stringarg; "." -> <:ast< (CD $dir) >>
      | "Quit"; "." -> <:ast< (QUIT) >>
      | LIDENT "Drop"; "." -> <:ast< (DROP) >>
      | LIDENT "ProtectedLoop"; "." -> <:ast< (PROTECTEDLOOP) >>
      | LIDENT "Print"; LIDENT "All"; "." -> <:ast< (PrintAll) >>
      | LIDENT "Print"; "." -> <:ast< (PRINT) >>
      | LIDENT "Print"; LIDENT "Hint"; "*"; "." 
	                    -> <:ast< (PrintHint) >>
      | LIDENT "Print"; LIDENT "Hint"; s = identarg; "." ->
          <:ast< (PrintHintId $s) >>
      | LIDENT "Print"; LIDENT "Hint"; "." ->
          <:ast< (PrintHintGoal) >>
      | LIDENT "Print"; LIDENT "HintDb"; s = identarg ; "." ->
	  <:ast< (PrintHintDb $s) >>
      | LIDENT "Print"; LIDENT "Section"; s = identarg; "." ->
          <:ast< (PrintSec $s) >>
      | LIDENT "Print"; LIDENT "States"; "." -> <:ast< (PrintStates) >>
      | LIDENT "Locate"; LIDENT "File"; f = stringarg; "." ->
	  <:ast< (LocateFile $f) >>
      | LIDENT "Locate"; LIDENT "Library"; id = identarg; "." ->
	  <:ast< (LocateLibrary $id) >>
      | LIDENT "Locate"; id = identarg; "." ->
	  <:ast< (Locate $id) >>
      | LIDENT "Print"; LIDENT "LoadPath"; "." -> <:ast< (PrintPath) >>
      | LIDENT "AddPath"; dir = stringarg; "." -> <:ast< (ADDPATH $dir) >>
      | LIDENT "DelPath"; dir = stringarg; "." -> <:ast< (DELPATH $dir) >>
      | LIDENT "AddRecPath"; dir = stringarg; "." ->
          <:ast< (RECADDPATH $dir) >>
      | LIDENT "Print"; LIDENT "Modules"; "." -> <:ast< (PrintModules) >>
      | LIDENT "Print"; "Proof"; id = identarg; "." ->
          <:ast< (PrintOpaqueId $id) >>
(* Pris en compte dans PrintOption ci-dessous 
      | LIDENT "Print"; id = identarg; "." -> <:ast< (PrintId $id) >> *)
      | LIDENT "Search"; id = identarg; "." -> <:ast< (SEARCH $id) >>
      | LIDENT "Inspect"; n = numarg; "." -> <:ast< (INSPECT $n) >>
      (* TODO: rapprocher Eval et Check *)
      | LIDENT "Eval"; r = Tactic.red_tactic; "in"; c = comarg; "." ->
          <:ast< (Eval (TACTIC_ARG (REDEXP $r)) $c) >>
      | LIDENT "Eval"; g = numarg; r = Tactic.red_tactic;
        "in"; c = comarg; "." ->
          <:ast< (Eval (TACTIC_ARG (REDEXP $r)) $c $g) >>
      | check = check_tok; c = comarg; "." -> <:ast< (Check $check $c) >>
      | check = check_tok; g = numarg; c = comarg; "." ->
          <:ast< (Check $check $c $g) >>
      | LIDENT "Print"; LIDENT "ML"; LIDENT "Path"; "." ->
          <:ast< (PrintMLPath) >>
      | LIDENT "Print"; LIDENT "ML"; LIDENT "Modules"; "." ->
          <:ast< (PrintMLModules) >>
      | LIDENT "Add"; LIDENT "ML"; LIDENT "Path"; dir = stringarg; "." ->
          <:ast< (AddMLPath $dir) >>
      | LIDENT "Add"; LIDENT "Rec"; LIDENT "ML"; LIDENT "Path";
        dir = stringarg; "." ->
          <:ast< (RecAddMLPath $dir) >>
      | LIDENT "Print"; LIDENT "Graph"; "." -> <:ast< (PrintGRAPH) >>
      | LIDENT "Print"; LIDENT "Classes"; "." -> <:ast< (PrintCLASSES) >>
      | LIDENT "Print"; LIDENT "Coercions"; "." -> <:ast< (PrintCOERCIONS) >>
      | LIDENT "Print"; LIDENT "Path"; c = identarg; d = identarg; "." ->
          <:ast< (PrintPATH $c $d) >>

(*      | LIDENT "Time"; "." -> <:ast< (Time) >>
      | LIDENT "Untime"; "." -> <:ast< (Untime) >> *)

      | LIDENT "Time"; v = vernac -> <:ast< (Time $v)>>
      | LIDENT "SearchIsos"; com = comarg; "." ->
          <:ast< (Searchisos $com) >>
      | "Set"; LIDENT "Undo"; n = numarg; "." ->
          <:ast< (SETUNDO $n) >>
      | LIDENT "Unset"; LIDENT "Undo"; "." -> <:ast< (UNSETUNDO) >>
      | "Set"; LIDENT "Hyps_limit"; n = numarg; "." ->
          <:ast< (SETHYPSLIMIT $n) >>
      | LIDENT "Unset"; LIDENT "Hyps_limit"; "." ->
          <:ast< (UNSETHYPSLIMIT) >>

      (* Pour intervenir sur les tables de paramètres *)
      | "Set"; table = identarg; field = identarg;
                      value = option_value; "." ->
          <:ast< (SetTableField $table $field $value) >>
      | "Set"; table = identarg; field = identarg; "." ->
          <:ast< (SetTableField $table $field) >>
      | LIDENT "Unset"; table = identarg; field = identarg; "." ->
          <:ast< (UnsetTableField $table $field) >>
      | "Set"; table = identarg; value = option_value; "." ->
          <:ast< (SetTableField $table $value) >>
      | "Set"; table = identarg; "." ->
          <:ast< (SetTableField $table) >>
      | LIDENT "Unset"; table = identarg; "." ->
          <:ast< (UnsetTableField $table) >>
      | LIDENT "Print"; table = identarg; field = identarg; "." ->
          <:ast< (PrintOption $table $field) >>
      (* Le cas suivant inclut aussi le "Print id" standard *)
      | LIDENT "Print"; table = identarg; "." ->
          <:ast< (PrintOption $table) >>
      | LIDENT "Add"; table = identarg; field = identarg; id = identarg; "."
        -> <:ast< (AddTableField $table $field $id) >>
      | LIDENT "Add"; table = identarg; id = identarg; "."
        -> <:ast< (AddTableField $table $id) >>
      | LIDENT "Test"; table = identarg; field = identarg; id = identarg; "."
        -> <:ast< (MemTableField $table $field $id) >>
      | LIDENT "Test"; table = identarg; id = identarg; "."
        -> <:ast< (MemTableField $table $id) >>
      | LIDENT "Remove"; table = identarg; field = identarg; id = identarg; "." ->
          <:ast< (RemoveTableField $table $field $id) >>
      | LIDENT "Remove"; table = identarg; id = identarg; "." ->
          <:ast< (RemoveTableField $table $id) >> ] ]
  ;
  option_value:
    [ [ id = identarg    -> id
      | n  = numarg      -> n
      | s  = stringarg   -> s ] ]
  ;
  check_tok:
    [ [ LIDENT "Check" -> <:ast< "CHECK" >>
      | "Type" -> <:ast< "PRINTTYPE" >> ] ] (* pas dans le RefMan *)
  ;
END;

(* $Id$ *)
