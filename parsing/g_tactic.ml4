
(* $Id$ *)

open Pp
open Ast
open Pcoq

open Tactic

(* Please leave several GEXTEND for modular compilation under PowerPC *)

(* Auxiliary grammar rules *)

GEXTEND Gram
  identarg:
    [ [ id = LIDENT -> <:ast< ($VAR $id) >> ] ]
  ;
  numarg:
    [ [ n = Prim.number -> n
      | "-"; n = Prim.number -> CoqAst.Num (Ast.loc n, ( - Ast.num_of_ast n))
      ] ]
  ;
  comarg:
    [ [ c = Command.command -> <:ast< (COMMAND $c) >> ] ]
  ;
  lcomarg:
    [ [ c = Command.lcommand -> <:ast< (COMMAND $c) >> ] ]
  ;
  ne_identarg_list:
    [ [ l = LIST1 identarg -> l ] ]
  ;
  ne_num_list:
    [ [ n = numarg; l = ne_num_list -> n :: l | n = numarg -> [n] ] ]
  ;
  pattern_occ:
    [ [ nl = ne_num_list; c = comarg -> <:ast< (PATTERN $c ($LIST $nl)) >>
      | c = comarg -> <:ast< (PATTERN $c) >> ] ]
  ;
  ne_pattern_list:
    [ [ l = LIST1 pattern_occ -> l ] ]
  ;
  pattern_occ_hyp:
    [ [ nl = ne_num_list; LIDENT "Goal" -> <:ast<(CCLPATTERN ($LIST $nl))>>
      | nl = ne_num_list; id = identarg -> <:ast<(HYPPATTERN $id ($LIST $nl))>>
      | LIDENT "Goal" -> <:ast< (CCLPATTERN) >>
      | id = identarg -> <:ast< (HYPPATTERN $id) >> ] ]
  ;
  ne_pattern_hyp_list:
    [ [ l = LIST1 pattern_occ_hyp -> l ] ]
  ;
  one_intropattern:
    [ [ p= ne_intropattern ->  <:ast< (INTROPATTERN $p)>> ]]
  ;
  ne_intropattern:
    [ [   tc = LIST1 simple_intropattern -> 
           <:ast< (LISTPATTERN ($LIST $tc))>> ] ]
  ;
  simple_intropattern:
    [ [ "["; tc = LIST1 intropattern  SEP "|" ; "]" -> 
         <:ast< (DISJPATTERN ($LIST $tc)) >>
      | "("; tc = LIST1 intropattern SEP "," ; ")" -> 
         <:ast< (CONJPATTERN ($LIST $tc)) >>
      | id = identarg                   -> 
         <:ast< (IDENTIFIER $id) >> ] ]
  ;
  intropattern:
    [ [   tc = LIST1 simple_intropattern -> 
              <:ast< (LISTPATTERN ($LIST $tc))>>
         | -> <:ast< (LISTPATTERN) >> ]]
  ;
  simple_binding:
    [ [ id = identarg; ":="; c = comarg -> <:ast< (BINDING $id $c) >>
      | n = numarg; ":="; c = comarg -> <:ast< (BINDING $n $c) >> ] ]
  ;
  simple_binding_list:
    [ [ b = simple_binding; l = simple_binding_list -> b :: l | -> [] ] ]
  ;
  com_binding_list:
    [ [ c = comarg; bl = com_binding_list -> <:ast< (BINDING $c) >> :: bl
      | -> [] ] ]
  ;
  binding_list:
    [ [ c1 = comarg; ":="; c2 = comarg; bl = simple_binding_list ->
          let id = match c1 with 
            | CoqAst.Node(_,"COMMAND",[c]) -> coerce_to_var "c1" c
            | _ -> assert false
          in <:ast<(BINDINGS (BINDING ($VAR $id) $c2) ($LIST $bl))>>
      | n = numarg; ":="; c = comarg; bl = simple_binding_list ->
          <:ast<(BINDINGS (BINDING $n $c) ($LIST $bl))>>
      | c1 = comarg; bl = com_binding_list ->
          <:ast<(BINDINGS (BINDING $c1) ($LIST $bl))>>
      | -> <:ast<(BINDINGS)>> ] ]
  ;
  with_binding_list:
    [ [ "with"; l = binding_list -> l | -> <:ast<(BINDINGS)>> ] ]
  ;
  comarg_binding_list:
    [ [ c = comarg; l = with_binding_list -> [c; l] ] ]
  ;
  numarg_binding_list:
    [ [ n = numarg; l = with_binding_list -> [n; l] ] ]
  ;
  comarg_list:
    [ [ c = comarg; l = comarg_list -> c :: l | -> [] ] ]
  ;
  unfold_occ:
    [ [ nl = ne_num_list; c = identarg -> <:ast< (UNFOLD $c ($LIST $nl)) >>
      | c = identarg -> <:ast< (UNFOLD $c) >> ] ]
  ;
  ne_unfold_occ_list:
    [ [ p = unfold_occ; l = ne_unfold_occ_list -> p :: l
      | p = unfold_occ -> [p] ] ]
  ;
  red_flag:
    [ [ LIDENT "Beta" -> <:ast< (Beta) >>
      | LIDENT "Delta" -> <:ast< (Delta) >>
      | LIDENT "Iota" -> <:ast< (Iota) >>
      | "["; idl = ne_identarg_list; "]" -> <:ast< (Unf ($LIST idl)) >>
      | "-"; "["; idl = ne_identarg_list; "]" ->
          <:ast< (UnfBut ($LIST idl)) >> ] ]
  ;
  red_tactic:
    [ [ LIDENT "Red" -> <:ast< (Red) >>
      | LIDENT "Hnf" -> <:ast< (Hnf) >>
      | LIDENT "Simpl" -> <:ast< (Simpl) >>
      | LIDENT "Cbv"; s = LIST1 red_flag -> <:ast< (Cbv ($LIST s)) >>
      | LIDENT "Lazy"; s = LIST1 red_flag -> <:ast< (Lazy ($LIST s)) >>
      | LIDENT "Compute" -> <:ast< (Cbv (Beta) (Delta) (Iota)) >>
      | LIDENT "Unfold"; ul = ne_unfold_occ_list ->
          <:ast< (Unfold ($LIST ul)) >>
      | LIDENT "Fold"; cl = comarg_list -> <:ast< (Fold ($LIST cl)) >>
      | LIDENT "Change"; c = comarg -> <:ast< (Change $c) >>
      | LIDENT "Pattern"; pl = ne_pattern_list ->
          <:ast< (Pattern ($LIST $pl)) >> ] ]
  ;
  clausearg:
    [ [ "in"; idl = ne_identarg_list -> <:ast< (CLAUSE ($LIST idl)) >>
      | -> <:ast< (CLAUSE) >> ] ]
  ;
  autoarg_depth:
  [ [ n = numarg -> <:ast< $n>>
     | -> CoqAst.Str(loc,"NoAutoArg") ] ]
  ;
  autoarg_adding:
  [ [ LIDENT "Adding" ; "["; l = ne_identarg_list; "]" -> 
        <:ast< (CLAUSE ($LIST $l))>>
      | -> <:ast< (CLAUSE) >> ] ]
  ;
  autoarg_destructing:
  [ [ LIDENT "Destructing" -> CoqAst.Str(loc,"Destructing")
      | -> CoqAst.Str(loc,"NoAutoArg") ] ]
  ;
  autoarg_usingTDB:
  [ [ "Using"; "TDB"  ->  CoqAst.Str(loc,"UsingTDB")
      | -> CoqAst.Str(loc,"NoAutoArg")  ] ]
  ;
  fixdecl:
    [ [ id = identarg; n = numarg; ":"; c = comarg; fd = fixdecl ->
          <:ast< (FIXEXP $id $n $c) >> :: fd
      | -> [] ] ]
  ;
  cofixdecl:
    [ [ id = identarg; ":"; c = comarg; fd = cofixdecl ->
          <:ast< (COFIXEXP $id $c) >> :: fd
      | -> [] ] ]
  ;
 END

(* Tactics grammar rules *)

GEXTEND Gram
  tactic_com_list:
    [ [ y = tactic_com; ";"; l = LIST1 tactic_com_tail SEP ";" ->
          <:ast< (TACTICLIST $y ($LIST $l)) >>
      | y = tactic_com -> <:ast< (TACTICLIST $y) >> ] ]
  ;
  tactic_com_tail:
    [ [ t1 = tactic_com -> t1
      | "["; l = LIST0 tactic_com_list SEP "|"; "]" ->
          <:ast< (TACLIST ($LIST $l)) >> ] ]
  ;
  tactic_com:
    [ [ st = simple_tactic; "Orelse"; tc = tactic_com ->
          <:ast< (ORELSE $st $tc) >>
      | st = simple_tactic -> st ] ]
  ;
  simple_tactic:
    [ [ LIDENT "Fix"; n = numarg -> <:ast< (Fix $n) >>
      | LIDENT "Fix"; id = identarg; n = numarg -> <:ast< (Fix $id $n) >>
      | LIDENT "Fix"; id = identarg; n = numarg; "with"; fd = fixdecl ->
          <:ast< (Fix $id $n ($LIST $fd)) >>
      | LIDENT "Cofix" -> <:ast< (Cofix) >>
      | LIDENT "Cofix"; id = identarg -> <:ast< (Cofix $id) >>
      | LIDENT "Cofix"; id = identarg; "with"; fd = cofixdecl ->
          <:ast< (Cofix $id ($LIST $fd)) >>
      | LIDENT "Induction"; s = identarg -> <:ast< (Induction $s) >>
      | LIDENT "Induction"; n = numarg -> <:ast< (Induction $n) >>
      | LIDENT "Double"; LIDENT "Induction"; i = numarg; j = numarg ->
          <:ast< (DoubleInd $i $j) >>
      | LIDENT "Trivial" -> <:ast<(Trivial)>>
      | LIDENT "Trivial"; "with"; lid = ne_identarg_list -> 
	  <:ast<(Trivial ($LIST $lid))>>
      | LIDENT "Trivial"; "with"; "*" ->  <:ast<(Trivial "*")>>
      | LIDENT "Auto"; n = numarg -> <:ast< (Auto $n) >>
      | LIDENT "Auto" -> <:ast< (Auto) >>
      | LIDENT "Auto"; n = numarg; "with";
	  lid = ne_identarg_list -> <:ast< (Auto $n ($LIST $lid)) >>
      | LIDENT "Auto"; "with";
	  lid = ne_identarg_list -> <:ast< (Auto ($LIST $lid)) >>
      | LIDENT "Auto"; n = numarg; "with"; "*" ->
	  <:ast< (Auto $n "*") >>
      | LIDENT "Auto"; "with"; "*" -> <:ast< (Auto "*") >>
     
      | LIDENT "AutoTDB"; n = numarg -> <:ast< (AutoTDB $n) >>
      | LIDENT "AutoTDB" -> <:ast< (AutoTDB) >>
      | LIDENT "DHyp";  id=identarg  -> <:ast< (DHyp  $id)>>
      | LIDENT "CDHyp"; id=identarg -> <:ast<  (CDHyp $id)>>
      | LIDENT "DConcl"  -> <:ast< (DConcl)>>
      | LIDENT "SuperAuto"; 
                       a0 = autoarg_depth;
                       a1 = autoarg_adding; 
                       a2 = autoarg_destructing; 
                       a3 = autoarg_usingTDB -> 
                   <:ast< (SuperAuto $a0 $a1 $a2 $a3) >>
      | LIDENT "Auto"; n = numarg; LIDENT "Decomp" -> <:ast< (DAuto $n) >>
      | LIDENT "Auto"; LIDENT "Decomp" -> <:ast< (DAuto) >>
      | LIDENT "Auto"; n = numarg; LIDENT "Decomp"; p = numarg-> <:ast< (DAuto $n $p) >>
      ]];
    END

GEXTEND Gram
 simple_tactic:
  [ [  LIDENT "Intros" -> <:ast< (Intros) >>
      | LIDENT "Intros"; LIDENT "until"; id = identarg 
                                              -> <:ast< (IntrosUntil $id) >>
      | LIDENT "Intros"; LIDENT "until"; n = numarg -> <:ast<(IntrosUntil $n)>>
      | LIDENT "Intros"; pl = one_intropattern -> <:ast< (Intros $pl) >>
      | LIDENT "Intro"; id = identarg; 
	  LIDENT "after"; id2 = identarg -> <:ast< (IntroMove $id $id2) >>
      | LIDENT "Intro";
	  LIDENT "after"; id2 = identarg -> <:ast< (IntroMove $id2) >>
      | LIDENT "Intro"; id = identarg -> <:ast< (Intro $id) >>
      | LIDENT "Intro" -> <:ast< (Intro) >>
      | LIDENT "Apply"; cl = comarg_binding_list ->
          <:ast< (Apply ($LIST $cl)) >>
      | LIDENT "Elim"; cl = comarg_binding_list; "using";
        el = comarg_binding_list ->
          <:ast< (Elim ($LIST $cl) ($LIST $el)) >>
      | LIDENT "Elim"; cl = comarg_binding_list ->
          <:ast< (Elim ($LIST $cl)) >>
      | LIDENT "Assumption" -> <:ast< (Assumption) >>
      | LIDENT "Contradiction" -> <:ast< (Contradiction) >>
      | LIDENT "Exact"; c = comarg -> <:ast< (Exact $c) >>
      | LIDENT "OldElim"; c = comarg -> <:ast< (OldElim $c) >>
      | LIDENT "ElimType"; c = comarg -> <:ast< (ElimType $c) >>
      | LIDENT "Case"; cl = comarg_binding_list ->
          <:ast< (Case ($LIST $cl)) >>
      | LIDENT "CaseType"; c = comarg -> <:ast< (CaseType $c) >>
      | LIDENT "Destruct"; s = identarg -> <:ast< (Destruct $s) >>
      | LIDENT "Destruct"; n = numarg -> <:ast< (Destruct $n) >>
      | LIDENT "Decompose"; LIDENT "Record" ; c = comarg -> 
             <:ast< (DecomposeAnd $c) >>
      | LIDENT "Decompose"; LIDENT "Sum"; c = comarg -> 
             <:ast< (DecomposeOr $c) >>
      | LIDENT "Decompose"; "["; l = ne_identarg_list; "]"; c = comarg ->
          <:ast< (DecomposeThese (CLAUSE ($LIST $l)) $c) >>
      |	LIDENT "First" ; "["; l = LIST0 tactic_com_list SEP "|"; "]" ->
          <:ast<(FIRST ($LIST $l))>>
      |	LIDENT "Solve" ; "["; l = LIST0 tactic_com_list SEP "|"; "]" ->
          <:ast<(TCLSOLVE ($LIST $l))>>
      | LIDENT "Cut"; c = comarg -> <:ast< (Cut $c) >>
      | LIDENT "Specialize"; n = numarg; lcb = comarg_binding_list ->
          <:ast< (Specialize $n ($LIST $lcb))>>
      | LIDENT "Specialize"; lcb = comarg_binding_list ->
          <:ast< (Specialize ($LIST $lcb)) >>
      | LIDENT "Generalize"; lc = comarg_list ->
          <:ast< (Generalize ($LIST $lc)) >>
      | LIDENT "Generalize"; LIDENT "Dependent"; c = comarg ->
          <:ast< (GeneralizeDep $c) >>
      | LIDENT "Let"; s = identarg; ":="; c = comarg; "in";
	  l = ne_pattern_hyp_list -> 
	    <:ast< (LetTac $s $c (LETPATTERNS ($LIST $l))) >>
      | LIDENT "LApply"; c = comarg -> <:ast< (CutAndApply $c) >>
      | LIDENT "Clear"; l = ne_identarg_list -> 
                <:ast< (Clear (CLAUSE ($LIST $l))) >>
      | LIDENT "Move"; id1 = identarg; LIDENT "after"; id2 = identarg -> 
                <:ast< (MoveDep $id1 $id2) >>
      | LIDENT "Do"; n = numarg; tc = tactic_com -> <:ast< (DO $n $tc) >>
      | LIDENT "Try"; tc = tactic_com -> <:ast< (TRY $tc) >>
      | LIDENT "Info"; tc = tactic_com -> <:ast< (INFO $tc) >>
      | LIDENT "Repeat"; tc = tactic_com -> <:ast< (REPEAT $tc) >>
      | LIDENT "Abstract"; tc = tactic_com -> <:ast< (ABSTRACT (TACTIC $tc)) >>
      | LIDENT "Abstract"; tc = tactic_com; "using";  s=identarg 
                                   -> <:ast< (ABSTRACT $s (TACTIC $tc)) >>
      | LIDENT "Left"; bl = with_binding_list -> <:ast< (Left $bl) >>
      | LIDENT "Right"; bl = with_binding_list -> <:ast< (Right $bl) >>
      | LIDENT "Split"; bl = with_binding_list -> <:ast< (Split $bl) >>
      | LIDENT "Exists"; bl = binding_list -> <:ast< (Split $bl) >>
      | LIDENT "Constructor"; nbl = numarg_binding_list ->
          <:ast<(Constructor ($LIST $nbl)) >>
      | LIDENT "Constructor" -> <:ast<(Constructor) >>
      | LIDENT "Reflexivity" -> <:ast< (Reflexivity) >>
      | LIDENT "Symmetry" -> <:ast< (Symmetry) >>
      | LIDENT "Transitivity"; c = comarg -> <:ast< (Transitivity $c) >>
      | LIDENT "Absurd"; c = comarg -> <:ast< (Absurd $c) >>
      | LIDENT "Idtac" -> <:ast< (Idtac) >>
      | LIDENT "Fail" -> <:ast< (Fail) >>
      | "("; tcl = tactic_com_list; ")" -> tcl
      | r = red_tactic; cl = clausearg -> <:ast< (Reduce (REDEXP $r) $cl) >> ]

    | [ id = identarg; l = comarg_list ->
          match (isMeta (nvar_of_ast id), l) with
            | (true, []) -> id
            | (false, _) -> <:ast< (CALL $id ($LIST $l)) >>
            | _ -> user_err_loc
                  (loc, "G_tactic.meta_tactic",
                   [< 'sTR"Cannot apply arguments to a meta-tactic." >])
      ] ]
  ;
  tactic:
    [ [ tac = tactic_com_list -> tac ] ]
  ;
END
