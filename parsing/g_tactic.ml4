
(* $Id$ *)

open Pp
open Ast
open Pcoq

open Tactic

(* Please leave several GEXTEND for modular compilation under PowerPC *)

(* Auxiliary grammar rules *)

GEXTEND Gram

  identarg:
    [ [ id = IDENT -> <:ast< ($VAR $id) >> ] ]
  ;
  numarg:
    [ [ n = Prim.number -> n
      | "-"; n = Prim.number -> Coqast.Num (Ast.loc n, ( - Ast.num_of_ast n))
      ] ]
  ;
  comarg:
    [ [ c = Constr.constr -> <:ast< (COMMAND $c) >> ] ]
  ;
  lcomarg:
    [ [ c = Constr.lconstr -> <:ast< (COMMAND $c) >> ] ]
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
    [ [ nl = ne_num_list; IDENT "Goal" -> <:ast<(CCLPATTERN ($LIST $nl))>>
      | nl = ne_num_list; id = identarg -> <:ast<(HYPPATTERN $id ($LIST $nl))>>
      | IDENT "Goal" -> <:ast< (CCLPATTERN) >>
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
            | Coqast.Node(_,"COMMAND",[c]) -> coerce_to_var "c1" c
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
    [ [ IDENT "Beta" -> <:ast< (Beta) >>
      | IDENT "Delta" -> <:ast< (Delta) >>
      | IDENT "Iota" -> <:ast< (Iota) >>
      | "["; idl = ne_identarg_list; "]" -> <:ast< (Unf ($LIST idl)) >>
      | "-"; "["; idl = ne_identarg_list; "]" ->
          <:ast< (UnfBut ($LIST idl)) >> ] ]
  ;
  red_tactic:
    [ [ IDENT "Red" -> <:ast< (Red) >>
      | IDENT "Hnf" -> <:ast< (Hnf) >>
      | IDENT "Simpl" -> <:ast< (Simpl) >>
      | IDENT "Cbv"; s = LIST1 red_flag -> <:ast< (Cbv ($LIST s)) >>
      | IDENT "Lazy"; s = LIST1 red_flag -> <:ast< (Lazy ($LIST s)) >>
      | IDENT "Compute" -> <:ast< (Cbv (Beta) (Delta) (Iota)) >>
      | IDENT "Unfold"; ul = ne_unfold_occ_list ->
          <:ast< (Unfold ($LIST ul)) >>
      | IDENT "Fold"; cl = comarg_list -> <:ast< (Fold ($LIST cl)) >>
      | IDENT "Pattern"; pl = ne_pattern_list ->
          <:ast< (Pattern ($LIST $pl)) >> ] ]
  ;
  clausearg:
    [ [ "in"; idl = ne_identarg_list -> <:ast< (CLAUSE ($LIST idl)) >>
      | -> <:ast< (CLAUSE) >> ] ]
  ;
  autoarg_depth:
  [ [ n = numarg -> <:ast< $n>>
     | -> Coqast.Str(loc,"NoAutoArg") ] ]
  ;
  autoarg_adding:
  [ [ IDENT "Adding" ; "["; l = ne_identarg_list; "]" -> 
        <:ast< (CLAUSE ($LIST $l))>>
      | -> <:ast< (CLAUSE) >> ] ]
  ;
  autoarg_destructing:
  [ [ IDENT "Destructing" -> Coqast.Str(loc,"Destructing")
      | -> Coqast.Str(loc,"NoAutoArg") ] ]
  ;
  autoarg_usingTDB:
  [ [ "Using"; "TDB"  ->  Coqast.Str(loc,"UsingTDB")
      | -> Coqast.Str(loc,"NoAutoArg")  ] ]
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
    [ [ IDENT "Fix"; n = numarg -> <:ast< (Fix $n) >>
      | IDENT "Fix"; id = identarg; n = numarg -> <:ast< (Fix $id $n) >>
      | IDENT "Fix"; id = identarg; n = numarg; "with"; fd = fixdecl ->
          <:ast< (Fix $id $n ($LIST $fd)) >>
      | IDENT "Cofix" -> <:ast< (Cofix) >>
      | IDENT "Cofix"; id = identarg -> <:ast< (Cofix $id) >>
      | IDENT "Cofix"; id = identarg; "with"; fd = cofixdecl ->
          <:ast< (Cofix $id ($LIST $fd)) >>
      | IDENT "Induction"; s = identarg -> <:ast< (Induction $s) >>
      | IDENT "Induction"; n = numarg -> <:ast< (Induction $n) >>
      | IDENT "Double"; IDENT "Induction"; i = numarg; j = numarg ->
          <:ast< (DoubleInd $i $j) >>
      | IDENT "Trivial" -> <:ast<(Trivial)>>
      | IDENT "Trivial"; "with"; lid = ne_identarg_list -> 
	  <:ast<(Trivial ($LIST $lid))>>
      | IDENT "Trivial"; "with"; "*" ->  <:ast<(Trivial "*")>>
      | IDENT "Auto"; n = numarg -> <:ast< (Auto $n) >>
      | IDENT "Auto" -> <:ast< (Auto) >>
      | IDENT "Auto"; n = numarg; "with";
	  lid = ne_identarg_list -> <:ast< (Auto $n ($LIST $lid)) >>
      | IDENT "Auto"; "with";
	  lid = ne_identarg_list -> <:ast< (Auto ($LIST $lid)) >>
      | IDENT "Auto"; n = numarg; "with"; "*" ->
	  <:ast< (Auto $n "*") >>
      | IDENT "Auto"; "with"; "*" -> <:ast< (Auto "*") >>
     
      | IDENT "AutoTDB"; n = numarg -> <:ast< (AutoTDB $n) >>
      | IDENT "AutoTDB" -> <:ast< (AutoTDB) >>
      | IDENT "DHyp";  id=identarg  -> <:ast< (DHyp  $id)>>
      | IDENT "CDHyp"; id=identarg -> <:ast<  (CDHyp $id)>>
      | IDENT "DConcl"  -> <:ast< (DConcl)>>
      | IDENT "SuperAuto"; 
                       a0 = autoarg_depth;
                       a1 = autoarg_adding; 
                       a2 = autoarg_destructing; 
                       a3 = autoarg_usingTDB -> 
                   <:ast< (SuperAuto $a0 $a1 $a2 $a3) >>
      | IDENT "Auto"; n = numarg; IDENT "Decomp" -> <:ast< (DAuto $n) >>
      | IDENT "Auto"; IDENT "Decomp" -> <:ast< (DAuto) >>
      | IDENT "Auto"; n = numarg; IDENT "Decomp"; p = numarg-> <:ast< (DAuto $n $p) >>
      ]];
    END

GEXTEND Gram
 simple_tactic:
  [ [  IDENT "Intros" -> <:ast< (Intros) >>
      | IDENT "Intros"; IDENT "until"; id = identarg 
                                              -> <:ast< (IntrosUntil $id) >>
      | IDENT "Intros"; IDENT "until"; n = numarg -> <:ast<(IntrosUntil $n)>>
      | IDENT "Intros"; pl = one_intropattern -> <:ast< (Intros $pl) >>
      | IDENT "Intro"; id = identarg; 
	  IDENT "after"; id2 = identarg -> <:ast< (IntroMove $id $id2) >>
      | IDENT "Intro";
	  IDENT "after"; id2 = identarg -> <:ast< (IntroMove $id2) >>
      | IDENT "Intro"; id = identarg -> <:ast< (Intro $id) >>
      | IDENT "Intro" -> <:ast< (Intro) >>
      | IDENT "Apply"; cl = comarg_binding_list ->
          <:ast< (Apply ($LIST $cl)) >>
      | IDENT "Elim"; cl = comarg_binding_list; "using";
        el = comarg_binding_list ->
          <:ast< (Elim ($LIST $cl) ($LIST $el)) >>
      | IDENT "Elim"; cl = comarg_binding_list ->
          <:ast< (Elim ($LIST $cl)) >>
      | IDENT "Assumption" -> <:ast< (Assumption) >>
      | IDENT "Contradiction" -> <:ast< (Contradiction) >>
      | IDENT "Exact"; c = comarg -> <:ast< (Exact $c) >>
      | IDENT "OldElim"; c = comarg -> <:ast< (OldElim $c) >>
      | IDENT "ElimType"; c = comarg -> <:ast< (ElimType $c) >>
      | IDENT "Case"; cl = comarg_binding_list ->
          <:ast< (Case ($LIST $cl)) >>
      | IDENT "CaseType"; c = comarg -> <:ast< (CaseType $c) >>
      | IDENT "Destruct"; s = identarg -> <:ast< (Destruct $s) >>
      | IDENT "Destruct"; n = numarg -> <:ast< (Destruct $n) >>
      | IDENT "Decompose"; IDENT "Record" ; c = comarg -> 
             <:ast< (DecomposeAnd $c) >>
      | IDENT "Decompose"; IDENT "Sum"; c = comarg -> 
             <:ast< (DecomposeOr $c) >>
      | IDENT "Decompose"; "["; l = ne_identarg_list; "]"; c = comarg ->
          <:ast< (DecomposeThese (CLAUSE ($LIST $l)) $c) >>
      |	IDENT "First" ; "["; l = LIST0 tactic_com_list SEP "|"; "]" ->
          <:ast<(FIRST ($LIST $l))>>
      |	IDENT "Solve" ; "["; l = LIST0 tactic_com_list SEP "|"; "]" ->
          <:ast<(TCLSOLVE ($LIST $l))>>
      | IDENT "Cut"; c = comarg -> <:ast< (Cut $c) >>
      | IDENT "Specialize"; n = numarg; lcb = comarg_binding_list ->
          <:ast< (Specialize $n ($LIST $lcb))>>
      | IDENT "Specialize"; lcb = comarg_binding_list ->
          <:ast< (Specialize ($LIST $lcb)) >>
      | IDENT "Generalize"; lc = comarg_list ->
          <:ast< (Generalize ($LIST $lc)) >>
      | IDENT "Generalize"; IDENT "Dependent"; c = comarg ->
          <:ast< (GeneralizeDep $c) >>
      | IDENT "Let"; s = identarg; ":="; c = comarg; "in";
	  l = ne_pattern_hyp_list -> 
	    <:ast< (LetTac $s $c (LETPATTERNS ($LIST $l))) >>
      | IDENT "LApply"; c = comarg -> <:ast< (CutAndApply $c) >>
      | IDENT "Clear"; l = ne_identarg_list -> 
                <:ast< (Clear (CLAUSE ($LIST $l))) >>
      | IDENT "Move"; id1 = identarg; IDENT "after"; id2 = identarg -> 
                <:ast< (MoveDep $id1 $id2) >>
      | IDENT "Do"; n = numarg; tc = tactic_com -> <:ast< (DO $n $tc) >>
      | IDENT "Try"; tc = tactic_com -> <:ast< (TRY $tc) >>
      | IDENT "Info"; tc = tactic_com -> <:ast< (INFO $tc) >>
      | IDENT "Repeat"; tc = tactic_com -> <:ast< (REPEAT $tc) >>
      | IDENT "Abstract"; tc = tactic_com -> <:ast< (ABSTRACT (TACTIC $tc)) >>
      | IDENT "Abstract"; tc = tactic_com; "using";  s=identarg 
                                   -> <:ast< (ABSTRACT $s (TACTIC $tc)) >>
      | IDENT "Left"; bl = with_binding_list -> <:ast< (Left $bl) >>
      | IDENT "Right"; bl = with_binding_list -> <:ast< (Right $bl) >>
      | IDENT "Split"; bl = with_binding_list -> <:ast< (Split $bl) >>
      | IDENT "Exists"; bl = binding_list -> <:ast< (Split $bl) >>
      | IDENT "Constructor"; nbl = numarg_binding_list ->
          <:ast<(Constructor ($LIST $nbl)) >>
      | IDENT "Constructor" -> <:ast<(Constructor) >>
      | IDENT "Reflexivity" -> <:ast< (Reflexivity) >>
      | IDENT "Symmetry" -> <:ast< (Symmetry) >>
      | IDENT "Transitivity"; c = comarg -> <:ast< (Transitivity $c) >>
      | IDENT "Absurd"; c = comarg -> <:ast< (Absurd $c) >>
      | IDENT "Idtac" -> <:ast< (Idtac) >>
      | IDENT "Fail" -> <:ast< (Fail) >>
      | "("; tcl = tactic_com_list; ")" -> tcl
      | r = red_tactic; cl = clausearg -> <:ast< (Reduce (REDEXP $r) $cl) >>
      (* Change ne doit pas s'appliquer dans un Definition t := Eval ... *)
      | IDENT "Change"; c = comarg; cl = clausearg ->
	  <:ast< (Change $c $cl) >> 
      | IDENT "ML"; s = Prim.string -> <:ast< (MLTACTIC $s) >> ]

    | [ id = identarg; l = comarg_list ->
          match (isMeta (nvar_of_ast id), l) with
            | (true, []) -> id
            | (false, _) -> <:ast< (CALL $id ($LIST $l)) >>
            | _ -> Util.user_err_loc
                  (loc, "G_tactic.meta_tactic",
                   [< 'sTR"Cannot apply arguments to a meta-tactic." >])
      ] ]
  ;
  tactic:
    [ [ tac = tactic_com_list -> tac ] ]
  ;
END
