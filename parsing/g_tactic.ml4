(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i camlp4deps: "parsing/grammar.cma" i*)

(* $Id$ *)

open Pp
open Ast
open Pcoq
open Tactic
open Util

(* Please leave several GEXTEND for modular compilation under PowerPC *)

(* Auxiliary grammar rules *)

GEXTEND Gram
  GLOBAL: autoargs;

  autoarg_depth:
  [ [ n = pure_numarg -> <:ast< $n>>
     | -> Coqast.Str(loc,"NoAutoArg") ] ]
  ;
  autoarg_adding:
  [ [ IDENT "Adding" ; "["; l = ne_qualidarg_list; "]" -> l
      | -> [] ] ]
  ;
  autoarg_destructing:
  [ [ IDENT "Destructing" -> Coqast.Str(loc,"Destructing")
      | -> Coqast.Str(loc,"NoAutoArg") ] ]
  ;
  autoarg_usingTDB:
  [ [ "Using"; "TDB"  ->  Coqast.Str(loc,"UsingTDB")
      | -> Coqast.Str(loc,"NoAutoArg")  ] ]
  ;
  autoargs:
  [ [ a0 = autoarg_depth; l = autoarg_adding; 
      a2 = autoarg_destructing; a3 = autoarg_usingTDB -> a0::a2::a3::l ] ]
  ;
  END

GEXTEND Gram

  identarg:
    [ [ id = Constr.ident -> id ] ]
  ;
  idmeta_arg:
    [ [ id = Constr.ident -> id
      | "?"; n = Prim.number -> <:ast< (COMMAND (META $n)) >> ] ]
  ;
  idmetahyp:
    [ [ id = idmeta_arg -> <:ast< (INHYP $id) >> ] ]
  ;
  qualidarg:
    [ [ l = Constr.qualid -> <:ast< (QUALIDARG ($LIST $l)) >>
      | "?"; n = Prim.number -> <:ast< (QUALIDMETA $n) >> ] ]
  ;
  pure_numarg:
     [ [ n = Prim.number -> n
       | "-"; n = Prim.number -> Coqast.Num (Ast.loc n, ( - Ast.num_of_ast n))
     ] ]
  ;
  numarg:
    [ [ n = Prim.number -> n
      | "-"; n = Prim.number -> Coqast.Num (Ast.loc n, ( - Ast.num_of_ast n))
      |	id = identarg -> id
      ] ]
  ;
  constrarg:
    [ [ c = Constr.constr -> <:ast< (COMMAND $c) >> ] ]
  ;
  castedopenconstrarg:
    [ [ c = Constr.constr -> <:ast< (CASTEDOPENCOMMAND $c) >> ] ]
  ;
  lconstrarg:
    [ [ c = Constr.lconstr -> <:ast< (COMMAND $c) >> ] ]
  ;
  castedconstrarg:
    [ [ c = Constr.constr -> <:ast< (CASTEDCOMMAND $c) >> ] ]
  ;
  ident_or_numarg:
    [ [ id = identarg -> id
      | n = numarg -> n ] ]
  ;
  ident_or_constrarg:
    [ [ c = Constr.constr ->
	  match c with
            | Coqast.Nvar(_,s) -> c
	    | Coqast.Node(_,"QUALID",[Coqast.Nvar(_,s) as c]) -> c
	    | _ -> <:ast< (COMMAND $c) >> ] ]
  ;
  ne_identarg_list:
    [ [ l = LIST1 identarg -> l ] ]
  ;
  ne_idmetahyp_list:
    [ [ l = LIST1 idmetahyp -> l ] ]
  ;
  ne_qualidarg_list:
    [ [ l = LIST1 qualidarg -> l ] ]
  ;
  pattern_occ:
    [ [ nl = LIST1 pure_numarg; c = constrarg ->
         <:ast< (PATTERN $c ($LIST $nl)) >>
      | c = constrarg -> <:ast< (PATTERN $c) >> ] ]
  ;
  ne_pattern_list:
    [ [ l = LIST1 pattern_occ -> l ] ]
  ;
  pattern_occ_hyp:
    [ [ nl = LIST1 pure_numarg; IDENT "Goal" ->
          <:ast<(CCLPATTERN ($LIST $nl))>>
      | nl = LIST1 pure_numarg; id = identarg ->
          <:ast<(HYPPATTERN $id ($LIST $nl))>>
      | IDENT "Goal" -> <:ast< (CCLPATTERN) >>
      | id = identarg -> <:ast< (HYPPATTERN $id) >> ] ]
  ;
  clause_pattern:
    [ [ "in"; l = LIST1 pattern_occ_hyp -> <:ast< (LETPATTERNS ($LIST $l)) >>
      | -> <:ast< (LETPATTERNS) >> ] ]
  ;
  one_intropattern:
    [ [ p= ne_intropattern ->  <:ast< (INTROPATTERN $p)>> ]]
  ;
  ne_intropattern:
    [ [ tc = LIST1 simple_intropattern -> 
          <:ast< (LISTPATTERN ($LIST $tc))>> ] ]
  ;
  simple_intropattern:
    [ [ "["; tc = LIST1 intropattern  SEP "|" ; "]" -> 
         <:ast< (DISJPATTERN ($LIST $tc)) >>
      | "("; tc = LIST1 intropattern SEP "," ; ")" -> 
         <:ast< (CONJPATTERN ($LIST $tc)) >>
      | IDENT "_" -> 
	 <:ast< (WILDCAR) >>
      | id = identarg                   -> 
         <:ast< (IDENTIFIER $id) >> 
      ] ]
  ;
  intropattern:
    [ [   tc = LIST1 simple_intropattern -> 
              <:ast< (LISTPATTERN ($LIST $tc))>>
         | -> <:ast< (LISTPATTERN) >> ]]
  ;
  simple_binding:
    [ [ id = identarg; ":="; c = constrarg -> <:ast< (BINDING $id $c) >>
      | n = pure_numarg; ":="; c = constrarg -> <:ast< (BINDING $n $c) >> ] ]
  ;
  simple_binding_list:
    [ [ b = simple_binding; l = simple_binding_list -> b :: l | -> [] ] ]
  ;
  com_binding_list:
    [ [ c = constrarg; bl = com_binding_list -> <:ast< (BINDING $c) >> :: bl
      | -> [] ] ]
  ;
  binding_list:
    [ [ c1 = constrarg; ":="; c2 = constrarg; bl = simple_binding_list ->
          let id = match c1 with 
            | Coqast.Node(_,"COMMAND",[c]) -> coerce_to_var c
            | _ -> assert false
          in <:ast<(BINDINGS (BINDING $id $c2) ($LIST $bl))>>
      | n = pure_numarg; ":="; c = constrarg; bl = simple_binding_list ->
          <:ast<(BINDINGS (BINDING $n $c) ($LIST $bl))>>
      | c1 = constrarg; bl = com_binding_list ->
          <:ast<(BINDINGS (BINDING $c1) ($LIST $bl))>>
      | -> <:ast<(BINDINGS)>> ] ]
  ;
  with_binding_list:
    [ [ "with"; l = binding_list -> l | -> <:ast<(BINDINGS)>> ] ]
  ;
  constrarg_binding_list:
    [ [ c = constrarg; l = with_binding_list -> [c; l] ] ]
  ;
  numarg_binding_list:
    [ [ n = numarg; l = with_binding_list -> [n; l] ] ]
  ;
  constrarg_list:
    [ [ c = constrarg; l = constrarg_list -> c :: l | -> [] ] ]
  ;
  unfold_occ:
    [ [ nl = LIST1 pure_numarg; c = qualidarg ->
         <:ast< (UNFOLD $c ($LIST $nl)) >>
      | c = qualidarg -> <:ast< (UNFOLD $c) >> ] ]
  ;
  ne_unfold_occ_list:
    [ [ p = unfold_occ; l = ne_unfold_occ_list -> p :: l
      | p = unfold_occ -> [p] ] ]
  ;
  red_flag:
    [ [ IDENT "Beta" -> <:ast< (Beta) >>
      | IDENT "Delta" -> <:ast< (Delta) >>
      | IDENT "Iota" -> <:ast< (Iota) >>
      | IDENT "Zeta" -> <:ast< (Zeta) >>
      | "["; idl = ne_qualidarg_list; "]" -> <:ast< (Unf ($LIST $idl)) >>
      | "-"; "["; idl = ne_qualidarg_list; "]" ->
          <:ast< (UnfBut ($LIST $idl)) >> ] ]
  ;
  red_tactic:
    [ [ IDENT "Red" -> <:ast< (Red) >>
      | IDENT "Hnf" -> <:ast< (Hnf) >>
      | IDENT "Simpl" -> <:ast< (Simpl) >>
      | IDENT "Cbv"; s = LIST1 red_flag -> <:ast< (Cbv ($LIST $s)) >>
      | IDENT "Lazy"; s = LIST1 red_flag -> <:ast< (Lazy ($LIST $s)) >>
      | IDENT "Compute" -> <:ast< (Cbv (Beta) (Delta) (Iota) (Zeta)) >>
      | IDENT "Unfold"; ul = ne_unfold_occ_list ->
          <:ast< (Unfold ($LIST $ul)) >>
      | IDENT "Fold"; cl = constrarg_list -> <:ast< (Fold ($LIST $cl)) >>
      | IDENT "Pattern"; pl = ne_pattern_list ->
          <:ast< (Pattern ($LIST $pl)) >> ] ]
  ;
  hypident:
    [ [ id = identarg -> <:ast< (INHYP $id) >>
      | "("; "Type"; "of"; id = identarg; ")" -> <:ast< (INHYPTYPE $id) >> ] ]
  ;
  ne_hyp_list:
    [ [ l = LIST1 hypident -> l ] ]
  ;
  clausearg:
    [ [ "in"; idl = ne_hyp_list -> <:ast< (CLAUSE ($LIST $idl)) >>
      | -> <:ast< (CLAUSE) >> ] ]
  ;
  fixdecl:
    [ [ id = identarg; n = pure_numarg; ":"; c = constrarg; fd = fixdecl ->
          <:ast< (FIXEXP $id $n $c) >> :: fd
      | -> [] ] ]
  ;
  cofixdecl:
    [ [ id = identarg; ":"; c = constrarg; fd = cofixdecl ->
          <:ast< (COFIXEXP $id $c) >> :: fd
      | -> [] ] ]
  ;
  simple_tactic:
    [ [ IDENT "Fix"; n = pure_numarg -> <:ast< (Fix $n) >>
      | IDENT "Fix"; id = identarg; n = pure_numarg -> <:ast< (Fix $id $n) >>
      | IDENT "Fix"; id = identarg; n = pure_numarg; "with"; fd = fixdecl ->
          <:ast< (Fix $id $n ($LIST $fd)) >>
      | IDENT "Cofix" -> <:ast< (Cofix) >>
      | IDENT "Cofix"; id = identarg -> <:ast< (Cofix $id) >>
      | IDENT "Cofix"; id = identarg; "with"; fd = cofixdecl ->
          <:ast< (Cofix $id ($LIST $fd)) >>
      | IDENT "Induction"; s = identarg -> <:ast< (Induction $s) >>
      | IDENT "Induction"; n = pure_numarg -> <:ast< (Induction $n) >>
      | IDENT "NewInduction"; c=ident_or_constrarg -> <:ast<(NewInduction $c)>>
      | IDENT "NewInduction"; n = pure_numarg -> <:ast< (NewInduction $n) >>
      | IDENT "Double"; IDENT "Induction"; i = pure_numarg; j = pure_numarg ->
          <:ast< (DoubleInd $i $j) >>
      | IDENT "Trivial" -> <:ast<(Trivial)>>
      | IDENT "Trivial"; "with"; lid = ne_identarg_list -> 
	  <:ast<(Trivial ($LIST $lid))>>
      | IDENT "Trivial"; "with"; "*" ->  <:ast<(Trivial "*")>>
      | IDENT "Auto"; n = pure_numarg -> <:ast< (Auto $n) >>
      | IDENT "Auto" -> <:ast< (Auto) >>
      | IDENT "Auto"; n = pure_numarg; "with";
	  lid = ne_identarg_list -> <:ast< (Auto $n ($LIST $lid)) >>
      | IDENT "Auto"; "with";
	  lid = ne_identarg_list -> <:ast< (Auto ($LIST $lid)) >>
      | IDENT "Auto"; n = pure_numarg; "with"; "*" ->
	  <:ast< (Auto $n "*") >>
      | IDENT "Auto"; "with"; "*" -> <:ast< (Auto "*") >>
     
      | IDENT "AutoTDB"; n = pure_numarg -> <:ast< (AutoTDB $n) >>
      | IDENT "AutoTDB" -> <:ast< (AutoTDB) >>
      | IDENT "DHyp";  id=identarg  -> <:ast< (DHyp  $id)>>
      | IDENT "CDHyp"; id=identarg -> <:ast<  (CDHyp $id)>>
      | IDENT "DConcl"  -> <:ast< (DConcl)>>
      | IDENT "SuperAuto"; l = autoargs ->
                   <:ast< (SuperAuto ($LIST $l)) >>
      | IDENT "Auto"; n = pure_numarg; IDENT "Decomp" -> <:ast< (DAuto $n) >>
      | IDENT "Auto"; IDENT "Decomp" -> <:ast< (DAuto) >>
      | IDENT "Auto"; n = pure_numarg; IDENT "Decomp"; p = pure_numarg ->
          <:ast< (DAuto $n $p) >>
      | IDENT "Intros" -> <:ast< (Intros) >>
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
      | IDENT "Apply"; cl = constrarg_binding_list ->
          <:ast< (Apply ($LIST $cl)) >>
      | IDENT "Elim"; cl = constrarg_binding_list; "using";
        el = constrarg_binding_list ->
          <:ast< (Elim ($LIST $cl) ($LIST $el)) >>
      | IDENT "Elim"; cl = constrarg_binding_list ->
          <:ast< (Elim ($LIST $cl)) >>
      | IDENT "Assumption" -> <:ast< (Assumption) >>
      | IDENT "Contradiction" -> <:ast< (Contradiction) >>
      | IDENT "Exact"; c = castedconstrarg -> <:ast< (Exact $c) >>
      | IDENT "OldElim"; c = constrarg -> <:ast< (OldElim $c) >>
      | IDENT "ElimType"; c = constrarg -> <:ast< (ElimType $c) >>
      | IDENT "Case"; cl = constrarg_binding_list ->
          <:ast< (Case ($LIST $cl)) >>
      | IDENT "CaseType"; c = constrarg -> <:ast< (CaseType $c) >>
      | IDENT "Destruct"; s = ident_or_constrarg -> <:ast< (Destruct $s) >>
      | IDENT "Destruct"; n = numarg -> <:ast< (Destruct $n) >>
      | IDENT "NewDestruct"; s = ident_or_constrarg -> <:ast<(NewDestruct $s)>>
      | IDENT "NewDestruct"; n = numarg -> <:ast< (NewDestruct $n) >>
      | IDENT "Decompose"; IDENT "Record" ; c = constrarg -> 
             <:ast< (DecomposeAnd $c) >>
      | IDENT "Decompose"; IDENT "Sum"; c = constrarg -> 
             <:ast< (DecomposeOr $c) >>
      | IDENT "Decompose"; "["; l = ne_qualidarg_list; "]"; c = constrarg ->
          <:ast< (DecomposeThese $c ($LIST $l)) >>
      | IDENT "Cut"; c = constrarg -> <:ast< (Cut $c) >>
      | IDENT "Assert"; c = constrarg -> <:ast< (TrueCut $c) >>
      | IDENT "Assert"; c = constrarg; ":"; t = constrarg ->
          let id = match c with 
            | Coqast.Node(_,"COMMAND",[c]) -> coerce_to_var c
            | _ -> assert false in
	  <:ast< (TrueCut $t $id) >>
      | IDENT "Assert"; c = constrarg; ":="; t = constrarg ->
          let id = match c with 
            | Coqast.Node(_,"COMMAND",[c]) -> coerce_to_var c
            | _ -> assert false in
	  <:ast< (Forward $t $id) >>
      | IDENT "Specialize"; n = pure_numarg; lcb = constrarg_binding_list ->
          <:ast< (Specialize $n ($LIST $lcb))>>
      | IDENT "Specialize"; lcb = constrarg_binding_list ->
          <:ast< (Specialize ($LIST $lcb)) >>
      | IDENT "Generalize"; lc = constrarg_list ->
          <:ast< (Generalize ($LIST $lc)) >>
      | IDENT "Generalize"; IDENT "Dependent"; c = constrarg ->
          <:ast< (GeneralizeDep $c) >>
      | IDENT "LetTac"; s = identarg; ":="; c = constrarg; p = clause_pattern->
	  <:ast< (LetTac $s $c $p) >>
      | IDENT "LApply"; c = constrarg -> <:ast< (CutAndApply $c) >>
      | IDENT "Clear"; l = ne_idmetahyp_list -> 
                <:ast< (Clear (CLAUSE ($LIST $l))) >>
      | IDENT "ClearBody"; l = ne_idmetahyp_list -> 
                <:ast< (ClearBody (CLAUSE ($LIST $l))) >>
      | IDENT "Move"; id1 = identarg; IDENT "after"; id2 = identarg -> 
                <:ast< (MoveDep $id1 $id2) >>
(*To do: put Abstract in Refiner*)
      | IDENT "Abstract"; tc = tactic_expr -> <:ast< (ABSTRACT (TACTIC $tc)) >>
      | IDENT "Abstract"; tc = tactic_expr; "using";  s=identarg ->
          <:ast< (ABSTRACT $s (TACTIC $tc)) >>
(*End of To do*)
      | IDENT "Left"; bl = with_binding_list -> <:ast< (Left $bl) >>
      | IDENT "Right"; bl = with_binding_list -> <:ast< (Right $bl) >>
      | IDENT "Split"; bl = with_binding_list -> <:ast< (Split $bl) >>
      | IDENT "Exists"; bl = binding_list -> <:ast< (Split $bl) >>
      | IDENT "Constructor"; nbl = numarg_binding_list ->
          <:ast<(Constructor ($LIST $nbl)) >>
      | IDENT "Constructor" -> <:ast<(Constructor) >>
      | IDENT "Reflexivity" -> <:ast< (Reflexivity) >>
      | IDENT "Symmetry" -> <:ast< (Symmetry) >>
      | IDENT "Transitivity"; c = constrarg -> <:ast< (Transitivity $c) >>
      | IDENT "Absurd"; c = constrarg -> <:ast< (Absurd $c) >>
      | IDENT "Idtac" -> <:ast< (Idtac) >>
      | IDENT "Fail" -> <:ast< (Fail) >>
      | r = red_tactic; cl = clausearg -> <:ast< (Reduce (REDEXP $r) $cl) >>
      (* Change ne doit pas s'appliquer dans un Definition t := Eval ... *)
      | IDENT "Change"; c = constrarg; cl = clausearg ->
	  <:ast< (Change $c $cl) >> 
      | IDENT "ML"; s = Prim.string -> <:ast< (MLTACTIC $s) >> ]

 (*   | [ id = identarg; l = constrarg_list ->
          match (isMeta (nvar_of_ast id), l) with
            | (true, []) -> id
            | (false, _) -> <:ast< (CALL $id ($LIST $l)) >>
            | _ -> Util.user_err_loc
                  (loc, "G_tactic.meta_tactic",
                   [< 'sTR"Cannot apply arguments to a meta-tactic." >])
      ] *)]
  ;
  tactic:
    [ [ tac = tactic_expr -> tac ] ]
  ;
END;;
