(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

(* ======================================= *)
(*   PP rules for basic elements           *)
(* ======================================= *)

Syntax tactic
  level 3:
    interpret [<<(Interp (TACTIC $t))>>] -> [ $t:E ]
  ;

  level 3:
    | tacticlist_parsimp [<<(TACTICLISTPAR $tac0 $tac1)>>] ->
      [ $tac0 ";" [1 0] $tac1]
    | tacticlist_parcomp [<<(TACTICLISTPAR $tac0 (TACTICLIST $tac1 $tac2))>>]
      -> [ (TACTICLIST $tac0 (TACTICLIST $tac1 $tac2)) ]
  ;

  level 2:
  | tacticlist_simp [<<(TACTICLIST $tac0 $tac1)>>] ->
    [ $tac0 ";" [1 0] $tac1]
  | tacticlist_comp [<<(TACTICLIST $tac0 (TACTICLIST $tac1 $tac2))>>] ->
    [ $tac0 ";" [1 0] [<hov 0> (TACTICLISTPAR $tac1 $tac2):E] ]
  | tactic_seq [<<(TACLIST ($LIST $l))>>]
             -> [ [<hv 0> "[ " (TACTICSEQBODY ($LIST $l)) " ]" ] ]
  | tacticseqbody_cons [<<(TACTICSEQBODY $t ($LIST $l))>>]
      -> [ [<hov 0> $t] [1 0] "| " (TACTICSEQBODY ($LIST $l)) ]
  | tacticseqbody_one  [<<(TACTICSEQBODY $t)>>] -> [ [<hov 0> $t] ]

(* Match Context *)

  | term [<<(TERM $t)>>] -> [ $t ]
  | subterm [<<(SUBTERM ($VAR $id) $t)>>] -> [ $id "[" $t "]" ]
  | match_context_hyps_id [<<(MATCHCONTEXTHYPS ($VAR $id) $t)>>] ->
    [ $id [1 0] ":" [1 0] $t]
  | match_context_hyps_ano [<<(MATCHCONTEXTHYPS $t)>>] ->
    [ "_" [1 0] ":" [1 0] $t]
  | hyps_cons [<<(HYPS $hyp0 $hyp1 ($LIST $hyps))>>] ->
    [ $hyp0 ";" [1 0] (HYPS $hyp1 ($LIST $hyps)) ]
  | hyps_three [<<(HYPS $hyp $concl $tac)>>] ->
    [ $hyp [1 0] "|-" [1 0] $concl [1 0] "]" [1 0] "->" [1 2] $tac ]
  | hyps_two [<<(HYPS $concl $tac)>>] ->
    [ "|-" [1 0] $concl [1 0] "]" [1 0] "->" [1 2] $tac ]
  | match_context_rule [<<(MATCHCONTEXTRULE ($LIST $hyps))>>] ->
    [ "[" [1 0] (HYPS ($LIST $hyps)) ]
  | match_context_rule_cons [<<(MATCHCONTEXTLIST $rul ($LIST $lrul))>>] ->
    [ FNL "|" [1 0] $rul (MATCHCONTEXTLIST ($LIST $lrul)) ]
  | match_context_rule_one [<<(MATCHCONTEXTLIST $rul)>>] ->
    [ FNL "|" [1 0] $rul ]

(* Match *)

  | match_list_cons [<<(MATCHLIST $rul ($LIST $lrul))>>] ->
    [ $rul (MATCHLIST ($LIST $lrul)) ]
  | match_list_one [<<(MATCHLIST $rul)>>] -> [ $rul ]
  | match_rul_pat [<<(MATCHRULE $pat $tac)>>] ->
    [ FNL "|" [1 0] "[" [1 0] $pat [1 0] "]" [1 0] "->" [1 2] $tac ]
  | match_rul_all [<<(MATCHRULE $tac)>>] ->
    [ FNL "|" [1 0] "_" [1 0] "->" [1 2] $tac ]

(* Let *)

  | let_decl_cons [<<(LETDECL (LETCLAUSE ($LIST $rul)) ($LIST $lrul))>>] ->
    [ (LET ($LIST $rul)) (LETLIST ($LIST $lrul)) ]
  | let_decl_one [<<(LETDECL (LETCLAUSE ($LIST $rul)))>>] ->
    [ (LET ($LIST $rul)) ]
  | let_list_cons [<<(LETLIST (LETCLAUSE ($LIST $rul)) ($LIST $lrul))>>] ->
    [ (AND ($LIST $rul)) (LETLIST ($LIST $lrul)) ]
  | let_list_one [<<(LETLIST (LETCLAUSE ($LIST $rul)))>>] ->
    [ (AND ($LIST $rul)) ]
  | let_rule [<<(LET ($VAR $id) $tac)>>] ->
    [ $id [1 0] "=" [1 0] $tac ]
  | and_rule [<<(AND ($VAR $id) $tac)>>] ->
    [ FNL "And" [1 0] $id [1 0] "=" [1 0] $tac]
  ;

  level 1:
    orelse [ $st Orelse $tc ] -> [ [<hov 0> $st:L " Orelse" [1 1] $tc:E] ]
  ;

  level 0:

(* ============================= *)
(*       PP rules for LTAC       *)
(* ============================= *)

  | idtac  [<<(IDTAC)>>]            -> ["Idtac"]
  | fail   [<<(FAIL)>>]             -> ["Fail"]
  | do     [<<(DO ($NUM $n) $tc)>>] -> ["Go " $n " " $tc:E]
  | try    [<<(TRY $t)>>]           -> ["Try " $t:E]
  | info   [<<(INFO $t)>>]          -> ["Info " $t:E]
  | repeat [<<(REPEAT $tc)>>]       -> ["Repeat " $tc:E]
  | first  [<<(FIRST ($LIST $l))>>] ->
    ["First" [1 0] "[" [1 0] (TACTICSEQBODY ($LIST $l)) [1 0] "]"]
  | solve  [<<(TCLSOLVE ($LIST $l))>>] ->
    ["Solve" [1 0] "[" [1 0] (TACTICSEQBODY ($LIST $l)) [1 0] "]"]
  | abstract_anon [<<(ABSTRACT (TACTIC $t))>>] 
         -> ["Abstract " $t:E]
  | abstract_name [<<(ABSTRACT ($VAR $id) (TACTIC $t))>>] 
         -> ["Abstract " $t:E " using "  $id]
  | match_context [<<(MATCHCONTEXT ($LIST $lrul))>>] ->
    [ [0 0] "Match Context With" (MATCHCONTEXTLIST ($LIST $lrul))]
  | match [<<(MATCH $t ($LIST $lrul))>>] ->
    [ [0 0] "Match" [1 0] $t [1 0] "With" (MATCHLIST ($LIST $lrul)) ]
  | let [<<(LET (LETDECL ($LIST $llc)) $u)>>] ->
    [ [0 0] "Let" [1 0] (LETDECL ($LIST $llc)) [1 0] "In" FNL $u ]

(* ========================================== *)
(*       PP rules for simple tactics          *)
(* ========================================== *)

  | reduce [<<(Reduce (REDEXP $rexp) $cl)>>] -> [ (REDEXP $rexp) $cl ]

  | split [<<(Split $b)>>] -> [ "Split" (WITHBINDING $b) ]
  | exists [<<(Exists $b)>>] -> ["Exists" $b] (* unused! *)

  | auton [<<(Auto ($NUM $n))>>] -> ["Auto " $n]
  | auto_with [<<(Auto ($LIST $lid))>>] -> 
	[ "Auto" [1 0] "with " [<hov 0> (LISTSPC ($LIST $lid))] ]
  | auton_with [<<(Auto ($NUM $n) ($LIST $lid))>>] ->
	[ "Auto" [1 0] $n [1 0] "with " [<hov 0> (LISTSPC ($LIST $lid))] ]
  | auto [<<(Auto)>>] -> ["Auto"]

  | dhyp [<<(DHyp $id)>>]  -> ["DHyp " $id]
  | cdhyp [<<(CDHyp $id)>>] -> ["CDHyp " $id]
  | dconcl [<<(DConcl)>>]   -> ["DConcl"] 
  | superauto [<<(SuperAuto   $a0 $a1 $a2 $a3)>>] ->
               ["SuperAuto " (AUTOARG $a0) [1 1] 
                             (AUTOARG $a1) [1 1]
                             (AUTOARG $a2) [1 1] 
                             (AUTOARG $a3)]

  | assumption [<<(Assumption)>>] -> ["Assumption"]

  | intro [<<(Intro)>>] -> ["Intro"]
  | intros [<<(Intros)>>] -> ["Intros"]
  | introsuntil_id [<<(IntrosUntil $id)>>] -> ["Intros until " $id]
  | introsuntil_n [<<(IntrosUntil ($NUM $n))>>] -> ["Intros until " $n]
  | intromove_an [<<(IntroMove $id)>>] -> ["Intro after " $id]
  | intromove_id [<<(IntroMove $id $id2)>>] -> ["Intro " $id " after " $id2]
  | intros_pattern [<<(INTROPATTERN $p)>>] -> [$p]

  | contradiction [<<(Contradiction)>>] -> ["Contradiction"]

  | apply [<<(Apply $c $b)>>] -> ["Apply " $c (WITHBINDING $b)]

  | oldelim [<<(Elim1 $C)>>] -> ["OldElim " $C]

  | elim [<<(Elim $c $b)>>] -> ["Elim " $c (WITHBINDING $b)]
  | elimusing [<<(Elim $c $b $cu $bu)>>]
      -> ["Elim " $c (WITHBINDING $b) [1 1]"using " $cu (WITHBINDING $bu)]

  | elimtype [<<(ElimType $c)>>] -> ["ElimType " $c]

  | case_tac [ << (Case $c $b) >> ] -> ["Case " $c (WITHBINDING $b) ]

  | casetype [<<(CaseType $c)>>] -> ["CaseType " $c] 
  | doubleind [<<(DoubleInd ($NUM $i) ($NUM $j))>>]
      -> [ "Double Induction " $i " " $j ]

  | specialize [<<(Specialize $c $b)>>] -> ["Specialize " $c (WITHBINDING $b)]
  | specializenum [<<(Specialize ($NUM $n) $c $b)>>]
      -> ["Specialize " $n " " $c (WITHBINDING $b) ]

  | generalize [<<(Generalize ($LIST $lc))>>]
      -> [ [<hov 3> "Generalize " (LISTSPC ($LIST $lc))] ]

  | lapply [<<(CutAndApply $c)>>] -> ["LApply " $c]

  | clear [<<(Clear (CLAUSE ($LIST $l)))>>] ->
          [ [<hov 3> "Clear " (LISTSPC ($LIST $l))] ]

  | move [<<(MoveDep $id1 $id2)>>] ->
          [ "Move " $id1 " after " $id2 ]

  | constructor [<<(Constructor)>>] -> ["Constructor" ]
  | constructor_num [<<(Constructor ($NUM $n) $b)>>]
      -> ["Constructor " $n (WITHBINDING $b) ]

  | trivial [<<(Trivial)>>] -> ["Trivial"]

  | failingtrivial [<<(FailingTrivial)>>] -> ["Trivial"]

  | inductionid [<<(Induction $id)>>] -> ["Induction " $id]
  | inductionnum [<<(Induction ($NUM $n))>>] -> ["Induction " $n]

  | destructid [<<(Destruct $id)>>] -> ["Destruct " $id]
  | destructnum [<<(Destruct ($NUM $n))>>] -> ["Destruct " $n]

  | decomposeand [<<(DecomposeAnd $c)>>] -> [ "Decompose Record " $c ]
  | decomposeor [<<(DecomposeOr $c)>>] -> [ "Decompose Sum " $c ]
  | decomposethese [<<(DecomposeThese (CLAUSE ($LIST $l)) $c )>>] -> 
              ["Decompose" [1 1] [<hov 0> "[" (LISTSPC ($LIST $l)) "]" ] 
	                         [1 1] $c]
  | mutualcofixtactic [<<(Cofix $id $cfe ($LIST $fd))>>] 
      -> ["Cofix "  $id  [1 1]"with " [<hov 0> $cfe (FIXLIST ($LIST $fd))] ]
  | pp_simple_cofix_tactic [<<(Cofix)>>] -> ["Cofix"]
  | pp_cofix_tactic [<<(Cofix $id)>>] -> ["Cofix " $id]
  | cofixexp [<<(COFIXEXP $id $c)>>] -> [ $id ":" $c ]

  | mutualfixtactic [<<(Fix $id $n $cfe ($LIST $fd))>>] 
      -> ["Fix " $id " " $n [1 1]"with " [<hov 0> $cfe (FIXLIST ($LIST $fd))] ]
  | pp_simple_fix_tactic [<<(Fix ($NUM $n))>>] -> ["Fix " $n]
  | pp_fix_tactic [<<(Fix $id ($NUM $n))>>] -> ["Fix " $id " " $n]
  | fixexp [<<(FIXEXP $id ($NUM $n) $c)>>] -> [ $id " " $n ":" $c ]

  | fixdeclcons [<<(FIXLIST $cfe ($LIST $fd))>>]
      -> [ [1 0] $cfe (FIXLIST ($LIST $fd))]
  | fixdeclnil  [<<(FIXLIST)>>] -> [ ]

  | exact [<<(Exact $C)>>] -> ["Exact " $C]

  | absurd [<<(Absurd $C)>>] -> ["Absurd " $C]

  | cut [<<(Cut $C)>>] -> ["Cut " $C]
  | lettac_cons [<<(LetTac $id $c (LETPATTERNS $p ($LIST $pl)))>>] -> 
	["LetTac" [1 1] $id ":=" $c [1 1] "in" [1 1] (LETPATTERNS $p ($LIST $pl))]
  | lettac_nil [<<(LetTac $id $c (LETPATTERNS))>>] -> 
	["LetTac" [1 1] $id ":=" $c]

  | left [<<(Left $b)>>] -> ["Left" (WITHBINDING $b)]
  | right [<<(Right $b)>>] -> [ "Right" (WITHBINDING $b)]

  | discriminate [<<(Discriminate)>>] -> ["Simple Discriminate"]

  | reflexivity [<<(Reflexivity)>>] -> ["Reflexivity"]
  | symmetry [<<(Symmetry)>>] -> ["Symmetry"]
  | transitivity [<<(Transitivity $C)>>] -> ["Transitivity " $C]

(* ============================================== *)
(*      PP rules for tactic arguments             *)
(* ============================================== *)

  | idargnil [<<(IDARGLIST)>>] -> [ ]
  | idargcons
      [<<(IDARGLIST $id ($LIST $L))>>] -> [ $id " "  (IDARGLIST ($LIST $L)) ]

  | nenumlistcons
      [<<(NENUMLIST ($NUM $n) ($LIST $l))>>] -> [ $n " " (NENUMLIST ($LIST $l)) ]
  | nenumlistone [<<(NENUMLIST ($NUM $n))>>] -> [ $n ]

  | numlistcons [<<(NUMLIST ($LIST $l))>>] -> [ (NENUMLIST ($LIST $l)) ]
  | numlistnil [<<(NUMLIST)>>] -> [ ]

  (* Bindings: print "with" before the bindings. *)
  | with_binding [<<(WITHBINDING (BINDINGS ($LIST $b)))>>]
       -> [ [1 1] "with " [<hov 0> (BINDBOX ($LIST $b)) ] ]
  | without_binding [<<(WITHBINDING (BINDINGS))>>] -> [ ]

  (* Bindings: nor break nor "with" before. *)
  | bindings [<<(BINDINGS ($LIST $l))>>] -> [ " " [<hov 0> (BINDBOX ($LIST $l)) ] ]
  | bindingsnone [<<(BINDINGS)>>] -> [ ]

  (* Prints a non-empty list of bindings, assuming the box and the first space
     is already printed. *)
  | bindinglistcons [<<(BINDBOX $b ($LIST $bl))>>]
      -> [ $b [1 0] (BINDBOX ($LIST $bl)) ]
  | bindinglistone [<<(BINDBOX $b)>>] -> [ $b ]

  (* One binding *)
  | bindingid [<<(BINDING ($VAR $id) $c)>>] -> [ [<hov 2> $id ":=" $c ] ]
  | bindingnum [<<(BINDING ($NUM $n) $c)>>] -> [ [<hov 2> $n ":=" $c ] ]
  | bindingcom [<<(BINDING $c)>>] -> [ $c ]

  | reduce_red [<<(REDEXP (Red))>>] -> ["Red"]
  | reduce_hnf [<<(REDEXP (Hnf))>>] -> ["Hnf"]
  | reduce_simpl [<<(REDEXP (Simpl))>>] -> ["Simpl"]
  | reduce_cbv [<<(REDEXP (Cbv ($LIST $lf)))>>] -> ["Cbv" (FLAGS ($LIST $lf))]
  | reduce_compute [<<(REDEXP (Cbv (Beta) (Delta) (Iota)))>>] -> [ "Compute" ]
  | reduce_lazy [<<(REDEXP (Lazy ($LIST $lf)))>>] ->
    ["Lazy" (FLAGS ($LIST $lf))]
  | reduce_unfold [<<(REDEXP (Unfold ($LIST $unf)))>>] ->
       [ [<hv 3> "Unfold " (UNFOLDLIST ($LIST $unf))] ]
  | reduce_fold [<<(REDEXP (Fold ($LIST $cl)))>>] ->
       [ [<hov 3> "Fold " (LISTSPC ($LIST $cl))] ]
  | reduce_change [<<(REDEXP (Change $c))>>] -> ["Change " $c]
  | reduce_pattern [<<(REDEXP (Pattern ($LIST $pl)))>>] ->
       [ [<hv 3> "Pattern " (NEPATTERNLIST ($LIST $pl)) ] ]

  | flags_beta [<<(FLAGS (Beta) ($LIST $F))>>] ->
        [ [1 0] "Beta" (FLAGS ($LIST $F))]
  | flags_delta [<<(FLAGS (Delta) ($LIST $F))>>] ->
        [ [1 0] "Delta" (FLAGS ($LIST $F))]
  | flags_iota [<<(FLAGS (Iota) ($LIST $F))>>] ->
        [ [1 0] "Iota" (FLAGS ($LIST $F))]
  | delta_unf [<<(FLAGS (Unf ($LIST $idl)) ($LIST $F))>>]
         -> [ [1 0] "[" [<hov 0> (LISTSPC ($LIST $idl)) ] "]"
              (FLAGS ($LIST $F))]
  | delta_unfbut [<<(FLAGS (UnfBut ($LIST $idl)) ($LIST $F))>>]
         -> [ [1 0] "-[" [<hov 0> (LISTSPC ($LIST $idl)) ] "]"
              (FLAGS ($LIST $F))]
  | flags_nil [<<(FLAGS)>>] -> [ ]


  | unfoldcons
        [<<(UNFOLDLIST $H ($LIST $T))>>] -> [ $H " " (UNFOLDLIST ($LIST $T)) ]
  | unfoldone [<<(UNFOLDLIST $H)>>] -> [ $H ]

  | unfoldarg [<<(UNFOLD $id ($LIST $OCCL))>>]
         -> [ (UNFOLDOCCLIST ($LIST $OCCL)) (COMMAND $id) ]

  | unfold_occ_nil  [<<(UNFOLDOCCLIST)>>] -> [ ]
  | unfold_occ_cons [<<(UNFOLDOCCLIST ($NUM $n) ($LIST $T))>>]
         -> [ $n " " (UNFOLDOCCLIST ($LIST $T)) ]


  | autoarg_depth     [<<(AUTOARG $n)>>] -> [ $n]
  | autoarg_adding1   [<<(AUTOARG (CLAUSE ($LIST $l)))>>] -> 
                      ["Adding" [1 1] "[" (LISTSPC ($LIST $l)) "]"]

  | autoarg_adding2     [<<(AUTOARG (CLAUSE))>>] -> [""]
  | autoarg_destructing [<<(AUTOARG "Destructing")>>] -> 
                        ["Destructing"]
  | autoarg_usingTDB    [<<(AUTOARG "UsingTDB")>>]    -> ["Using TDB"]
  | autoarg_noarg       [<<(AUTOARG "NoAutoArg")>>]   -> [""]
  
  | intropatlist [<<(LISTPATTERN ($LIST $tl))>>] ->
                 [ (LISTSPC ($LIST $tl)) ]
  | intropatdisj [<<(DISJPATTERN ($LIST $dp))>>] ->
                 [ "[" [<hv 0> (LISTBAR ($LIST $dp))] "]" ]
  | intropatconj [<<(CONJPATTERN ($LIST $cp))>>] ->
                 [ "(" [<hov 0> (LISTCOMA ($LIST $cp))] ")" ]
  | intropatid [<<(IDENTIFIER ($VAR $id))>>] -> [ $id ]


  | patterncons [<<(NEPATTERNLIST $H ($LIST $T))>>]
         -> [ [<hov 1> $H ] [1 0] (NEPATTERNLIST ($LIST $T)) ]
  | patternone [<<(NEPATTERNLIST $H)>>] -> [ [<hov 1> $H ] ]

  | patternargoccs [<<(PATTERN $c ($LIST $OCCL))>>]
         -> [ [<hov 1> (NENUMLIST ($LIST $OCCL)) ] [1 1] $c ]
  | patternargnil [<<(PATTERN $c)>>] -> [ $c ]


  | letpatterncons [<<(LETPATTERNS $H ($LIST $T))>>]
         -> [ [<hov 1> $H ] [1 0] (LETPATTERNS ($LIST $T)) ]
  | letpatternone [<<(LETPATTERNS $H)>>] -> [ [<hov 1> $H ] ]

  | hyppatternargoccs [<<(HYPPATTERN $s ($LIST $OCCL))>>]
         -> [ [<hov 1> (NENUMLIST ($LIST $OCCL)) ] [1 1] $s ]
  | hyppatternargnil [<<(HYPPATTERN $s)>>] -> [ $s ]

  | cclpatternargoccs [<<(CCLPATTERN ($LIST $OCCL))>>]
         -> [ [<hov 1> (NENUMLIST ($LIST $OCCL)) ] [1 1] "Goal" ]
  | cclpatternargnil [<<(CCLPATTERN)>>] -> [ "Goal" ]


  | clause [<<(CLAUSE ($LIST $l))>>]
         -> [ [1 1][<hov 2> "in " (LISTSPC ($LIST $l)) ] ]
  | clause_none [<<(CLAUSE)>>] -> [ ]


  (* Lists with separators *)
  | listspc_cons [<<(LISTSPC $x ($LIST $l))>>] ->
                 [ $x [1 0] (LISTSPC ($LIST $l)) ]
  | listspc_one  [<<(LISTSPC $x)>>] -> [ $x ]
  | listspc_nil  [<<(LISTSPC )>>] -> [ ]

  | listbar_cons [<<(LISTBAR $x ($LIST $l))>>] ->
                 [ $x [1 0]"| " (LISTBAR ($LIST $l)) ]
  | listbar_one  [<<(LISTBAR $x)>>] -> [ $x ]
  | listbar_nil  [<<(LISTBAR )>>] -> [ ]

  | listcoma_cons [<<(LISTCOMA $x ($LIST $l))>>] ->
                  [ $x ","[1 0] (LISTCOMA ($LIST $l)) ]
  | listcoma_one  [<<(LISTCOMA $x)>>] -> [ $x ]
  | listcoma_nil  [<<(LISTCOMA )>>] -> [ ]
  ;

  level 8:
    tactic_to_constr [<<(COMMAND $c)>>] -> [ $c:"constr":9 ]
  | tactic_to_castedconstr [<<(CASTEDCOMMAND $c)>>] -> [ $c:"constr":9 ]
  | tactic_to_openconstr [<<(CASTEDOPENCOMMAND $c)>>] -> [ $c:"constr":9 ]

  (* This is produced bu UNFOLDLIST *)
  | tactic_qualidarg_constr [<<(COMMAND (QUALIDARG $p))>>] -> [(QUALIDARG $p)]
  | tactic_qualidarg_nil [<<(QUALIDARG $id)>>] -> [ $id ]
  | tactic_qualidarg_cons [<<(QUALIDARG $id $p)>>] ->
	 [ $id [1 0] "." (QUALID $p) ].
