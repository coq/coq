(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

Syntax constr
  level 0:
    ne_command_listcons2 [ << (NECOMMANDLIST2 $c1 ($LIST $cl)) >> ]
      -> [ $c1:L [1 0] (NECOMMANDLIST2 ($LIST $cl)) ]
  | ne_command_listone2 [ << (NECOMMANDLIST2 $c1) >> ] -> [$c1:L]
  ;

  level 10:
    as_patt [ << (PATTAS $var $patt) >> ] -> [$patt:L" as "$var]
  ;

  level 0:
    ne_pattlist_nil  [ << (PATTLIST) >> ] -> [ ]
  | ne_pattlist_cons [ << (PATTLIST $patt ($LIST $lpatt)) >> ]
      -> [$patt:E " " (PATTLIST ($LIST $lpatt))]
  ;

  level 8:
    equation [ << (EQN $rhs ($LIST $lhs)) >> ]
      -> [ [<hov 0> (PATTLIST ($LIST $lhs)) "=> " [0 1] $rhs:E] ]
  ;
 
  level 0:
    bar_eqnlist_nil [ << (BAREQNLIST) >> ] -> [ ]
  | bar_eqnlist_cons [ << (BAREQNLIST $eqn ($LIST $leqn)) >> ]
      -> [ "| " $eqn [1 0] (BAREQNLIST ($LIST $leqn)) ]
  | bar_eqnlist_one [ << (BAREQNLIST $eqn) >> ]
      -> [ "| " $eqn ]

  | tomatch [ << (TOMATCH ($LIST $lc)) >> ] -> [(NECOMMANDLIST2 ($LIST $lc)):E]
  ;

  level 10: 
    pattconstruct [ << (PATTCONSTRUCT $C $D ($LIST $T)) >> ] ->
	 [(APPLIST $C $D ($LIST $T))]
  ;

  level 0:
    pattconstructatomic [ << (PATTCONSTRUCT $C) >> ] -> [ $C ]
  ;

  level 8:

    cases_exp_none [ << (CASES $pred $tomatch) >> ]
      -> [ [<hov 0> (ELIMPRED $pred)
              [<hv 0> "Cases"[1 2] $tomatch:E [1 0] "of"] [1 0] "end"] ]

  | cases_exp_one [ << (CASES $pred $tomatch $eqn) >> ]
      -> [ [<hov 0> (ELIMPRED $pred)
              [<hv 0> [<hv 0> "Cases"[1 2] $tomatch:E [1 0] "of"] [1 2]
                     $eqn [1 0]
                     "end"] ] ]

  | cases_exp_many [ << (CASES $pred $tomatch $eqn1 $eqn2 ($LIST $eqns)) >> ]
      -> [ [<hov 0> (ELIMPRED $pred)
              [<v 0> [<hv 0> "Cases"[1 2] $tomatch:E [1 0] "of"] [1 2]
                     $eqn1 [1 0]
                     (BAREQNLIST $eqn2 ($LIST $eqns)) [1 0]
                     "end"] ] ]

  (* "level" indiff�rent pour ce qui suit *)
  | let_binder_var [ << (LETBINDER ($VAR $id)) >> ] -> [ $id ]
  | let_binder_app 
	[<<(LETBINDER (PATTCONSTRUCT $toforget ($VAR $id) ($LIST $vars)))>>]
      -> [ "(" $id (LETBINDERTAIL ($LIST $vars)) ")" ]
 
  | let_binder_tail_nil  [ << (LETBINDERTAIL) >> ] -> [ ]
  | let_binder_tail_cons [ << (LETBINDERTAIL $var ($LIST $vars)) >> ]
      -> [ "," [1 0] $var (LETBINDERTAIL ($LIST $vars)) ]

  | elim_pred      [ << (ELIMPRED $pred) >> ]          -> [ "<" $pred:E ">" [0 2] ]
  | elim_pred_xtra [ << (ELIMPRED "SYNTH") >> ] -> [ ]
  ;

  (* On force les parenth�ses autour d'un "if" sous-terme (m�me si le
     parsing est lui plus tol�rant) *)
  level 10:
    boolean_cases [ << (FORCEIF $pred $tomatch (EQN $c1 $_) (EQN $c2 $_)) >> ]
      -> [ [<hov 0> (ELIMPRED $pred)
              [<hv 0> "if " [<hov 0> $tomatch:L ]
                      [1 0] [<hov 0> "then" [1 1] $c1:L ]
                      [1 0] [<hov 0> "else" [1 1] $c2:L ] ] ] ]

  | let_cases [ << (FORCELET $pred $tomatch (EQN $c $pat)) >> ]
      -> [ [<hov 0> (ELIMPRED $pred)
              [<hv 0> "let " [<hov 0> (LETBINDER $pat) ] " ="
                      [1 1] [<hov 0> $tomatch:L ] ]
              [1 0] "in " [<hov 0> $c:L ] ] ]
.
