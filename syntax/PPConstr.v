(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

(* Syntax for the Calculus of Constructions. *)

Syntax constr
  level 0:
    ne_command_listcons [ << (NECOMMANDLIST $c1 ($LIST $cl)) >> ]
       -> [ $c1 [1 0] (NECOMMANDLIST ($LIST $cl)) ]
  | ne_command_listone [ << (NECOMMANDLIST $c1) >> ] -> [ $c1 ]
  ;

(* Things parsed in binder *)
(* ======================= *)

  level 0:
    idbindercons [ << (IDBINDER ($VAR $id) ($LIST $L)) >> ] ->
       [ $id ","[0 0] (IDBINDER ($LIST $L))]
  | idbinderone  [ << (IDBINDER ($VAR $id)) >> ] -> [$id]
  | idbindernil  [ << (IDBINDER) >> ] -> [ ]

  | binderscons [ << (BINDERS (BINDER $c ($LIST $id)) ($LIST $b)) >> ] ->
       [ [<hv 0> [<hov 0> (IDBINDER ($LIST $id))] ":"
                 [0 1] $c:E] ";"[1 0]
         (BINDERS ($LIST $b))  ]
  | bindersone  [ << (BINDERS (BINDER $c ($LIST $id))) >> ] -> 
       [ [<hov 0> (IDBINDER ($LIST $id))] ":" $c:E ]

  | letbindercons [ << (BINDERS (LETBINDER $c $id) ($LIST $b)) >> ] ->
       [ [<hov 0> id ":=" [0 1] $c:E ";" [1 0] (BINDERS ($LIST $b)) ] ]
  | letbinderone  [ << (BINDERS (LETBINDER $c $id)) >> ] -> 
       [ [<hov 0> id ":=" [0 1] $c:E ] ]
  ;


(* Things parsed in command0 *)
  level 0:
    prop [ Prop ] -> ["Prop"]
  | set  [ Set ]  -> ["Set"]
  | type [ Type ] -> ["Type"]
  | type_sp [ << (TYPE $id) >> ] -> ["Type" $id]
(* Note: Atomic constants (Nvar, CONST, MUTIND, MUTCONSTRUCT) are printed in
   Printer to know if they must be qualified or not (and previously to
   deal with the duality CCI/FW) *)

  | evar [ ? ] -> ["?"]
  | meta [ << (META $n) >> ] -> [ $n ]
  | implicit [ << (IMPLICIT) >> ] -> ["<Implicit>"]
  | indice [ << (REL ($NUM $n)) >> ] -> ["<Unbound ref: " $n ">"]
  | instantiation [ << (INSTANCE $a ($LIST $l)) >> ] ->
	 [ $a "{" (CONTEXT ($LIST $l)) "}"]
  | instantiation_nil [ << (CONTEXT) >> ] -> [ ]
  | instantiation_one [ << (CONTEXT $a) >> ] -> [ $a ]
  | instantiation_many [ << (CONTEXT $a $b ($LIST $l)) >> ] ->
	 [ (CONTEXT $b ($LIST $l)) ";" $a ]
  | qualid [ << (QUALID $id ($LIST $l)) >> ] -> [ $id (FIELDS ($LIST $l)) ]
  | fieldsnil [ << (FIELDS) >> ] -> [ ]
  | fieldscons [ << (FIELDS $id ($LIST $l)) >> ] ->
	 [ "." $id (FIELDS ($LIST $l)) ]
  ;

(* Things parsed in command1 *)
  level 1:
    soap [ << (SOAPP $lc1 ($LIST $cl)) >> ]
      -> [ [<hov 0> "(" $lc1 ")@[" (NECOMMANDLIST ($LIST $cl)) "]"] ]

  (* For debug *)
  | abstpatnamed [ << [$id1]$c >> ] -> [ [<hov 0> "<<" $id1 ">>" [0 1] $c:E ] ]
  | abstpatanon  [ << [ <> ]$c >> ] -> [ [<hov 0> "<<_>>" [0 1] $c:E ] ]
  ;

(* Things parsed in command2 *)

(* Things parsed in command3 *)

(* Things parsed in command4 *)

(* Things parsed in command5 *)

(* Things parsed in command6 *)

(* Things parsed in command7 *)

(* Things parsed in command8 *)
  level 8:
    lambda [ << (LAMBDA $Dom [$x]$Body) >> ]
     -> [(LAMBOX (BINDERS (BINDER $Dom $x)) $Body)]
  | lambda_anon [ << (LAMBDA $Dom [<>]$Body) >> ]
     -> [(LAMBOX (BINDERS (BINDER $Dom _)) $Body)]
  | lambdalist  [ << (LAMBDALIST $c [$x]$body) >> ]
     -> [(LAMLBOX (BINDERS) $c (IDS $x) $body)]
  | lambdalist_anon  [ << (LAMBDALIST $c [<>]$body) >> ]
     -> [(LAMLBOX (BINDERS) $c (IDS _) $body)]

  | formated_lambda [ << (LAMBOX $pbi $t) >> ]
     -> [ [<hov 0> "[" [<hv 0> $pbi] "]" [0 1] $t:E ] ]

  | lambda_cons [<<(LAMBOX (BINDERS ($LIST $acc)) (LAMBDA $Dom [$x]$body))>>]
      -> [(LAMBOX (BINDERS ($LIST $acc) (BINDER $Dom $x)) $body) ]
  | lambda_cons_anon
      [ << (LAMBOX (BINDERS ($LIST $acc)) (LAMBDA $Dom [<>]$body)) >> ]
      -> [(LAMBOX (BINDERS ($LIST $acc) (BINDER $Dom _)) $body)]
  | lambdal_start [ << (LAMBOX $pbi (LAMBDALIST $Dom $Body)) >> ]
      -> [(LAMLBOX $pbi $Dom (IDS) $Body)]

  | lambdal_end [<<(LAMLBOX (BINDERS ($LIST $acc)) $c (IDS ($LIST $ids)) $t)>>]
      -> [(LAMBOX (BINDERS ($LIST $acc) (BINDER $c ($LIST $ids))) $t)]
  | lambdal_cons_anon [ << (LAMLBOX $pbi $c (IDS ($LIST $ids)) [<>]$body) >> ]
      -> [(LAMLBOX $pbi $c (IDS ($LIST $ids) _) $body)]
  | lambdal_cons [ << (LAMLBOX $pbi $c (IDS ($LIST $ids)) [$id]$body) >> ]
      -> [(LAMLBOX $pbi $c (IDS ($LIST $ids) $id) $body)]

  | pi [ << (PROD $A [$x]$B) >> ] -> [ (PRODBOX (BINDERS) (PROD $A [$x]$B)) ]
  | prodlist  [ << (PRODLIST $c $b) >> ]
       -> [(PRODBOX (BINDERS) (PRODLIST $c $b))]

  | formated_prod [ << (PRODBOX $pbi $t) >> ]
     -> [ [<hov 0> "(" [<hov 0> $pbi] ")" [0 1] $t:E ] ]

  | prod_cons
      [ << (PRODBOX (BINDERS ($LIST $acc)) (PROD $Dom [$x]$body)) >> ]
      -> [(PRODBOX (BINDERS ($LIST $acc) (BINDER $Dom $x)) $body)]
  | prodl_start_cons [ << (PRODBOX $pbi (PRODLIST $Dom $Body)) >> ]
      -> [(PRODLBOX $pbi $Dom (IDS) $Body)]

  | prodl_end [<<(PRODLBOX (BINDERS ($LIST $acc)) $c (IDS ($LIST $ids)) $t)>>]
      -> [(PRODBOX (BINDERS ($LIST $acc) (BINDER $c ($LIST $ids))) $t)]
  | prodl_cons_anon [ << (PRODLBOX $pbi $c (IDS ($LIST $ids)) [<>]$body) >> ]
      -> [(PRODLBOX $pbi $c (IDS ($LIST $ids) _) $body)]
  | prodl_cons [ << (PRODLBOX $pbi $c (IDS ($LIST $ids)) [$id]$body) >> ]
      -> [(PRODLBOX $pbi $c (IDS ($LIST $ids) $id) $body)]


  | arrow [ << (ARROW $A [<>]$B) >> ] ->
       [ [<hv 0> $A:L " ->" [0 0] (ARROWBOX $B) ] ]
  | arrow_stop [ << (ARROWBOX $c) >> ] -> [ $c:E ]
  | arrow_again [ << (ARROWBOX (PROD $A [<>]$B)) >> ] ->
	 [ $A:L " ->" [0 0] (ARROWBOX $B) ]

(* These are synonymous *)
(* redundant
  | let [ [$x = $M]$N ] -> [ [<hov 0> "[" $x "=" $M:E "]" [0 1] $N:E ] ]
*)
  | letin [ << (LETIN $A [$x]$B) >> ] -> [ [ <hov 0> "[" $x ":=" [0 1] $A:E "]" [0 1] $B:E ] ]
  | letincast [ << (LETIN (CAST $A $C) [$x]$B) >> ] -> [ [ <hov 0> "[" $x ":=" [0 1] $A:E ":" $C:E "]" [0 1] $B:E ] ]
  ;

(* Things parsed in command9 *)
  level 9:
    cast [ << (CAST $C $T) >> ] -> [ [<hv 0> $C:L [0 0] "::" $T:E] ]
  ;

(* Things parsed in command10 *)
  level 10:
    app_cons [ << (APPLIST $H ($LIST $T)) >> ]
                 -> [ [<hov 0>  $H:E  (APPTAIL ($LIST $T)):E ] ]

  | app_imp  [ << (APPLISTEXPL $H ($LIST $T)) >> ]
                 -> [ [<hov 0>  "!" $H:E (APPTAIL ($LIST $T)):E ] ]

(*
  | app_imp  [ << (APPLISTEXPL $H ($LIST $T)) >> ]
                 -> [ (APPLISTIMPL (ACC $H) ($LIST $T)):E ]

  | app_imp_arg  [ << (APPLISTIMPL (ACC ($LIST $AC)) $a ($LIST $T)) >> ]
        -> [ (APPLISTIMPL (ACC ($LIST $AC) $a) ($LIST $T)):E ]

  | app_imp_imp_arg  [ << (APPLISTIMPL $AC (EXPL $_ $_) ($LIST $T)) >> ]
       -> [ (APPLISTIMPL $AC ($LIST $T)):E ]

  | app_imp_last [ << (APPLISTIMPL (ACC ($LIST $A)) $T) >> ]
         -> [ (APPLIST ($LIST $A) $T):E ]
*)

  | apptailcons [ << (APPTAIL $H ($LIST $T)) >> ]
	 -> [ [1 1] $H:L  (APPTAIL ($LIST $T)):E ]
  | apptailnil [ << (APPTAIL) >> ] -> [ ]

(* Implicits *)
  | apptailcons1  [ << (APPTAIL (EXPL $n $c1) ($LIST $T)) >> ]
         -> [ [1 1] $n "!" $c1:E  (APPTAIL ($LIST $T)):E ]
  ;
(*
  level 8:
    arg_implicit [ << (EXPL ($NUM $n) $c1) >> ] -> [ $n "!" $c1:L ]
(*  | arg_implicit1 [(EXPL "EX" ($NUM $n) $c1)] -> [ $n "!" $c1:L ]
  | fun_explicit [ << (EXPL $f) >> ] -> [ $f ]*)
  ;
*)

  level 8:
  recterm [ << (MATCH $P $c ($LIST $BL)) >> ] ->
     [ [<hov 0> [<hov 0> (ELIMPRED $P)
    		 [0 2] [<hov 0> "Match" [1 1] $c:E  [1 0] "with" ]]
	         [1 3] [<hov 0> (MATCHBRANCHES ($LIST $BL)):E ] "end"] ]

  | matchbranchescons [ << (MATCHBRANCHES $B ($LIST $T)) >> ]
       -> [ [<hov 0> [<hov 0> $B:E ] FNL] (MATCHBRANCHES ($LIST $T)):E ]
  | matchbranchesnil [ << (MATCHBRANCHES) >> ] -> [ ]

  | caseterm [ << (CASE $P $c ($LIST $BL)) >> ] ->
     [ [<hov 0> [<hov 0> (ELIMPRED $P)
                  [0 2][<hov 0> "Case" [1 1] $c:E  [1 0] "of" ]]
                  [1 3][<hov 0> (MATCHBRANCHES ($LIST $BL)):E ] "end"] ]

  | ifterm [ << (IF $P $c $b1 $b2) >> ] ->
     [ (FORCEIF $P $c (EQN $b1 JUNK) (EQN $b2 JUNK)):E ]

  | letterm [ << (LET $P $c (LAMBDALIST $_ $b)) >> ] ->
     [ (LETSLAM $P $c $b) ]
  | letslamend [ << (LETSLAM $P $c $b ($LIST $IDL))>> ] ->
     [ (FORCELET $P $c (EQN $b (PATTCONSTRUCT JUNK ($LIST $IDL)))):E ]
  | letslam [ << (LETSLAM $P $c [$ID]$b ($LIST $IDL))>> ] ->
     [ (LETSLAM $P $c $b ($LIST $IDL) $ID) ]
  | letslamanon [ << (LETSLAM $P $c [<>]$b ($LIST $IDL))>> ] ->
     [ (LETSLAM $P $c $b ($LIST $IDL) _) ]

  | elim_pred      [ << (ELIMPRED $pred) >> ]          -> [ "<" $pred:E ">" [0 2] ]
  | elim_pred_xtra [ << (ELIMPRED "SYNTH") >> ] -> [ ]
  ;

  level 0:
    fix [ << (FIX $f $def ($LIST $lfs)) >> ] ->
      [ [<hov 0> "Fix " $f
           [0 2] "{" [<v 0> [<hov 0> $def]
                            (FIXDECLS ($LIST $lfs)) ] "}"] ]

  | cofix [ << (COFIX $f $def ($LIST $lfs)) >> ] ->
      [ [<hov 0> "CoFix " $f
           [0 2] "{" [<v 0> [<hov 0> $def]
                            (FIXDECLS ($LIST $lfs)) ] "}"] ]

  | nofixdefs [ << (FIXDECLS) >> ] -> [ ]
  | fixdefs [ << (FIXDECLS $def1 ($LIST $defs)) >> ] ->
      [ FNL [<hov 0> "with " $def1] (FIXDECLS ($LIST $defs)) ]
  ;

  level 8:
    onefixnumdecl [ << (NUMFDECL $f ($NUM $x) $A $t) >> ] ->
      [ $f "/" $x " :"
        [1 2] $A:E " :="
        [1 2] $t:E ]
  | onefixdecl [ << (FDECL $f (BINDERS ($LIST $l)) $A $t) >> ] ->
      [ $f
        [1 2] "[" [<hv 0> (BINDERS ($LIST $l))] "]"
        [1 2] ": " $A:E " :="
        [1 2] $t:E ]
  | onecofixdecl [ << (CFDECL $f $A $t) >> ] ->
      [ $f " : "
        [1 2] $A:E " :="
        [1 2] $t:E ]
  ;

  level 8:
    evalconstr [ << (EVAL $c $r) >> ] ->
	 [ [<hv 0> "Eval" [1 1] $r [1 0] "in" [1 1] $c:E ] ].

