
(* $Id: *)

Require Export Equality.

Declare ML Module "Inv" "Leminv".

Syntax tactic level 0:
  inversion    [(Inv $ic $id)] -> [ (INVCOM $ic) [1 1] $id]
| inversion_in [(InvIn $ic $id ($LIST $l))]
    -> [ (INVCOM $ic) [1 1] $id (CLAUSE ($LIST $l))]

| dep_inv [(DInv $ic $id)] -> ["Dependent " (INVCOM $ic) [1 1] $id]
| dep_inv_with [(DInvWith $ic $id $c)]
    -> ["Dependent " (INVCOM $ic) [1 1] $id [1 1] "with " $c]

(* Use rules *)

| inv_using
    [(UseInversionLemma $id $c)] -> ["Inversion " $id [1 1] "using " $c]
| inv_using_in [(UseInversionLemmaIn $id $c ($LIST $l))]
    -> ["Inversion " $id [1 1] "using " $c (CLAUSE ($LIST $l))]

| simple_inv       [(INVCOM HalfInversion)] -> [ "Simple Inversion" ]
| inversion_com    [(INVCOM Inversion)] -> [ "Inversion" ]
| inversion_clear  [(INVCOM InversionClear)] -> [ "Inversion_clear" ].


Grammar tactic simple_tactic: Ast :=
  inversion    [ inversion_com($ic) identarg($id) ] -> [(Inv $ic $id)]
| inversion_in [ inversion_com($ic) identarg($id) "in" ne_identarg_list($l) ]
      -> [(InvIn $ic $id ($LIST $l))]
| dep_inv   [ "Dependent" inversion_com($ic) identarg($id) ]
     -> [(DInv $ic $id)]
| dep_inv_with
   [ "Dependent" inversion_com($ic) identarg($id) "with" constrarg($c) ]
     -> [(DInvWith $ic $id $c) ]

| inv_using [ inversion_com($ic) identarg($id) "using" constrarg($c) ]
     -> case [$ic] of
          Inversion -> [(UseInversionLemma $id $c)]
        esac

| inv_using_in
   [ inversion_com($ic) identarg($id) "using" constrarg($c)
     "in" ne_identarg_list($l) ]
     -> case [$ic] of
          Inversion -> [(UseInversionLemmaIn $id $c ($LIST $l))]
        esac

with inversion_com: Ast :=
  simple_inv    [ "Simple" "Inversion" ] -> [ HalfInversion ]
| inversion_com [ "Inversion" ] -> [ Inversion ]
| inv_clear     [ "Inversion_clear" ] -> [ InversionClear ].


Grammar vernac vernac: Ast :=
  der_inv_clr [ "Derive" "Inversion_clear"  identarg($na) identarg($id) "." ]
               -> [(MakeInversionLemmaFromHyp 1 $na $id)]

| der_inv_clr_num [ "Derive" "Inversion_clear"
                     numarg($n) identarg($na) identarg($id) "." ]
                   -> [(MakeInversionLemmaFromHyp $n $na $id)]

| der_inv_clr_with_srt [ "Derive" "Inversion_clear"  identarg($na) 
                         "with" constrarg($com) "Sort" sortarg($s) "." ]
                        -> [(MakeInversionLemma $na $com $s)]

| der_inv_clr_with [ "Derive" "Inversion_clear"  identarg($na)
                     "with" constrarg($com) "." ]
                    -> [(MakeInversionLemma $na $com (COMMAND (PROP{Null})))]

| der_inv_with_srt [ "Derive" "Inversion" identarg($na)
                     "with" constrarg($com) "Sort" sortarg($s) "." ]
                    -> [(MakeSemiInversionLemma $na $com $s)]

| der_inv_with [ "Derive" "Inversion" identarg($na) "with" constrarg($com) "." ]
                -> [(MakeSemiInversionLemma $na $com (COMMAND (PROP{Null})))]

| der_inv [ "Derive" "Inversion" identarg($na) identarg($id) "." ]
           -> [(MakeSemiInversionLemmaFromHyp 1 $na $id)]

| der_inv_num [ "Derive" "Inversion"
                numarg($n) identarg($na) identarg($id) "." ]
               -> [(MakeSemiInversionLemmaFromHyp $n $na $id)]

| der_dep_inv_with_srt [ "Derive" "Dependent" "Inversion" identarg($na) 
                         "with" constrarg($com) "Sort" sortarg($s) "." ]
                  -> [(MakeDependentSemiInversionLemma $na $com $s)]

| der_dep_inv_clr_with_srt
     [ "Derive" "Dependent" "Inversion_clear"  identarg($na) 
       "with" constrarg($com)  "Sort" sortarg($s)"." ]
      -> [(MakeDependentInversionLemma $na $com $s)].
