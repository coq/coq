(****************************************************************************)
(*                 The Calculus of Inductive Constructions                  *)
(*                                                                          *)
(*                                Projet Coq                                *)
(*                                                                          *)
(*                     INRIA        LRI-CNRS        ENS-CNRS                *)
(*              Rocquencourt         Orsay          Lyon                    *)
(*                                                                          *)
(*                                 Coq V6.3                                 *)
(*                               July 1st 1999                              *)
(*                                                                          *)
(****************************************************************************)
(*                                 Prolog.v                                 *)
(****************************************************************************)

Grammar tactic simple_tactic: Ast :=
  eapply [ "EApply" constrarg_binding_list($cl) ]
      -> [(EApplyWithBindings ($LIST $cl))]
| eexact [ "EExact" constrarg($c) ] -> [(EExact $c)]
| prolog [ "Prolog" "[" constrarg_list($l) "]" numarg($n) ]
      -> [(Prolog $n ($LIST $l))]
| instantiate [ "Instantiate" numarg($n) constrarg($c) ] 
      -> [(Instantiate $n $c)]
| normevars [ "NormEvars" ] -> [(NormEvars)]
| etrivial [ "ETrivial" ] -> [(ETrivial)]
| eauto [ "EAuto" ] -> [(EAuto)]
| eauto_n [ "EAuto" numarg($n) ] -> [(EAuto $n)]
| eauto_with [ "EAuto" "with" ne_identarg_list($lid) ] 
	-> [(EAuto ($LIST $lid))]
| eauto_n_with [ "EAuto" numarg($n) "with" ne_identarg_list($lid) ]
	-> [(EAuto $n ($LIST $lid))]
| eauto_with_star [ "EAuto" "with" "*" ] 
	-> [(EAuto "*")]
| eauto_n_with_star [ "EAuto" numarg($n) "with" "*" ]
	-> [(EAuto $n "*")].

Syntax tactic level 0:
  eauto_with [<<(EAuto ($LIST $lid))>>] -> 
	[ "EAuto" [1 0] "with " [<hov 0> (LISTSPC ($LIST $lid))] ]
| eauto [<<(EAuto)>>] -> ["EAuto"]
| eauto_n_with [<<(EAuto ($NUM $n) ($LIST $lid))>>] ->
	[ "EAuto " $n [1 0] "with " [<hov 0> (LISTSPC ($LIST $lid))] ]
| eauto_n [<<(EAuto ($NUM $n))>>] -> ["EAuto " $n]
| eauto_with_star [<<(EAuto "*")>>] -> 
	[ "EAuto with *" ]
| eauto_n_with_star [<<(EAuto ($NUM $n) "*")>>] ->
	[ "EAuto " $n " with *" ]
| etrivial [<<(ETrivial)>>] -> ["ETrivial"]

| eexact [<<(EExact $c)>>] -> ["EExact " $c]

| eapply [<<(EApplyWithBindings $c ($LIST $bl))>>]
      -> ["EApply " $c (WITHBINDING ($LIST $bl))]

| prolog [<<(Prolog ($NUM $n) ($LIST $l))>>]
    -> [ [<hov 0> "Prolog" [1 2] "[" [<hov 0> (LISTSPC ($LIST $l)) ] "]"
                  [1 2] $n] ]

| instantiate [<<(Instantiate ($NUM $n) $c)>>] -> ["Instantiate " $n [1 2] $c]

| normevars [<<(NormEvars)>>] -> ["NormEvars"].


(* $Id$ *)

