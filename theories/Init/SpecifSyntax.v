(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

Require LogicSyntax.
Require Specif.

(* Parsing of things in Specif.v *)

Grammar constr constr1 :=
  sig [ "{" lconstr($lc) ":" lconstr($c1) "|" lconstr($c2) "}" ]
       -> [ (sig $c1 [$lc : $c1]$c2) ]

| sig2 [ "{" lconstr($lc) ":" lconstr($c1)
           "|" lconstr($c2) "&" lconstr($c3) "}" ]
       -> [ (sig2 $c1 [$lc : $c1]$c2 [$lc : $c1]$c3) ]

| sigS [ "{" lconstr($lc) ":" lconstr($c1) "&" lconstr($c2) "}" ]
       -> [ (sigS $c1 [$lc : $c1]$c2) ]

| sigS2 [ "{" lconstr($lc) ":" lconstr($c1)
             "&" lconstr($c2) "&" lconstr($c3) "}" ]
       -> [ (sigS2 $c1 [$lc : $c1]$c2 [$lc : $c1]$c3) ].

Grammar constr constr1: ast :=
  squash [ "{" lconstr($lc) "}" ] -> [(SQUASH $lc)].

Grammar constr lassoc_constr4 :=
  squash_sum
  [ lassoc_constr4($c1) "+" lassoc_constr4($c2) ] ->
      case [$c2] of
        (SQUASH $T2) ->
            case [$c1] of
              (SQUASH $T1) -> [ (sumbool $T1 $T2) ] (* {T1}+{T2} *)
            | $_           -> [ (sumor $c1 $T2) ]   (* c1+{T2} *)
            esac
      | $_           -> [ (sum $c1 $c2) ]           (* c1+c2 *)
      esac.

(* Pretty-printing of things in Specif.v *)

Syntax constr
  (* Default pretty-printing rules *)
  level 10:
    sig_var
      [<<(ABSTR_B_NB $c1 $c2)>>] -> [ [<hov 0> "sig " $c1:L [1 1] $c2:L ] ]
  | sig2_var
      [<<(Sig2_ABSTR_B_NB $c1 $c2 $c3)>>]
       -> [ [<hov 0> "sig2 " $c1:L [1 1] $c2:L [1 1] $c3:L] ]
  | sigS_var
      [<<(SigS_ABSTR_B_NB $c1 $c2)>>] -> [ [<hov 0> "sigS " $c1:L [1 1] $c2:L ] ]
  | sigS2_var [<<(SigS2_ABSTR_B_NB $c1 $c2 $c3)>>]
       -> [ [<hov 0> "sigS2 " $c1:L [1 1] $c2:L [1 1] $c3:L] ]
  ;

  level 1:
(* Pretty-printing of [sig] *)
    sig  [ (sig $c1 $c2) ] -> [ (ABSTR_B_NB  $c1 $c2):E ]
  | sig_nb [ << (ABSTR_B_NB $c1 (LAMBDALIST $c1 [<>]$c2)) >> ]
      -> [ [<hov 0> "{_:" $c1:E " |" [1 3] $c2:E "}" ] ]
  | sigma_b [ << (ABSTR_B_NB $c1 (LAMBDALIST $c1 [$id]$c2)) >> ]
      -> [ [<hov 0> "{" $id ":" $c1:E " |" [1 3] $c2:E "}" ] ]

(* Pretty-printing of [sig2] *)
  | sig2 [ (sig2 $c1 $c2 $c3) ] -> [ (Sig2_ABSTR_B_NB  $c1 $c2 $c3):E ]
  | sig2_b_b
      [ << (Sig2_ABSTR_B_NB $c1 (LAMBDALIST $c1 [$id]$c2)
                            (LAMBDALIST $c1 [$id]$c3)) >> ]
       -> [ [<hov 0> "{"$id":"$c1:E"|" [1 3]$c2:E [1 3]"& "$c3:E "}" ] ]
  | sig2_nb_b
      [ << (Sig2_ABSTR_B_NB $c1 (LAMBDALIST $c1 [<>]$c2)
                            (LAMBDALIST  $c1 [$id]$c3)) >> ]
       -> [ [<hov 0> "{"$id":"$c1:E"|" [1 3]$c2:E [1 3]"& "$c3:E "}" ] ]
  | sig2_b_nb
      [ << (Sig2_ABSTR_B_NB $c1 (LAMBDALIST $c1 [$id]$c2)
                            (LAMBDALIST $c1 [<>]$c3)) >> ]
       -> [ [<hov 0> "{"$id":"$c1:E"|" [1 3]$c2:E [1 3]"& "$c3:E "}" ] ]
  | sig2_nb_nb
      [ << (Sig2_ABSTR_B_NB $c1 (LAMBDALIST $c1 [<>]$c2)
                            (LAMBDALIST $c1 [<>]$c3)) >> ]
       -> [ [<hov 0> "{_:"$c1:E "|" [1 3] $c2:E [1 3]"& " $c3:E "}" ] ]

(* Pretty-printing of [sigS] *)
  | sigS [ (sigS $c1 $c2) ] -> [(SigS_ABSTR_B_NB  $c1 $c2):E]
  | sigS_nb [ << (SigS_ABSTR_B_NB $c1 (LAMBDALIST $c1 [<>]$c2)) >> ]
       -> [ [<hov 0> "{_:" $c1:E [1 3]"& " $c2:E  "}" ] ]
  | sigS_b [ << (SigS_ABSTR_B_NB $c1 (LAMBDALIST $c1 [$id]$c2)) >> ]
       -> [ [<hov 0> "{" $id  ":" $c1:E [1 3] "& " $c2:E "}" ] ]

(* Pretty-printing of [sigS2] *)
  | sigS2 [ (sigS2 $c1 $c2 $c3) ] -> [(SigS2_ABSTR_B_NB  $c1 $c2 $c3):E]
  | sigS2_b_b
      [ << (SigS2_ABSTR_B_NB $c1 (LAMBDALIST $c1 [$id]$c2)
                             (LAMBDALIST $c1 [$id]$c3)) >> ]
       -> [ [<hov 0> "{"$id ":" $c1:E [1 3]"& "$c2:E [1 3]"& "$c3:E "}" ] ]
  | sigS2_nb_b
      [ << (SigS2_ABSTR_B_NB $c1 (LAMBDALIST $c1 [<>]$c2)
                             (LAMBDALIST  $c1 [$id]$c3)) >> ]
       -> [ [<hov 0> "{"$id ":" $c1:E [1 3]"& "$c2:E [1 3]"& "$c3:E "}" ] ]
  | sigS2_b_nb
      [ << (SigS2_ABSTR_B_NB $c1 (LAMBDALIST $c1 [$id]$c2)
                              (LAMBDALIST $c1 [<>]$c3)) >> ]
       -> [ [<hov 0> "{"$id ":" $c1:E [1 3]"& "$c2:E [1 3]"& "$c3:E "}" ] ]
  | sigS2_nb_nb
      [ << (SigS2_ABSTR_B_NB $c1 (LAMBDALIST $c1 [<>]$c2)
                             (LAMBDALIST $c1 [<>]$c3)) >> ]
       -> [ [<hov 0> "{_:"$c1:E [1 3]"& "$c2:E [1 3]"& "$c3:E "}" ] ]

(* Pretty-printing of [projS1] and [projS2] *)
  | projS1_imp [ (projS1 ? ? $a) ] -> ["(ProjS1 " $a:E ")"]  
  | projS2_imp [ (projS2 ? ? $a) ] -> ["(ProjS2 " $a:E ")"]
  ;

(* Pretty-printing of [sumbool] and [sumor] *)
  level 4:
    sumbool [ (sumbool $t1 $t2) ]
       -> [ [<hov 0> "{" $t1:E "}" [0 1] "+" "{" $t2:L "}"] ]
  | sumor [ (sumor $t1 $t2) ]
       -> [ [<hov 0> $t1:E [0 1]  "+" "{" $t2:L "}"] ]
  ;

(* Pretty-printing of [except] *)
  level 1:
    Except_imp [ (except $1 $t2) ] -> [ [<hov 0> "Except " $t2 ] ]

(* Pretty-printing of [error] and [value] *)
  | Error_imp [ (error $t1) ]     -> [ [<hov 0> "Error" ] ]
  | Value_imp [ (value $t1 $t2) ] -> [ [<hov 0> "(Value " $t2 ")" ] ].

