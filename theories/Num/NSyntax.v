(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*s Syntax for arithmetic *)

Require Export Params.
Require Export NeqDef.

Infix 6 "<" lt.
Infix 6 "<=" le.
Infix 6 ">" gt.
Infix 6 ">=" ge.
Infix 6 "<>" neq.

(*i Infix 6 "=" eq. i*)

Grammar constr constr1 :=
eq_impl [ constr0($c) "=" constr0($c2) ] -> [ (eq $c $c2) ].

(*i Infix 7 "+" plus. i*)

Grammar constr lassoc_constr4 :=
  squash_sum
  [ lassoc_constr4($c1) "+" lassoc_constr4($c2) ] ->
      case [$c2] of
        (SQUASH $T2) ->
            case [$c1] of
              (SQUASH $T1) -> [ (sumbool $T1 $T2) ] (* {T1}+{T2} *)
            | $_           -> [ (sumor $c1 $T2) ]   (* c1+{T2} *)
            esac
      | $_           -> [ (add $c1 $c2) ]           (* c1+c2 *)
      esac.

Syntax constr
  level 1:
    equal [ (eq $t1  $t2) ] -> [ [<hov 0> $t1:E [0 1]  "=" $t2:E ] ]
 ;

  level 4:
    sum [ (add $t1 $t2) ] -> [ [<hov 0> $t1:E [0 1] "+" $t2:L ] ]
.