(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Syntax for arithmetic *)

Require Export Params.

Infix 6 "<" lt V8only 70.
Infix 6 "<=" le V8only 70.
Infix 6 ">" gt V8only 70.
Infix 6 ">=" ge V8only 70.

(*i Infix 7 "+" plus V8only 50. i*)

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
  level 4:
    sum [ (add $t1 $t2) ] -> [ [<hov 0> $t1:E [0 1] "+" $t2:L ] ]
.
