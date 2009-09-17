(*************************************************************************

   PROJET RNRT Calife - 2001
   Author: Pierre Crégut - France Télécom R&D
   Licence : LGPL version 2.1

 *************************************************************************)

(*i camlp4deps: "parsing/grammar.cma" i*)

open Refl_omega
open Refiner

let romega_tactic l =
  let tacs = List.map
    (function
       | "nat" -> Tacinterp.interp <:tactic<zify_nat>>
       | "positive" -> Tacinterp.interp <:tactic<zify_positive>>
       | "N" -> Tacinterp.interp <:tactic<zify_N>>
       | "Z" -> Tacinterp.interp <:tactic<zify_op>>
       | s -> Util.error ("No ROmega knowledge base for type "^s))
    (Util.list_uniquize (List.sort compare l))
  in
  tclTHEN
    (tclREPEAT (tclPROGRESS (tclTHENLIST tacs)))
    (tclTHEN
       (* because of the contradiction process in (r)omega,
          we'd better leave as little as possible in the conclusion,
          for an easier decidability argument. *)
       Tactics.intros
       total_reflexive_omega_tactic)


TACTIC EXTEND romega
|  [ "romega" ] -> [ romega_tactic [] ]
END

TACTIC EXTEND romega'
| [ "romega" "with" ne_ident_list(l) ] ->
    [ romega_tactic (List.map Names.string_of_id l) ]
| [ "romega" "with" "*" ] -> [ romega_tactic ["nat";"positive";"N";"Z"] ]
END
