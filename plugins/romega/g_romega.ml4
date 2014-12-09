(*************************************************************************

   PROJET RNRT Calife - 2001
   Author: Pierre Crégut - France Télécom R&D
   Licence : LGPL version 2.1

 *************************************************************************)

(*i camlp4deps: "grammar/grammar.cma" i*)

DECLARE PLUGIN "romega_plugin"

open Refl_omega

let romega_tactic l =
  let tacs = List.map
    (function
       | "nat" -> Tacinterp.interp <:tactic<zify_nat>>
       | "positive" -> Tacinterp.interp <:tactic<zify_positive>>
       | "N" -> Tacinterp.interp <:tactic<zify_N>>
       | "Z" -> Tacinterp.interp <:tactic<zify_op>>
       | s -> Errors.error ("No ROmega knowledge base for type "^s))
    (Util.List.sort_uniquize String.compare l)
  in
  Tacticals.New.tclTHEN
    (Tacticals.New.tclREPEAT (Proofview.tclPROGRESS (Tacticals.New.tclTHENLIST tacs)))
    (Tacticals.New.tclTHEN
       (* because of the contradiction process in (r)omega,
          we'd better leave as little as possible in the conclusion,
          for an easier decidability argument. *)
       (Tactics.intros)
       (Proofview.V82.tactic total_reflexive_omega_tactic))


TACTIC EXTEND romega
|  [ "romega" ] -> [ romega_tactic [] ]
END

TACTIC EXTEND romega'
| [ "romega" "with" ne_ident_list(l) ] ->
    [ romega_tactic (List.map Names.Id.to_string l) ]
| [ "romega" "with" "*" ] -> [ romega_tactic ["nat";"positive";"N";"Z"] ]
END
