(*************************************************************************

   PROJET RNRT Calife - 2001
   Author: Pierre Crégut - France Télécom R&D
   Licence : LGPL version 2.1

 *************************************************************************)

(*i camlp4deps: "parsing/grammar.cma" i*)

open Refl_omega

(* arnaud: trucs factices *)
let tclTHEN = Tacticals.tclTHEN
let tclREPEAT = Tacticals.tclREPEAT
let tclPROGRESS = Tacticals.tclPROGRESS
let tclTHENLIST = Tacticals.tclTHENLIST
module Refiner =
  struct
    let abstract_extended_tactic = Tacticals.abstract_extended_tactic
  end 
(* arnaud: /trucs factices *)

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
|  [ "romega" ] -> [ Util.anomaly "G_romega.romega: à restaurer" (* arnaud: romega_tactic [] *)]
END

TACTIC EXTEND romega'
| [ "romega" "with" ne_ident_list(l) ] -> 
    [ Util.anomaly "G_romega.romega': à restaurer" (* arnaud: romega_tactic (List.map Names.string_of_id l) *)]
| [ "romega" "with" "*" ] -> [ Util.anomaly "G_romega.romega': à restaurer" (* arnaud: romega_tactic ["nat";"positive";"N";"Z"] *)]
END
