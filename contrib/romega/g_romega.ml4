(*************************************************************************

   PROJET RNRT Calife - 2001
   Author: Pierre Cr�gut - France T�l�com R&D
   Licence : LGPL version 2.1

 *************************************************************************)

(*i camlp4deps: "parsing/grammar.cma" i*)

(* $Id$ *)

open Refl_omega

TACTIC EXTEND ROmega
  [ "ROmega" ] -> [ omega_solver ]
END
