(*************************************************************************

   PROJET RNRT Calife - 2001
   Author: Pierre Crégut - France Télécom R&D
   Licence : LGPL version 2.1

 *************************************************************************)

Require Omega.
Require ReflOmegaCore.

Grammar tactic simple_tactic : ast :=
  romega [ "ROmega" ] -> [(ReflOmega)].

Syntax tactic level 0:
  romega [ (ReflOmega) ] -> ["ROmega"].   
     
