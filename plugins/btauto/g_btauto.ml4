(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Ltac_plugin

DECLARE PLUGIN "btauto_plugin"

TACTIC EXTEND btauto
| [ "btauto" ] -> [ Refl_btauto.Btauto.tac ]
END

