(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Genarg
open Ppextend
open Pptactic
open Extrawit

let pr_tac_polymorphic n _ _ prtac = prtac (n,E)

let _ = for i=0 to 5 do
  let wit = wit_tactic i in
  declare_extra_genarg_pprule wit
    (pr_tac_polymorphic i) (pr_tac_polymorphic i) (pr_tac_polymorphic i)
done
