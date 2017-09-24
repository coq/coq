(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Entries
open Globnames

let declare_variable id obj =
  let kn = Declare.declare_variable id obj in
  Impargs.declare_var_implicits id;
  Notation.declare_ref_arguments_scope (VarRef id);
  kn

let declare_constant ?internal ?local id ?export_seff (cd, kind) =
  let c = Declare.declare_constant ?internal ?local id ?export_seff (cd, kind) in
  Impargs.declare_constant_implicits c;
  Notation.declare_ref_arguments_scope (ConstRef c);
  c


let declare_inductive_argument_scopes kn mie =
  List.iteri (fun i {mind_entry_consnames=lc} ->
    Notation.declare_ref_arguments_scope (IndRef (kn,i));
    for j=1 to List.length lc do
      Notation.declare_ref_arguments_scope (ConstructRef ((kn,i),j));
    done) mie.mind_entry_inds

let declare_mind mie =
  let (sp,kn), isprim = Declare.declare_mind mie in
  let mind = Global.mind_of_delta_kn kn in
  Impargs.declare_mib_implicits mind;
  declare_inductive_argument_scopes mind mie;
  (sp,kn), isprim
