(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Extraction to Ocaml : use of basic Ocaml types *)

Extract Inductive bool => bool [ true false ].
Extract Inductive option => option [ Some None ].
Extract Inductive unit => unit [ "()" ].
Extract Inductive list => list [ "[]" "( :: )" ].
Extract Inductive prod => "( * )" [ "" ].

(** NB: The "" above is a hack, but produce nicer code than "(,)" *)

(** Mapping sumbool to bool and sumor to option is not always nicer,
    but it helps when realizing stuff like [lt_eq_lt_dec] *)

Extract Inductive sumbool => bool [ true false ].
Extract Inductive sumor => option [ Some None ].

(** Restore lazyness of andb, orb.
    NB: without these Extract Constant, andb/orb would be inlined
    by extraction in order to have lazyness, producing inelegant
    (if ... then ... else false) and (if ... then true else ...).
*)

Extract Inlined Constant andb => "(&&)".
Extract Inlined Constant orb => "(||)".

