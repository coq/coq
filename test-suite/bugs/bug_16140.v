(* Test regression https://github.com/coq/coq/issues/16140
   where congruence produces ill-typed terms *)

Inductive wrap1 : Type :=
  wrap1I (u : unit) : match u with tt => bool end -> wrap1.

Goal (wrap1I tt false) = (wrap1I tt true) -> False.
Proof.
  Fail congruence. (* expected to fail *)
Abort.

Inductive wrap2 : unit -> Type :=
  wrap2I (u : unit) : match u with tt => bool end -> wrap2 u.

Goal (wrap2I tt false) = (wrap2I tt true) -> False.
Proof.
  Fail congruence. (* expected to fail *)
Abort.

Inductive wrap3 (u : unit) : Type :=
  wrap3I : match u with tt => bool end -> wrap3 u.

Goal (wrap3I tt false) = (wrap3I tt true) -> False.
Proof.
  congruence.
Qed.
