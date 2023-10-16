Require Import Ltac2.Init.

Ltac2 @ external type : constr -> constr := "coq-core.plugins.ltac2" "constr_type".

Print Ltac2 Signatures.

Print type.

Locate type.

About type.

(* constructors *)

Print Ltac2 None.
Print Ltac2 Some.

Print Err.

Ltac2 Type ('a,'b) either := [ Inl ('a) | Inr ('b) ].

Print Ltac2 Inl.
Print Ltac2 Inr.

Ltac2 Type ('a,'b,'c) triple := [ Triple ('c, 'b, 'a) ].

Print Ltac2 Triple.

Print Ltac2 Not_found.
Print Ltac2 Out_of_bounds.

(* alias *)

Ltac2 Notation nota := () ().

Print nota.
