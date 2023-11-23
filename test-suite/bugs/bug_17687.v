(* -*- coq-prog-args: ("-noinit"); -*- *)

Declare ML Module "ltacX_common_plugin".
Declare ML Module "ltac_plugin".
Global Set Default Proof Mode "Classic".

Inductive paths {A : Type} (a : A) : forall _:A, Type := idpath : paths a a.
Axiom transport : forall {A : Type} (x : A) (p : paths x x), paths x x.
Lemma t (x : Type) (eq : paths x x) : paths (transport x eq) (transport x eq).
Fail rewrite eq.
Succeed try rewrite eq.
Abort.
