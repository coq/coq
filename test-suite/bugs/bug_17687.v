(* -*- coq-prog-args: ("-noinit"); -*- *)

Declare ML Module "rocq-runtime.plugins.ltac".
Global Set Default Proof Mode "Classic".

Inductive paths {A : Type} (a : A) : forall _:A, Type := idpath : paths a a.
Axiom transport : forall {A : Type} (x : A) (p : paths x x), paths x x.
Lemma t (x : Type) (eq : paths x x) : paths (transport x eq) (transport x eq).
Fail rewrite eq.
Succeed try rewrite eq.
Abort.
