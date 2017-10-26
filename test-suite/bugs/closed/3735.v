Require Import Coq.Program.Tactics.
Class Foo := { bar : Type }.
Fail Lemma foo : Foo -> bar. (* 'Command has indeed failed.' in both 8.4 and trunk *)
Fail Program Lemma foo : Foo -> bar. 
