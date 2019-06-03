From Tuto0 Require Import Loader.

(*** Printing messages ***)

HelloWorld.

Lemma test : True.
Proof.
hello_world.
Abort.

(*** Printing warnings ***)

HelloWarning.

Lemma test : True.
Proof.
hello_warning.
Abort.

(*** Signaling errors ***)

Fail HelloError.

Lemma test : True.
Proof.
Fail hello_error.
Abort.
