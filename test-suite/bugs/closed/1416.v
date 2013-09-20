(* In 8.1 autorewrite used to raised an anomaly here *)
(* After resolution of the bug, autorewrite succeeded *)
(* From forthcoming 8.4, autorewrite is forbidden to instantiate *)
(* evars, so the new test just checks it is not an anomaly *)

Set Implicit Arguments.

Record Place (Env A: Type) : Type := {
  read: Env -> A ;
  write: Env -> A -> Env ;
  write_read: forall (e:Env), (write e (read e))=e
}.

Hint Rewrite -> write_read: placeeq.

Record sumPl (Env A B: Type) (vL:(Place Env A)) (vR:(Place Env B)) : Type :=
 {
   mkEnv: A -> B -> Env ;
   mkEnv2writeL: forall (e:Env) (x:A), (mkEnv x (read vR e))=(write vL e x)
 }.

(* when the following line is commented, the bug does not appear *)
Hint Rewrite -> mkEnv2writeL: placeeq.

Lemma autorewrite_raise_anomaly: forall (Env A:Type) (e: Env) (p:Place Env A),
  (exists e1:Env, e=(write p e1 (read p e))).
Proof.
  intros Env A e p; eapply ex_intro.
  autorewrite with placeeq. (* Here is the bug *)

