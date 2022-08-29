Goal True -> True.
Proof.
intros H.
apply (fun (f : True -> True) (n : True) => f n) in H.
(* Anomaly "in retyping: unknown meta 150." *)
+ exact I.
+ exact (fun x : True => x).
Qed.
