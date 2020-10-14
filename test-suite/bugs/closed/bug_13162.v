
Module Type T. End T.
Module F (X:T). End F.
Fail Import F.
(* Error: Anomaly "Uncaught exception Not_found." *)

Fail Import T.
