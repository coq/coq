(* Declare Module in Module Type *)
Module Type A.
Record t : Set := { something : unit }.
End A.


Module Type B.
Declare Module BA : A.
End B.


Module Type C.
Declare Module CA  : A.
Declare Module CB : B with Module BA := CA.
End C.


Module Type D.
Declare Module DA : A.
(* Next line gives: "Anomaly: uncaught exception Not_found. Please report." *)
Declare Module DC : C with Module CA := DA.
End D.
