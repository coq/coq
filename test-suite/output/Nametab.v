Module Q.
  Module N.
    Module K.
      Definition id:=Set.
    End K.
  End N.
End Q.

(* Bad *) Locate id.
(* Bad *) Locate K.id.
(* Bad *) Locate N.K.id.
(* OK  *) Locate Q.N.K.id.
(* OK  *) Locate Top.Q.N.K.id.

(* Bad *) Locate K.
(* Bad *) Locate N.K.
(* OK  *) Locate Q.N.K.
(* OK  *) Locate Top.Q.N.K.

(* Bad *) Locate N.
(* OK  *) Locate Q.N.
(* OK  *) Locate Top.Q.N.

(* OK  *) Locate Q.
(* OK  *) Locate Top.Q.



Import Q.N.


(* Bad *) Locate id.
(* OK  *) Locate K.id.
(* Bad *) Locate N.K.id.
(* OK  *) Locate Q.N.K.id.
(* OK  *) Locate Top.Q.N.K.id.

(* OK  *) Locate K.
(* Bad *) Locate N.K.
(* OK  *) Locate Q.N.K.
(* OK  *) Locate Top.Q.N.K.

(* Bad *) Locate N.
(* OK  *) Locate Q.N.
(* OK  *) Locate Top.Q.N.

(* OK  *) Locate Q.
(* OK  *) Locate Top.Q.
