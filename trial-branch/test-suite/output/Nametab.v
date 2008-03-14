Module Q.
  Module N.
    Module K.
      Definition id := Set.
    End K.
  End N.
End Q.

(* Bad *) Locate id.
(* Bad *) Locate K.id.
(* Bad *) Locate N.K.id.
(* OK  *) Locate Q.N.K.id.
(* OK  *) Locate Top.Q.N.K.id.

(* Bad *) Locate Module K.
(* Bad *) Locate Module N.K.
(* OK  *) Locate Module Q.N.K.
(* OK  *) Locate Module Top.Q.N.K.

(* Bad *) Locate Module N.
(* OK  *) Locate Module Q.N.
(* OK  *) Locate Module Top.Q.N.

(* OK  *) Locate Module Q.
(* OK  *) Locate Module Top.Q.


Import Q.N.


(* Bad *) Locate id.
(* OK  *) Locate K.id.
(* Bad *) Locate N.K.id.
(* OK  *) Locate Q.N.K.id.
(* OK  *) Locate Top.Q.N.K.id.

(* OK  *) Locate Module K.
(* Bad *) Locate Module N.K.
(* OK  *) Locate Module Q.N.K.
(* OK  *) Locate Module Top.Q.N.K.

(* Bad *) Locate Module N.
(* OK  *) Locate Module Q.N.
(* OK  *) Locate Module Top.Q.N.

(* OK  *) Locate Module Q.
(* OK  *) Locate Module Top.Q.
