Module Q.
  Module N.
    Module K.
      Definition foo := Set.
    End K.
  End N.
End Q.

(* Bad *) Locate foo.
(* Bad *) Locate K.foo.
(* Bad *) Locate N.K.foo.
(* OK  *) Locate Q.N.K.foo.
(* OK  *) Locate Top.Q.N.K.foo.

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


(* Bad *) Locate foo.
(* OK  *) Locate K.foo.
(* Bad *) Locate N.K.foo.
(* OK  *) Locate Q.N.K.foo.
(* OK  *) Locate Top.Q.N.K.foo.

(* OK  *) Locate Module K.
(* Bad *) Locate Module N.K.
(* OK  *) Locate Module Q.N.K.
(* OK  *) Locate Module Top.Q.N.K.

(* Bad *) Locate Module N.
(* OK  *) Locate Module Q.N.
(* OK  *) Locate Module Top.Q.N.

(* OK  *) Locate Module Q.
(* OK  *) Locate Module Top.Q.
