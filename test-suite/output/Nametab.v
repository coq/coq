(* coq-prog-args: ("-top" "Nametab") *)
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
(* OK  *) Locate Nametab.Q.N.K.foo.

(* Bad *) Locate Module K.
(* Bad *) Locate Module N.K.
(* OK  *) Locate Module Q.N.K.
(* OK  *) Locate Module Nametab.Q.N.K.

(* Bad *) Locate Module N.
(* OK  *) Locate Module Q.N.
(* OK  *) Locate Module Nametab.Q.N.

(* OK  *) Locate Module Q.
(* OK  *) Locate Module Nametab.Q.


Import Q.N.


(* Bad *) Locate foo.
(* OK  *) Locate K.foo.
(* Bad *) Locate N.K.foo.
(* OK  *) Locate Q.N.K.foo.
(* OK  *) Locate Nametab.Q.N.K.foo.

(* OK  *) Locate Module K.
(* Bad *) Locate Module N.K.
(* OK  *) Locate Module Q.N.K.
(* OK  *) Locate Module Nametab.Q.N.K.

(* Bad *) Locate Module N.
(* OK  *) Locate Module Q.N.
(* OK  *) Locate Module Nametab.Q.N.

(* OK  *) Locate Module Q.
(* OK  *) Locate Module Nametab.Q.

(* A slightly different request *)
Section T.
Locate T.
About T.
End T.
