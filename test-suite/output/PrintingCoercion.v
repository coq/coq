
Parameter A B C D : Type.

Parameter f : A -> B.
Parameter g : B -> C.
Parameter h : C -> D.

Coercion f : A >-> B.
Coercion g : B >-> C.

Parameter a : A.

Check a : C.

Module M.
  Module N.
    Section S.
      Add Printing Coercion f. (* implicit local *)
      #[export] Add Printing Coercion g.

      Variable h' : C -> D.

      Coercion h' : C >-> D.

      Fail Global Add Printing Coercion h'.
      Fail #[export] Add Printing Coercion h'.

      Check a : D.

      Fail Add Printing Coercion h.
      Add Printing Coercion h'.

      Check a : D.

    End S.

    Check a : C.

    Global Add Printing Coercion f.

    Coercion h : C >-> D.
    Add Printing Coercion h. (* implicit export *)

    Check a : D.
  End N.
  Check a : C.

  Remove Printing Coercion f. (* implicit export *)
End M.
Check a : C.

Import M.
Check a : C.

Import(coercions) N.
Check a : D.

Import(options) N.
Check a : D.
