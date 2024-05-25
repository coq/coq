Module M.
(* The encapsulation in a module tests that the grammar rules
   and keywords are correctly registered *)
Require Derive.
End M.

(* Tests when x is refined by typechecking *)
Derive x SuchThat (eq_refl x = eq_refl 0) As x_ok.
reflexivity.
Qed.

Derive s SuchThat (forall z, eq_refl (s z) = eq_refl (S z)) As s_ok.
reflexivity.
Qed.
