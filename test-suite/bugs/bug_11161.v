(* Ensure that evars are properly normalized in the instance path.
   Problems with this can cause eg #11161. *)

Class Foo (n:nat) := {x : bool}.

Instance bar n : Foo n. Admitted.

Instance bar' n : Foo n. split. abstract exact true. Qed.

Instance bar'' n : Foo n. split. abstract exact true. Defined.
