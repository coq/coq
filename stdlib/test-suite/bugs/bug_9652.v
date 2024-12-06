Set Universe Polymorphism.
From Stdlib Require Import BinInt.
Class word_interface (width : Z) : Type := Build_word
  { rep : Type;
    unsigned : rep -> Z;
    of_Z : Z -> rep;
    sub : rep -> rep -> rep }.
Coercion rep : word_interface >-> Sortclass.
Axiom word : word_interface 64. Local Existing Instance word.
Goal
  forall (x : list word) (x1 x2 : word),
  (unsigned (sub x2 x1) / 2 ^ 4 * 2 ^ 3 <
   unsigned (of_Z 8) * Z.of_nat (Datatypes.length x))%Z.
Proof.
  intros.
  assert (unsigned (sub x2 x1) = unsigned (sub x2 x1)) by exact eq_refl.
  Fail progress rewrite H.
  Fail rewrite H.
Abort.
