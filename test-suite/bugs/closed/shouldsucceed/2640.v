(* Testing consistency of globalization and interpretation in some
   extreme cases *)

Section sect.

  (* Simplification of the initial example *)
  Hypothesis Other: True.

  Lemma C2 : True.
  proof.
  Fail have True using Other.
  Abort.

  (* Variant of the same problem *)
  Lemma C2 : True.
  Fail clear; Other.
  Abort.
