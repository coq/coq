(* IN 8.5pl2 and 8.6 (4da2131), the following shows different typeclass resolution behaviors following an unshelve tactical vs. an Unshelve command: *)

(*Pose an open constr to prevent immediate typeclass resolution in holes:*)
Tactic Notation "opose" open_constr(x) "as" ident(H) := pose x as H.

Inductive vect A : nat -> Type :=
| vnil : vect A 0
| vcons : forall (h:A) (n:nat), vect A n -> vect A (S n).

Class Eqdec A := eqdec : forall a b : A, {a=b}+{a<>b}.

Require Bool.

Instance Bool_eqdec : Eqdec bool := Bool.bool_dec.

Context `{vect_sigT_eqdec : forall A : Type, Eqdec A -> Eqdec {a : nat & vect A a}}.

Typeclasses eauto := debug.

Goal True.
  unshelve opose (@vect_sigT_eqdec _ _ _ _) as H.
  all:cycle 2.
  eapply existT. (*BUG: Why does this do typeclass resolution in the evar?*)
  Focus 5.
Abort.

Goal True.
  opose (@vect_sigT_eqdec _ _ _ _) as H.
  Unshelve.
  all:cycle 3.
  eapply existT. (*This does no typeclass resultion, which is correct.*)
  Focus 5.
Abort.
