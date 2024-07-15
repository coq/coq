Inductive coulfeu : Set :=
  | Vert : coulfeu
  | Orange : coulfeu
  | Rouge : coulfeu
.


Definition coul_suiv : coulfeu -> coulfeu :=
  fun c =>
    match c with
    | Vert => Orange
    | Orange => Rouge
    | Rouge => Vert
    end.

Theorem th_crou_gen : forall c : coulfeu, c = Rouge -> coul_suiv c = Vert.
Proof.
  intro c0.
  (** Pour démontrer [c0 = Rouge -> coul_suiv c0 = Vert],
      on suppose [c0 = Rouge]
      et on doit alors prouver [coul_suiv c0 = Vert]
      sous cette hypothèse supplémentaire ;
      lorsque l'on introduit une hypothèse, on lui donne un nom. *)
  intro c0rou. (* /!\   CRASH ON THIS LINE   /!\ *)
  (** Le raisonnement sous-jacent est :
      soit c0rou une preuve arbitraire (inconnue) de [c0 = Rouge],
      on peut s'en servir pour démontrer coul_suiv [c0 = Vert]. *)
  rewrite c0rou. cbn [coul_suiv]. reflexivity.
Qed.
