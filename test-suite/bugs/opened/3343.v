(* File reduced by coq-bug-finder from original input, then from 13699 lines to 656 lines, then from 584 lines to 200 lines *)
Set Asymmetric Patterns.
Require Export Coq.Lists.List.
Export List.ListNotations.

Record CFGV := { Terminal : Type; VarSym : Type }.

Section Gram.
  Context  {G : CFGV}.

  Inductive  Pattern : (Terminal G) -> Type :=
  | ptleaf : forall (T : Terminal G),
               nat -> Pattern T
  with Mixture : list (Terminal G) -> Type :=
  | mtcons : forall {h: Terminal G}
                    {tl: list (Terminal G)},
               Pattern h -> Mixture tl -> Mixture (h::tl).

  Variable vc : VarSym G.

  Fixpoint pBVars {gs}  (p : Pattern gs) : (list nat) :=
    match p with
      | ptleaf _ _ => []
    end
  with mBVars {lgs} (pts : Mixture lgs) : (list nat) :=
         match pts with
           | mtcons _ _ _ tl =>  mBVars  tl
         end.

  Lemma mBndngVarsAsNth :
    forall mp (m : @Mixture mp),
      mBVars m = [2].
  Proof.
    intros.
    induction m. progress simpl.
  Admitted.
End Gram.

Lemma mBndngVarsAsNth' {G : CFGV} { vc  : VarSym G} :
  forall mp (m : @Mixture G mp),
    mBVars m = [2].
Proof.
  intros.
  induction m.
  Fail progress simpl.
  (* simpl did nothing here, while it does something inside the section; this is probably a bug*)
