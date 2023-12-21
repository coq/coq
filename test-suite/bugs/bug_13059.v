Set Uniform Inductive Parameters.
Inductive test (X : Set) : Prop :=
with test2 (X : Set) : X -> Prop :=
 | C (x : X) : test2 x.

Require Import TestSuite.list.

Set Suggest Proof Using.
Set Primitive Projections.


Section Grammar.
Variable A : Type.

Record grammar : Type := Grammar {
  gm_nonterm :> Type ;
  gm_rules :> list (gm_nonterm * list (A + gm_nonterm)) ;
}.

Set Uniform Inductive Parameters.
Inductive lang (gm : grammar) : gm -> list A -> Prop :=
| lang_rule S ps ws : In (S, ps) gm -> lmatch ps ws -> lang S (concat ws)
with lmatch (gm : grammar) : list (A + gm) -> list (list A) -> Prop :=
| lmatch_nil : lmatch nil nil
| lmatch_consL ps ws a : lmatch ps ws -> lmatch (inl a :: ps) (cons (cons a nil) ws)
| lmatch_consR ps ws S w :
    lang S w -> lmatch ps ws -> lmatch (inr S :: ps) (w :: ws)
.

End Grammar.
