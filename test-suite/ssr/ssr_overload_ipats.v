Require Import ssreflect.

Axiom frl : (nat -> Prop) -> Prop.
Axiom frl_intro : forall P : nat -> Prop, (forall x, P x) -> (frl P).
Notation "`all x , P" := (frl (fun x : _ => P)) (x ident, at level 20).

Lemma test : frl (fun x => x = 0).
Proof.
Fail move=> x.
Fail move=> ?.
Abort.

Hint Extern id 0 (frl _) => apply: frl_intro => id : ssr_intro_id.
Hint Extern 0 (frl _) => apply: frl_intro => ?  : ssr_intro_anon.
Hint Extern 0 (frl _) => apply: frl_intro => _  : ssr_intro_drop.
Hint Extern id 0 => idtac "check" id : ssr_check_hyp_exists.
Hint Extern id 0 => clear id || idtac : ssr_intro_delayed_clear.
Hint Extern o d x 0 => idtac "occ" o "dir" d "subject" x : ssr_intro_subst.

Lemma test : forall w, `all y, `all x, (x = w).
Proof.
move=> ? _ [|x]. Undo.
move=> w {-3}<- x {y q}.
Abort.
