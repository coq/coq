Require Import ssreflect ssrbool.

Set Universe Polymorphism.

Cumulative Variant paths {A} (x:A) : A -> Type
  := idpath : paths x x.

Register paths as core.eq.type.
Register idpath as core.eq.refl.

Structure type := Pack {sort; op : rel sort}.

Example unfold_fold (T : type) (x : sort T) (a : op T x x) : op T x x.
Proof.
  rewrite /op. rewrite -/(op _ _ _). assumption.
Qed.

Example pattern_unfold_fold (b:bool) (a := b) : paths a b.
Proof.
  rewrite [in X in paths X _]/a.
  rewrite -[in X in paths X _]/a.
  constructor.
Qed.

Example unfold_in_hyp (b:bool) (a := b) : unit.
Proof.
  assert (paths a a) as A by reflexivity.
  rewrite [in X in paths X _]/a in A.
  rewrite /a in (B := idpath a).
  rewrite [in X in paths _ X]/a in (C := idpath a).
  constructor.
Qed.

Example fold_in_hyp (b:bool) (p := idpath b) : unit.
Proof.
  assert (paths (idpath b) (idpath b)) as A by reflexivity.
  rewrite -[in X in paths X _]/p in A.
  rewrite -[in X in paths _ X]/p in (C := idpath (idpath b)).
  constructor.
Qed.
