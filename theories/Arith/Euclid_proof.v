
(* $Id$ *)

Require Euclid_def.
Require Compare_dec.
Require Wf_nat.

Lemma eucl_dev : (b:nat)(gt b O)->(a:nat)(diveucl a b).
Intros b H a; Pattern a; Apply gt_wf_rec; Intros n H0.
Elim (le_gt_dec b n).
Intro lebn.
Elim (H0 (minus n b)); Auto with arith.
Intros q r g e.
Apply divex with (S q) r; Simpl; Auto with arith.
Elim plus_assoc_l.
Elim e; Auto with arith.
Intros gtbn.
Apply divex with O n; Simpl; Auto with arith.
Save.

Lemma quotient : (b:nat)(gt b O)->
     (a:nat){q:nat|(EX r:nat | (a=(plus (mult q b) r))/\(gt b r))}.
Intros b H a; Pattern a; Apply gt_wf_rec; Intros n H0.
Elim (le_gt_dec b n).
Intro lebn.
Elim (H0 (minus n b)); Auto with arith.
Intros q Hq; Exists (S q).
Elim Hq; Intros r Hr.
Exists r; Simpl; Elim Hr; Intros.
Elim plus_assoc_l.
Elim H1; Auto with arith.
Intros gtbn.
Exists O; Exists n; Simpl; Auto with arith.
Save.

Lemma modulo : (b:nat)(gt b O)->
     (a:nat){r:nat|(EX q:nat | (a=(plus (mult q b) r))/\(gt b r))}.
Intros b H a; Pattern a; Apply gt_wf_rec; Intros n H0.
Elim (le_gt_dec b n).
Intro lebn.
Elim (H0 (minus n b)); Auto with arith.
Intros r Hr; Exists r.
Elim Hr; Intros q Hq.
Elim Hq; Intros; Exists (S q); Simpl.
Elim plus_assoc_l.
Elim H1; Auto with arith.
Intros gtbn.
Exists n; Exists O; Simpl; Auto with arith.
Save.
