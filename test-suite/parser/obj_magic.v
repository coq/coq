Inversion H.
Absurd (Ex [a:b] c).
Discriminate H.
DEq H.
Injection H.
Replace a with b.
Rewrite <- H with a:=b.
Rewrite <- H with a:=b in H1.
Conditional Auto Rewrite H with 1:=b.
Conditional Auto Rewrite H with 1:=b in H2.
Dependent Rewrite -> H.
CutRewrite -> (a=b).
EAuto 3 4 with a.
Prolog [A (B c)] 4.
EApply H with 1:= H2 a:= b.
Inversion H using (A b).
Inversion H using (A b) in H1 H2.
Ring a b.

Hint Rewrite -> [ (A b) ] in v.
Hint Rewrite <- [ (A b) ] in v using Auto.
