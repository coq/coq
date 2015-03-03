Hint Extern 10 ((?X = ?Y) -> False) => intros; discriminate.
Hint Unfold not : core.

Goal true<>false.
Set Typeclasses Debug.
typeclasses eauto with core.
Qed.