#[local] Hint Extern 10 ((?X = ?Y) -> False) => intros; discriminate : core.
#[local] Hint Unfold not : core.

Goal true<>false.
typeclasses eauto with core.
Qed.
