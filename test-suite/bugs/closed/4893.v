Goal True.
evar (P: Prop).
assert (H : P); [|subst P]; [exact I|].
let T := type of H in not_evar T.
