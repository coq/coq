Ltac induction_with_subterm c H :=
  let x := fresh "x" in
  let y := fresh "y" in
  (set(x := c) ; assert(y:x = c) by reflexivity ;
  rewrite <- y in H ; 
  induction H ; subst).

Ltac induction_on_subterm c :=
  let x := fresh "x" in
  let y := fresh "y" in
  (set(x := c) ; assert(y:x = c) by reflexivity ; clearbody x ; induction x ; inversion y ; try subst ; 
  clear y).

Ltac induction_with_subterms c c' H :=
  let x := fresh "x" in
  let y := fresh "y" in
  let z := fresh "z" in
  let w := fresh "w" in
  (set(x := c) ; assert(y:x = c) by reflexivity ;
  set(z := c') ; assert(w:z = c') by reflexivity ;
  rewrite <- y in H ; rewrite <- w in H ; 
  induction H ; subst).
