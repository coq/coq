
Lemma foo@{u v w|u <= v, v <= w} : Prop.
Show Universes.
Abort.

Goal True.
  pose (fun x => let y := Type in x y :y).
  Show Universes.
Abort.
(* was:
UNIVERSES:
 {ShowUnivs.5 ShowUnivs.4 ShowUnivs.3 ShowUnivs.2 ShowUnivs.1} |= ShowUnivs.2 < ShowUnivs.3
                                                 ShowUnivs.3 < ShowUnivs.4
                                                 ShowUnivs.3 <= ShowUnivs.5
                                                 ShowUnivs.4 <= ShowUnivs.1
                                                 ShowUnivs.5 <= ShowUnivs.1
ALGEBRAIC UNIVERSES:{ShowUnivs.5 ShowUnivs.4 ShowUnivs.1}
UNDEFINED UNIVERSES:
 ShowUnivs.5
 ShowUnivs.4
 ShowUnivs.3
 ShowUnivs.1
WEAK CONSTRAINTS:


Normalized constraints: {ShowUnivs.3 ShowUnivs.2} |=
ShowUnivs.2 < ShowUnivs.3
*)
