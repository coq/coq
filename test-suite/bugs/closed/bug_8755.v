
Lemma f : Type.
Fail let i := ident:(i) in
let t := context i [Type] in
idtac.
Abort.
