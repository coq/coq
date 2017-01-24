Definition foo := O.
Arguments foo : simpl nomatch.
Timeout 2 Eval cbn in id foo.
