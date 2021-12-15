Definition foo := O.
Arguments foo : simpl nomatch.
Timeout 1 Eval cbn in id foo.
