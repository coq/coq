Goal True.
set (x := 0).
Succeed set (y := 0) in x.
Succeed set (y := 0) in x at 1.
Fail set (y := 0) in x at 2.
Abort.
