Goal let x:=O+O in x=x.
intro.
set (y1:=O) in (type of x).
Show.
set (y2:=O) in (value of x) at 1.
Show.
set (y3:=O) in (value of x).
Show.
trivial.
Qed.
