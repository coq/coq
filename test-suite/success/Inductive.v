(* Check local definitions in context of inductive types *)
Inductive A [C,D:Prop; E:=C; F:=D; x,y:E->F] : E -> Set :=
   I : (z:E)(A C D x y z).

Check
   [C,D:Prop; E:=C; F:=D; x,y:(E ->F);
    P:((c:C)(A C D x y c) ->Type);
    f:((z:C)(P z (I C D x y z)));
    y0:C; a:(A C D x y y0)]
    <[y1:C; a0:(A C D x y y1)](P y1 a0)>Cases a of (I x0) => (f x0) end.

Record B [C,D:Set; E:=C; F:=D; x,y:E->F] : Set := { p : C; q : E }.

Check
   [C,D:Set; E:=C; F:=D; x,y:(E ->F);
    P:((B C D x y) ->Type);
    f:((p0,q0:C)(P (Build_B C D x y p0 q0)));
    b:(B C D x y)]
    <[b0:(B C D x y)](P b0)>Cases b of (Build_B x0 x1) => (f x0 x1) end.
