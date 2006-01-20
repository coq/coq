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

(* Check implicit parameters of inductive types (submitted by Pierre
  Casteran and also implicit in #338) *)

Set Implicit Arguments.

CoInductive LList [A:Set] : Set :=
   | LNil : (LList A)
   | LCons : A -> (LList A) -> (LList A).

Implicits LNil [1].

Inductive Finite [A:Set] : (LList A) -> Prop :=
   | Finite_LNil : (Finite LNil)
   | Finite_LCons : (a:A) (l:(LList A)) (Finite l) -> (Finite (LCons a l)).

(* Check positivity modulo reduction (cf bug #983) *)

Record P:Type := {PA:Set; PB:Set}.

Definition F [p:P] := (PA p) -> (PB p).

Inductive I_F:Set := c : (F (Build_P nat I_F)) -> I_F.
