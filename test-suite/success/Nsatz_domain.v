Require Import Nsatz_domain ZArith Reals List Ring_polynom.

Variable A: Type.
Variable Ad: Domain A.

Add Ring Ar1: (@ring_ring A (@domain_ring _ Ad)).

Instance Ari : Ring A := {
  ring0 := @ring0 A (@domain_ring _ Ad);
  ring1 := @ring1 A (@domain_ring _ Ad);
  ring_plus := @ring_plus A (@domain_ring _ Ad);
  ring_mult := @ring_mult A (@domain_ring _ Ad);
  ring_sub := @ring_sub A (@domain_ring _ Ad);
  ring_opp := @ring_opp A (@domain_ring _ Ad);  
  ring_ring := @ring_ring A (@domain_ring _ Ad)}.

Instance Adi : Domain A := {
  domain_ring := Ari;
  domain_axiom_product := @domain_axiom_product A Ad;
  domain_axiom_one_zero := @domain_axiom_one_zero A Ad}.

Instance zero_ring2 : Zero A := {zero := ring0}.
Instance one_ring2 : One A := {one := ring1}.
Instance addition_ring2 : Addition A := {addition x y := ring_plus x y}.
Instance multiplication_ring2 : Multiplication A := {multiplication x y := ring_mult x y}.
Instance subtraction_ring2 : Subtraction A := {subtraction x y := ring_sub x y}.
Instance opposite_ring2 : Opposite A := {opposite x := ring_opp x}.

Goal forall x y:A,  x = y -> x+0 = y*1+0.
nsatz_domain.
Qed.

Goal forall a b c:A, a = b -> b = c -> c = a.
nsatz_domain.
Qed.

Goal forall a b c:A, a = b -> b = c -> a = c.
nsatz_domain.
Qed.

Goal forall a b c x:A, a = b -> b = c -> a*a = c*c.
nsatz_domain.
Qed.

Goal forall x y:Z,  x = y -> (x+0)%Z = (y*1+0)%Z.
nsatz_domainZ.
Qed.

Goal forall x y:R,  x = y -> (x+0)%R = (y*1+0)%R.
nsatz_domainR.
Qed.

Goal forall a b c x:R, a = b -> b = c -> (a*a)%R = (c*c)%R.
nsatz_domainR.
Qed.

Section Examples.

Delimit Scope PE_scope with PE.
Infix "+" := PEadd : PE_scope.
Infix "*" := PEmul : PE_scope.
Infix "-" := PEsub : PE_scope.
Infix "^" := PEpow : PE_scope.
Notation "[ n ]" := (@PEc Z n) (at level 0).

Open Scope R_scope.

Lemma example1 : forall x y,
  x+y=0 ->
  x*y=0 ->
  x^2=0.
Proof.
 nsatz_domainR.
Qed.

Lemma example2 : forall x, x^2=0 -> x=0.
Proof.
 nsatz_domainR.
Qed.

(*
Notation X  := (PEX Z 3).
Notation Y  := (PEX Z 2).
Notation Z_ := (PEX Z 1).
*)
Lemma example3 : forall x y z,
  x+y+z=0 ->
  x*y+x*z+y*z=0->
  x*y*z=0 -> x^3=0.
Proof.
Time nsatz_domainR.
simpl.
discrR.
Qed.

(*
Notation X  := (PEX Z 4).
Notation Y  := (PEX Z 3).
Notation Z_ := (PEX Z 2).
Notation U  := (PEX Z 1).
*)
Lemma example4 : forall x y z u,
  x+y+z+u=0 ->
  x*y+x*z+x*u+y*z+y*u+z*u=0->
  x*y*z+x*y*u+x*z*u+y*z*u=0->
  x*y*z*u=0 -> x^4=0.
Proof.
Time nsatz_domainR.
Qed.

(*
Notation x_ := (PEX Z 5).
Notation y_ := (PEX Z 4).
Notation z_ := (PEX Z 3).
Notation u_ := (PEX Z 2).
Notation v_ := (PEX Z 1).
Notation "x :: y" := (List.cons x y)
(at level 60, right associativity, format "'[hv' x  ::  '/' y ']'").
Notation "x :: y" := (List.app x y)
(at level 60, right associativity, format "x :: y").
*)

Lemma example5 : forall x y z u v,
  x+y+z+u+v=0 ->
  x*y+x*z+x*u+x*v+y*z+y*u+y*v+z*u+z*v+u*v=0->
  x*y*z+x*y*u+x*y*v+x*z*u+x*z*v+x*u*v+y*z*u+y*z*v+y*u*v+z*u*v=0->
  x*y*z*u+y*z*u*v+z*u*v*x+u*v*x*y+v*x*y*z=0 ->
  x*y*z*u*v=0 -> x^5=0.
Proof.
Time nsatz_domainR.
Qed.

End Examples.

Section Geometry.

Open Scope R_scope.

Record point:Type:={
 X:R;
 Y:R}.

Definition collinear(A B C:point):=
  (X A - X B)*(Y C - Y B)-(Y A - Y B)*(X C - X B)=0.

Definition parallel (A B C D:point):=
  ((X A)-(X B))*((Y C)-(Y D))=((Y A)-(Y B))*((X C)-(X D)).

Definition notparallel (A B C D:point)(x:R):=
  x*(((X A)-(X B))*((Y C)-(Y D))-((Y A)-(Y B))*((X C)-(X D)))=1.

Definition orthogonal (A B C D:point):=
  ((X A)-(X B))*((X C)-(X D))+((Y A)-(Y B))*((Y C)-(Y D))=0.

Definition equal2(A B:point):=
  (X A)=(X B) /\ (Y A)=(Y B).

Definition equal3(A B:point):=
  ((X A)-(X B))^2+((Y A)-(Y B))^2 = 0.

Definition nequal2(A B:point):=
  (X A)<>(X B) \/ (Y A)<>(Y B).

Definition nequal3(A B:point):=
  not (((X A)-(X B))^2+((Y A)-(Y B))^2 = 0).

Definition middle(A B I:point):=
  2*(X I)=(X A)+(X B) /\ 2*(Y I)=(Y A)+(Y B).

Definition distance2(A B:point):=
  (X B - X A)^2 + (Y B - Y A)^2.

(* AB = CD *)
Definition samedistance2(A B C D:point):=
  (X B - X A)^2 + (Y B - Y A)^2 = (X D - X C)^2 + (Y D - Y C)^2.
Definition determinant(A O B:point):=
  (X A - X O)*(Y B - Y O) - (Y A - Y O)*(X B - X O).
Definition scalarproduct(A O B:point):=
  (X A - X O)*(X B - X O) + (Y A - Y O)*(Y B - Y O).
Definition norm2(A O B:point):=
  ((X A - X O)^2+(Y A - Y O)^2)*((X B - X O)^2+(Y B - Y O)^2).


Lemma a1:forall A B C:Prop, ((A\/B)/\(A\/C)) -> (A\/(B/\C)).
intuition.
Qed.
 
Lemma a2:forall A B C:Prop, ((A\/C)/\(B\/C)) -> ((A/\B)\/C).
intuition.
Qed.

Lemma a3:forall a b c d:R, (a-b)*(c-d)=0 -> (a=b \/ c=d).
intros.
assert ( (a-b = 0) \/ (c-d = 0)).
apply Rmult_integral.
trivial.
destruct H0.
left; nsatz_domainR.
right; nsatz_domainR.
Qed.

Ltac geo_unfold :=
  unfold collinear; unfold parallel; unfold notparallel; unfold orthogonal;
  unfold equal2; unfold equal3; unfold nequal2; unfold nequal3; 
  unfold middle; unfold samedistance2; 
  unfold determinant; unfold scalarproduct; unfold norm2; unfold distance2.

Ltac geo_end :=
  repeat (
  repeat (match goal with h:_/\_ |- _ => decompose [and] h; clear h end);
  repeat (apply a1 || apply a2 || apply a3);
  repeat split).

Ltac geo_rewrite_hyps:=
  repeat (match goal with
           | h:X _ = _ |- _ => rewrite h in *; clear h
           | h:Y _ = _ |- _ => rewrite h in *; clear h
          end).

Ltac geo_begin:=
  geo_unfold;
  intros;
  geo_rewrite_hyps;
  geo_end.

(* Examples *)

Lemma Thales: forall O A B C D:point,
  collinear O A C -> collinear O B D ->
  parallel A B C D ->
  (distance2 O B * distance2 O C = distance2 O D * distance2 O A
  /\ distance2 O B * distance2 C D = distance2 O D * distance2 A B)
 \/ collinear O A B.
repeat geo_begin.

Time nsatz_domainR.
simpl;discrR.
Time nsatz_domainR.
simpl;discrR.
Qed.

Require Import NsatzR.

Lemma hauteurs:forall A B C A1 B1 C1 H:point,
  collinear B C A1 ->  orthogonal A A1 B C ->
  collinear A C B1 -> orthogonal B B1 A C -> 
  collinear A B C1 -> orthogonal C C1 A B ->
  collinear A A1 H -> collinear B B1 H -> 
  
  collinear C C1 H
  \/ collinear A B C.

geo_begin.
(* Time nsatzRpv 2%N 1%Z (@nil R) (@nil R).*)
(*Finished transaction in 3. secs (2.363641u,0.s)*)
(*Time nsatz_domainR. trop long! *)
(* en fait nsatz_domain ne tient pas encore compte de la liste des variables! ;-) *)
Time 
 let lv := constr:(Y A1
 :: X A1
    :: Y B1
       :: X B1
          :: Y A0
             :: Y B
                :: X B
                   :: X A0
                      :: X H
                         :: Y C
                            :: Y C1 :: Y H :: X C1 :: X C ::nil) in
 nsatz_domainpv 2%N 1%Z (@List.nil R) lv ltac:simplR Rdi.
(* Finished transaction in 6. secs (5.579152u,0.001s) *)
Qed.

End Geometry.
