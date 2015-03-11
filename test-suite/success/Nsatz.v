Require Import TestSuite.admit.
(* compile en user    3m39.915s sur cachalot *)
Require Import Nsatz.

(* Example with a generic domain *)

Section test.

Context {A:Type}`{Aid:Integral_domain A}.

Lemma example3 : forall x y z,
  x+y+z==0 ->
  x*y+x*z+y*z==0->
  x*y*z==0 -> x^3%Z==0.
Proof.
Time nsatz. 
Qed.

Lemma example4 : forall x y z u,
  x+y+z+u==0 ->
  x*y+x*z+x*u+y*z+y*u+z*u==0->
  x*y*z+x*y*u+x*z*u+y*z*u==0->
  x*y*z*u==0 -> x^4%Z==0.
Proof.
Time nsatz.
Qed.

Lemma example5 : forall x y z u v,
  x+y+z+u+v==0 ->
  x*y+x*z+x*u+x*v+y*z+y*u+y*v+z*u+z*v+u*v==0->
  x*y*z+x*y*u+x*y*v+x*z*u+x*z*v+x*u*v+y*z*u+y*z*v+y*u*v+z*u*v==0->
  x*y*z*u+y*z*u*v+z*u*v*x+u*v*x*y+v*x*y*z==0 ->
  x*y*z*u*v==0 -> x^5%Z==0.
Proof.
Time nsatz.
Qed.

Goal forall x y:Z,  x = y -> (x+0)%Z = (y*1+0)%Z.
nsatz.
Qed.

Require Import Reals.

Goal forall x y:R,  x = y -> (x+0)%R = (y*1+0)%R.
nsatz.
Qed.

Goal forall a b c x:R, a = b -> b = c -> (a*a)%R = (c*c)%R.
nsatz.
Qed.

End test.

Section Geometry.
(* See the interactive pictures of Laurent Théry 
   on http://www-sop.inria.fr/marelle/CertiGeo/ 
   and research paper on 
   https://docs.google.com/fileview?id=0ByhB3nPmbnjTYzFiZmIyNGMtYTkwNC00NWFiLWJiNzEtODM4NmVkYTc2NTVk&hl=fr
*)

Require Import List.
Require Import Reals.

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
  ((X A)-(X B))^2%Z+((Y A)-(Y B))^2%Z = 0.

Definition nequal2(A B:point):=
  (X A)<>(X B) \/ (Y A)<>(Y B).

Definition nequal3(A B:point):=
  not (((X A)-(X B))^2%Z+((Y A)-(Y B))^2%Z = 0).

Definition middle(A B I:point):=
  2%R*(X I)=(X A)+(X B) /\ 2%R*(Y I)=(Y A)+(Y B).

Definition distance2(A B:point):=
  (X B - X A)^2%Z + (Y B - Y A)^2%Z.

(* AB = CD *)
Definition samedistance2(A B C D:point):=
  (X B - X A)^2%Z + (Y B - Y A)^2%Z = (X D - X C)^2%Z + (Y D - Y C)^2%Z.
Definition determinant(A O B:point):=
  (X A - X O)*(Y B - Y O) - (Y A - Y O)*(X B - X O).
Definition scalarproduct(A O B:point):=
  (X A - X O)*(X B - X O) + (Y A - Y O)*(Y B - Y O).
Definition norm2(A O B:point):=
  ((X A - X O)^2%Z+(Y A - Y O)^2%Z)*((X B - X O)^2%Z+(Y B - Y O)^2%Z).

Definition equaldistance(A B C D:point):=
  ((X B) - (X A))^2%Z + ((Y B) - (Y A))^2%Z =
  ((X D) - (X C))^2%Z + ((Y D) - (Y C))^2%Z.

Definition equaltangente(A B C D E F:point):=
  let s1:= determinant A B C in
  let c1:= scalarproduct A B C in
  let s2:= determinant D E F in
  let c2:= scalarproduct D E F in
  s1 * c2 = s2 * c1.

Ltac cnf2 f :=
  match f with
   | ?A \/ (?B /\ ?C) =>
     let c1 := cnf2 (A\/B) in
     let c2 := cnf2 (A\/C) in constr:(c1/\c2)
   | (?B /\ ?C) \/ ?A =>
     let c1 := cnf2 (B\/A) in
     let c2 := cnf2 (C\/A) in constr:(c1/\c2)
   | (?A \/ ?B) \/ ?C =>
     let c1 := cnf2 (B\/C) in cnf2 (A \/ c1)
   | _ => f
  end
with cnf f :=
  match f with
   | ?A \/ ?B =>
     let c1 := cnf A in
       let c2 := cnf B in
         cnf2 (c1 \/ c2)
   | ?A /\ ?B =>
     let c1 := cnf A in
       let c2 := cnf B in
         constr:(c1 /\ c2)
   | _ => f
  end.
      
Ltac scnf :=
  match goal with
    | |- ?f => let c := cnf f in
      assert c;[repeat split| tauto]
  end.

Ltac disj_to_pol f :=
  match f with
   | ?a = ?b \/ ?g => let p := disj_to_pol g in constr:((a - b)* p)
   | ?a = ?b => constr:(a - b)
  end.

Lemma fastnsatz1:forall x y:R, x - y = 0 -> x = y.
nsatz.
Qed.

Ltac fastnsatz:=
  try trivial; try apply fastnsatz1; try trivial; nsatz.
  
Ltac proof_pol_disj :=
  match goal with
   | |- ?g => let p := disj_to_pol g in
     let h := fresh "hp" in
     assert (h:p = 0);
     [idtac|
      prod_disj h p]
   | _ => idtac
  end
with prod_disj h p :=
  match goal with
   | |- ?a = ?b \/ ?g => 
        match p with
          | ?q * ?p1 => 
        let h0 := fresh "hp" in
        let h1 := fresh "hp" in
        let h2 := fresh "hp" in
        assert (h0:a - b = 0 \/ p1 = 0);
        [apply Rmult_integral; exact h|
         destruct h0 as [h1|h2];
         [left; fastnsatz|
          right; prod_disj h2 p1]]
        end
   | _ => fastnsatz
  end.

(*
Goal forall a b c d e f:R, a=b \/ c=d \/ e=f \/ e=a.
intros. scnf; proof_pol_disj .
admit.*)

Ltac geo_unfold :=
  unfold collinear, parallel, notparallel, orthogonal,
    equal2, equal3, nequal2, nequal3,
    middle, samedistance2,
    determinant, scalarproduct, norm2, distance2,
      equaltangente, determinant, scalarproduct, equaldistance.

Ltac geo_rewrite_hyps:=
  repeat (match goal with
           | h:X _ = _ |- _ => rewrite h in *; clear h
           | h:Y _ = _ |- _ => rewrite h in *; clear h
          end).

Ltac geo_split_hyps:=
  repeat (match goal with
           | h:_ /\ _ |- _ => destruct h
          end).

Ltac geo_begin:=
  geo_unfold;
  intros;
  geo_rewrite_hyps;
  geo_split_hyps;
  scnf; proof_pol_disj.

(* Examples *)

Lemma medians: forall A B C A1 B1 C1 H:point,
  middle B C A1 ->  
  middle A C B1 -> 
  middle A B C1 -> 
  collinear A A1 H -> collinear B B1 H -> 
  collinear C C1 H
  \/ collinear A B C.
Proof. geo_begin.
idtac "Medians".
 Time nsatz.
(*Finished transaction in 2. secs (2.69359u,0.s)
*) Qed.

Lemma Pythagore: forall A B C:point,
  orthogonal A B A C ->
  distance2 A C + distance2 A B = distance2 B C.
Proof. geo_begin.
idtac "Pythagore". 
Time nsatz.
(*Finished transaction in 0. secs (0.354946u,0.s)
*) Qed.

Lemma Thales: forall O A B C D:point,
  collinear O A C -> collinear O B D ->
  parallel A B C D ->
  (distance2 O B * distance2 O C = distance2 O D * distance2 O A
  /\ distance2 O B * distance2 C D = distance2 O D * distance2 A B)
 \/ collinear O A B.
geo_begin.
idtac "Thales".
Time nsatz. (*Finished transaction in 2. secs (1.598757u,0.s)*)
Time nsatz.
Qed.

Lemma segments_of_chords: forall A B C D M O:point,
  equaldistance O A O B ->
  equaldistance O A O C ->
  equaldistance O A O D ->
  collinear A B M ->
  collinear C D M ->
  (distance2 M A) * (distance2 M B) = (distance2 M C) * (distance2 M D)
  \/ parallel A B C D.
Proof. 
geo_begin. 
idtac "segments_of_chords".
Time nsatz.
(*Finished transaction in 3. secs (2.704589u,0.s)
*) Qed.


Lemma isoceles: forall A B C:point,
  equaltangente A B C B C A ->
  distance2 A B = distance2 A C
  \/ collinear A B C.
Proof. geo_begin.  Time nsatz. 
(*Finished transaction in 1. secs (1.140827u,0.s)*) Qed.

Lemma minh: forall A B C D O E H I:point,
  X A = 0 -> Y A = 0 -> Y O = 0 ->
  equaldistance O A O B -> 
  equaldistance O A O C ->
  equaldistance O A O D ->
  orthogonal A C B D ->
  collinear A C E ->
  collinear B D E ->
  collinear A B H ->
  orthogonal E H A B ->
  collinear C D I ->
  middle C D I ->
  collinear H E I
  \/ (X C)^2%Z * (X B)^5%Z * (X O)^2%Z
     * (X C - 2%Z * X O)^3%Z * (-2%Z * X O + X B)=0
  \/  parallel A C B D.
Proof. geo_begin.
idtac "minh". 
Time nsatz with radicalmax :=1%N strategy:=1%Z
  parameters:=(X O::X B::X C::nil)
  variables:= (@nil R).
(*Finished transaction in 13. secs (10.102464u,0.s)
*)
Qed.

Lemma Pappus: forall A B C A1 B1 C1 P Q S:point,
  X A = 0 -> Y A = 0 -> Y B = 0 -> Y C = 0 -> 
  collinear A1 B1 C1 ->
  collinear A B1 P -> collinear A1 B P ->
  collinear A C1 Q -> collinear A1 C Q ->
  collinear B C1 S -> collinear B1 C S ->
  collinear P Q S 
  \/ (Y A1 - Y B1)^2%Z=0 \/ (X A = X B1)
  \/ (X A1 = X C) \/ (X C = X B1)
  \/ parallel A B1 A1 B \/ parallel A C1 A1 C \/ parallel B C1 B1 C.
Proof.
geo_begin.
idtac "Pappus".
Time nsatz with radicalmax :=1%N strategy:=0%Z
  parameters:=(X B::X A1::Y A1::X B1::Y B1::X C::Y C1::nil)
  variables:= (X B
 :: X A1
    :: Y A1
       :: X B1
          :: Y B1
             :: X C
                :: Y C1
                   :: X C1 :: Y P :: X P :: Y Q :: X Q :: Y S :: X S :: nil).
(*Finished transaction in 8. secs (7.795815u,0.000999999999999s)
*)
Qed.

Lemma Simson: forall A B C O D E F G:point,
  X A = 0 -> Y A = 0 -> 
  equaldistance O A O B ->
  equaldistance O A O C ->
  equaldistance O A O D ->
  orthogonal  E D B C ->
  collinear B C E ->
  orthogonal F D A C ->
  collinear A C F ->
  orthogonal G D A B ->
  collinear A B G ->
  collinear E F G
  \/ (X C)^2%Z = 0 \/ (Y C)^2%Z = 0 \/ (X B)^2%Z = 0 \/ (Y B)^2%Z = 0 \/ (Y C - Y B)^2%Z = 0
  \/ equal3 B A 
  \/ equal3 A C \/ (X C - X B)^2%Z = 0
  \/ equal3 B C.
Proof.
geo_begin.
idtac "Simson".
Time nsatz with radicalmax :=1%N strategy:=0%Z
  parameters:=(X B::Y B::X C::Y C::Y D::nil)
  variables:= (@nil R). (* compute -[X Y]. *)
(*Finished transaction in 8. secs (7.550852u,0.s)
*)
Qed.

Lemma threepoints: forall A B C A1 B1 A2 B2 H1 H2 H3:point,
  (* H1 intersection of bisections *)
  middle B C A1 ->  orthogonal H1 A1 B C ->
  middle A C B1 -> orthogonal H1 B1 A C -> 
  (* H2 intersection of medians *)
  collinear A A1 H2 -> collinear B B1 H2 -> 
  (* H3 intersection of altitudes *)
  collinear B C A2 ->  orthogonal A A2 B C ->
  collinear A C B2 -> orthogonal B B2 A C ->
  collinear A A1 H3 -> collinear B B1 H3 -> 
  collinear H1 H2 H3
  \/ collinear A B C.
Proof. geo_begin. 
idtac "threepoints".
Time nsatz. 
(*Finished transaction in 7. secs (6.282045u,0.s)
*) Qed.

Lemma Feuerbach:  forall A B C A1 B1 C1 O A2 B2 C2 O2:point, 
  forall r r2:R,
  X A = 0 -> Y A =  0 -> X B = 1 -> Y B =  0->
  middle A B C1 -> middle B C A1 -> middle C A B1 ->
  distance2 O A1 = distance2 O B1 ->
  distance2 O A1 = distance2 O C1 ->
  collinear A B C2 -> orthogonal A B O2 C2 -> 
  collinear B C A2 -> orthogonal B C O2 A2 ->
  collinear A C B2 -> orthogonal A C O2 B2 ->
  distance2 O2 A2 = distance2 O2 B2 ->
  distance2 O2 A2 = distance2 O2 C2 ->
  r^2%Z = distance2 O A1 ->
  r2^2%Z = distance2 O2 A2 ->
  distance2 O O2 = (r + r2)^2%Z
  \/ distance2 O O2 = (r - r2)^2%Z
  \/ collinear A B C.
Proof. geo_begin. 
idtac "Feuerbach".
Time nsatz. 
(*Finished transaction in 21. secs (19.021109u,0.s)*)
Qed.




Lemma Euler_circle: forall A B C A1 B1 C1 A2 B2 C2 O:point,
  middle A B C1 -> middle B C A1 -> middle C A B1 ->
  orthogonal A B C C2 -> collinear A B C2 ->
  orthogonal B C A A2 -> collinear B C A2 ->
  orthogonal A C B B2 -> collinear A C B2 ->
  distance2 O A1 = distance2 O B1 ->
  distance2 O A1 = distance2 O C1 ->
  (distance2 O A2 = distance2 O A1
   /\distance2 O B2 = distance2 O A1
   /\distance2 O C2 = distance2 O A1)
  \/ collinear A B C.
Proof. geo_begin. 
idtac "Euler_circle 3 goals".
Time nsatz. 
(*Finished transaction in 13. secs (11.208296u,0.124981s)*)
Time nsatz.  
(*Finished transaction in 10. secs (8.846655u,0.s)*) 
Time nsatz. 
(*Finished transaction in 11. secs (9.186603u,0.s)*)
Qed.



Lemma Desargues: forall A B C A1 B1 C1 P Q R S:point,
  X S = 0 -> Y S = 0 -> Y A = 0 ->
  collinear A S A1 -> collinear B S B1 -> collinear C S C1 ->
  collinear B1 C1 P -> collinear B C P ->
  collinear A1 C1 Q -> collinear A C Q -> 
  collinear A1 B1 R -> collinear A B R ->
  collinear P Q R
  \/ X A = X B \/ X A = X C \/ X B = X C  \/ X A = 0 \/ Y B = 0 \/ Y C = 0
  \/ collinear S B C \/ parallel A C A1 C1 \/ parallel A B A1 B1.
Proof.
geo_begin.
idtac "Desargues".
Time 
let lv := rev (X A
 :: X B
    :: Y B
       :: X C
          :: Y C
             :: Y A1 :: X A1
                :: Y B1
                   :: Y C1
                      :: X R
                         :: Y R
                            :: X Q
                               :: Y Q :: X P :: Y P :: X C1 :: X B1 :: nil) in
nsatz with radicalmax :=1%N strategy:=0%Z
  parameters:=(X A::X B::Y B::X C::Y C::X A1::Y B1::Y C1::nil)
  variables:= lv. (*Finished transaction in 8. secs (8.02578u,0.001s)*)
Qed.

Lemma chords: forall O A B C D M:point,
  equaldistance O A O B ->
  equaldistance O A O C ->
  equaldistance O A O D ->
  collinear A B M -> collinear C D M ->
  scalarproduct A M B = scalarproduct C M D
  \/ parallel A B C D.
Proof. geo_begin. 
idtac "chords".
 Time nsatz. 
(*Finished transaction in 4. secs (3.959398u,0.s)*)
Qed.

Lemma Ceva: forall A B C D E F M:point,
  collinear M A D -> collinear M B E -> collinear M C F ->
  collinear B C D -> collinear E A C -> collinear F A B ->
  (distance2 D B) * (distance2 E C) * (distance2 F A) =
  (distance2 D C) * (distance2 E A) * (distance2 F B)
  \/ collinear A B C.
Proof. geo_begin. 
idtac "Ceva".
Time nsatz.
(*Finished transaction in 105. secs (104.121171u,0.474928s)*)
Qed.

Lemma bissectrices: forall A B C M:point,
  equaltangente C A M M A B ->
  equaltangente A B M M B C ->
  equaltangente B C M M C A
  \/ equal3 A B.
Proof. geo_begin. 
idtac "bissectrices".
Time nsatz.
(*Finished transaction in 2. secs (1.937705u,0.s)*)
Qed.

Lemma bisections: forall A B C A1 B1 C1 H:point,
  middle B C A1 ->  orthogonal H A1 B C ->
  middle A C B1 -> orthogonal H B1 A C -> 
  middle A B C1 -> 
  orthogonal H C1 A B 
  \/ collinear A B C.
Proof. geo_begin.
idtac "bisections". 
Time nsatz. (*Finished transaction in 2. secs (2.024692u,0.002s)*)
Qed.

Lemma altitudes: forall A B C A1 B1 C1 H:point,
  collinear B C A1 ->  orthogonal A A1 B C ->
  collinear A C B1 -> orthogonal B B1 A C -> 
  collinear A B C1 -> orthogonal C C1 A B ->
  collinear A A1 H -> collinear B B1 H -> 
  collinear C C1 H
  \/ equal2 A B
  \/ collinear A B C.
Proof. geo_begin.
idtac "altitudes".
Time nsatz. (*Finished transaction in 3. secs (3.001544u,0.s)*)
Time nsatz. (*Finished transaction in 4. secs (3.113527u,0.s)*)
Qed.

Lemma hauteurs:forall A B C A1 B1 C1 H:point,
  collinear B C A1 ->  orthogonal A A1 B C ->
  collinear A C B1 -> orthogonal B B1 A C -> 
  collinear A B C1 -> orthogonal C C1 A B ->
  collinear A A1 H -> collinear B B1 H -> 
  
  collinear C C1 H
  \/ collinear A B C.

geo_begin.
idtac "hauteurs".
Time 
 let lv := constr:(Y A1
 :: X A1 :: Y B1 :: X B1 :: Y A :: Y B :: X B :: X A :: X H :: Y C
 :: Y C1 :: Y H :: X C1 :: X C :: (@Datatypes.nil R)) in
nsatz with radicalmax := 2%N strategy := 1%Z parameters := (@Datatypes.nil R)
 variables := lv.
(*Finished transaction in 5. secs (4.360337u,0.008999s)*)
Qed.


End Geometry.

