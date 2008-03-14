(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id$ *)

(* This file contains proofs of programs taken from the
 * "Handbook of Theoretical Computer Science", volume B,
 * chapter "Methods and Logics for Proving Programs", by P. Cousot,
 * pp 841--993, Edited by J. van Leeuwen (c) Elsevier Science Publishers B.V.
 * 1990.
 * 
 * Programs are refered to by numbers and pages.
 *)

Require Correctness.

Require Sumbool.
Require Omega.
Require Zcomplements.
Require Zpower.

(****************************************************************************)

(* program (2) page 853 to compute x^y (annotated version is (25) page 860) *)

(* en attendant... *)
Parameter Zdiv2  : Z->Z.

Parameter Zeven_odd_dec : (x:Z){`x=2*(Zdiv2 x)`}+{`x=2*(Zdiv2 x)+1`}.
Definition Zodd_dec := [z:Z](sumbool_not ? ? (Zeven_odd_dec z)).
Definition Zodd_bool := [z:Z](bool_of_sumbool ? ? (Zodd_dec z)).

Axiom axiom1 : (x,y:Z) `y>0` -> `x*(Zpower x (Zpred y)) = (Zpower x y)`.
Axiom axiom2 : (x:Z)`x>0` -> `(Zdiv2 x)<x`.
Axiom axiom3 : (x,y:Z) `y>=0` -> `(Zpower (x*x) (Zdiv2 y)) = (Zpower x y)`.

Global Variable X : Z ref.
Global Variable Y : Z ref.
Global Variable Z_ : Z ref.

Correctness pgm25
  { `Y >= 0` }
  begin
    Z_ := 1;
    while !Y <> 0 do
      { invariant `Y >= 0` /\ `Z_ * (Zpower X Y) = (Zpower X@0 Y@0)`
        variant Y }
      if (Zodd_bool !Y) then begin
      	Y := (Zpred !Y);
	Z_ := (Zmult !Z_ !X)
      end else begin
      	Y := (Zdiv2 !Y);	
	X := (Zmult !X !X)
      end
    done
  end
  { Z_ = (Zpower X@ Y@) }.
Proof.
Split.
Unfold Zpred; Unfold Zwf; Omega.
Split.
Unfold Zpred; Omega.
Decompose [and] Pre2.
Rewrite <- H0.
Replace `Z_1*X0*(Zpower X0 (Zpred Y0))` with `Z_1*(X0*(Zpower X0 (Zpred Y0)))`.
Apply f_equal with f := (Zmult Z_1).
Apply axiom1.
Omega.

Auto.
Symmetry.
Apply Zmult_assoc_r.

Split.
Unfold Zwf.
Repeat (Apply conj).
Omega.

Omega.

Apply axiom2. Omega.

Split.
Omega.

Decompose [and] Pre2.
Rewrite <- H0.
Apply f_equal with f:=(Zmult Z_1).
Apply axiom3. Omega.

Omega.

Decompose [and] Post6.
Rewrite <- H2.
Rewrite H0.
Simpl.
Omega.

Save.


(****************************************************************************)

(* program (178) page 934 to compute the factorial using global variables
 * annotated version is (185) page 939
 *)

Parameter Zfact : Z -> Z.

Axiom axiom4 : `(Zfact 0) = 1`.
Axiom axiom5 : (x:Z) `x>0` -> `(Zfact (x-1))*x=(Zfact x)`.

Correctness pgm178
let rec F (u:unit) : unit { variant X } =
  { `X>=0` }
  (if !X = 0 then
    Y := 1
  else begin
    label L;
    X := (Zpred !X);
    (F tt);
    X := (Zs !X);
    Y := (Zmult !Y !X)
  end)
  { `X=X@` /\ `Y=(Zfact X@)` }.
Proof.
Rewrite Test1. Rewrite axiom4. Auto.
Unfold Zwf. Unfold Zpred. Omega.
Unfold Zpred. Omega.
Unfold Zs. Unfold Zpred in Post3. Split.
Omega.
Decompose [and] Post3.
Rewrite H.
Replace `X0+(-1)+1` with X0.
Rewrite H0.
Replace `X0+(-1)` with `X0-1`.
Apply axiom5.
Omega.
Omega.
Omega.
Save.


(****************************************************************************)

(* program (186) page 939 "showing the usefulness of auxiliary variables" ! *)

Global Variable N : Z ref.
Global Variable S : Z ref.

Correctness pgm186
let rec F (u:unit) : unit { variant N } =
  { `N>=0` }
  (if !N > 0 then begin
    label L;
    N := (Zpred !N);
    (F tt);
    S := (Zs !S);
    (F tt);
    N := (Zs !N)
  end)
  { `N=N@` /\ `S=S@+(Zpower 2 N@)-1` }.
Proof.
Unfold Zwf. Unfold Zpred. Omega.
Unfold Zpred. Omega.
Decompose [and] Post5. Rewrite H. Unfold Zwf. Unfold Zpred. Omega.
Decompose [and] Post5. Rewrite H. Unfold Zpred. Omega.
Split.
Unfold Zpred in Post5. Omega.
Decompose [and] Post4. Rewrite H0. 
Decompose [and] Post5. Rewrite H2. Rewrite H1. 
Replace `(Zpower 2 N0)` with `2*(Zpower 2 (Zpred N0))`. Omega.
Symmetry.
Replace `(Zpower 2 N0)` with `(Zpower 2 (1+(Zpred N0)))`.
Replace `2*(Zpower 2 (Zpred N0))` with `(Zpower 2 1)*(Zpower 2 (Zpred N0))`.
Apply Zpower_exp.
Omega.
Unfold Zpred. Omega.
Auto.
Replace `(1+(Zpred N0))` with N0; [ Auto | Unfold Zpred; Omega ].
Split.
Auto.
Replace N0 with `0`; Simpl; Omega.
Save.


(****************************************************************************)

(* program (196) page 944 (recursive factorial procedure with value-result
 * parameters)
 *)

Correctness pgm196
let rec F (U:Z) (V:Z ref) : unit { variant U } =
  { `U >= 0` }
  (if U = 0 then
    V := 1
  else begin
    (F (Zpred U) V);	
    V := (Zmult !V U)
  end)
  { `V = (Zfact U)` }.
Proof.
Symmetry. Rewrite Test1. Apply axiom4.
Unfold Zwf. Unfold Zpred. Omega.
Unfold Zpred. Omega.
Rewrite Post3. 
Unfold Zpred. Replace `U0+(-1)` with `U0-1`. Apply axiom5.
Omega.
Omega.
Save.

(****************************************************************************)

(* program (197) page 945 (L_4 subset of Pascal) *)

(*
procedure P(X:Z; procedure Q(Z:Z));
  procedure L(X:Z); begin Q(X-1) end;
  begin if X>0 then P(X-1,L) else Q(X) end;

procedure M(N:Z);
  procedure R(X:Z); begin writeln(X) (* => RES := !X *) end;
  begin P(N,R) end.
*)
