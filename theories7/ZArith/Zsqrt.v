(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

Require Omega.
Require Export ZArith_base.
Require Export ZArithRing.
V7only [Import Z_scope.].
Open Local Scope Z_scope.

(**********************************************************************)
(** Definition and properties of square root on Z *)

(** The following tactic replaces all instances of (POS (xI ...)) by
    `2*(POS ...)+1` , but only when ... is not made only with xO, XI, or xH. *)
Tactic Definition compute_POS :=
  Match Context With
  | [|- [(POS (xI ?1))]] ->
    (Match ?1 With
     | [[xH]] -> Fail
     | _ -> Rewrite (POS_xI ?1))
  | [|- [(POS (xO ?1))]] ->
    (Match ?1 With
     | [[xH]] -> Fail
     | _ -> Rewrite (POS_xO ?1)).

Inductive sqrt_data [n : Z] : Set :=
  c_sqrt: (s, r :Z)`n=s*s+r`->`0<=r<=2*s`->(sqrt_data n) .

Definition sqrtrempos: (p : positive)  (sqrt_data (POS p)).
Refine (Fix sqrtrempos {
         sqrtrempos [p : positive] : (sqrt_data (POS p)) :=
            <[p : ?]  (sqrt_data (POS p))> Cases p of
                xH => (c_sqrt `1` `1` `0` ? ?)
               | (xO xH) => (c_sqrt `2` `1` `1` ? ?)
               | (xI xH) => (c_sqrt `3` `1` `2` ? ?)
               | (xO (xO p')) =>
                   Cases (sqrtrempos p') of
                     (c_sqrt s' r' Heq Hint) =>
                       Cases (Z_le_gt_dec `4*s'+1` `4*r'`) of
                         (left Hle) =>
                           (c_sqrt (POS (xO (xO p'))) `2*s'+1` `4*r'-(4*s'+1)` ? ?)
                        | (right Hgt) =>
                            (c_sqrt (POS (xO (xO p'))) `2*s'` `4*r'` ? ?)
                       end
                   end
               | (xO (xI p')) =>
                   Cases (sqrtrempos p') of
                     (c_sqrt s' r' Heq Hint) =>
                       Cases
                        (Z_le_gt_dec `4*s'+1` `4*r'+2`) of
                         (left Hle) =>
                           (c_sqrt 
			     (POS (xO (xI p'))) `2*s'+1` `4*r'+2-(4*s'+1)` ? ?)
                        | (right Hgt) =>
                            (c_sqrt (POS (xO (xI p'))) `2*s'` `4*r'+2` ? ?)
                       end
                   end
               | (xI (xO p')) =>
                   Cases (sqrtrempos p') of
                     (c_sqrt s' r' Heq Hint) =>
                       Cases
                        (Z_le_gt_dec `4*s'+1` `4*r'+1`) of
                         (left Hle) =>
                           (c_sqrt
                            (POS (xI (xO p'))) `2*s'+1` `4*r'+1-(4*s'+1)` ? ?)
                        | (right Hgt) =>
                            (c_sqrt (POS (xI (xO p'))) `2*s'` `4*r'+1` ? ?)
                       end
                   end
               | (xI (xI p')) =>
                   Cases (sqrtrempos p') of
                     (c_sqrt s' r' Heq Hint) =>
                       Cases
                        (Z_le_gt_dec `4*s'+1` `4*r'+3`) of
                         (left Hle) =>
                           (c_sqrt
                            (POS (xI (xI p'))) `2*s'+1` `4*r'+3-(4*s'+1)` ? ?)
                        | (right Hgt) =>
                            (c_sqrt (POS (xI (xI p'))) `2*s'` `4*r'+3` ? ?)
                       end
                   end
            end
        }); Clear sqrtrempos; Repeat compute_POS;
 Try (Try Rewrite Heq; Ring; Fail); Try Omega.
Defined.

(** Define with integer input, but with a strong (readable) specification. *)
Definition Zsqrt : (x:Z)`0<=x`->{s:Z & {r:Z | x=`s*s+r` /\ `s*s<=x<(s+1)*(s+1)`}}.
Refine [x]
   <[x:Z]`0<=x`->{s:Z & {r:Z | x=`s*s+r` /\ `s*s<=x<(s+1)*(s+1)`}}>Cases x of
       (POS p) => [h]Cases (sqrtrempos p) of
                    (c_sqrt s r Heq Hint) =>
                  (existS ? [s:Z]{r:Z | `(POS p)=s*s+r` /\ 
		                         `s*s<=(POS p)<(s+1)*(s+1)`}
		   s
                    (exist Z [r:Z]((POS p)=`s*s+r` /\ `s*s<=(POS p)<(s+1)*(s+1)`)
                       r ?))
                  end
     | (NEG p) => [h](False_rec 
		         {s:Z & {r:Z |
			     (NEG p)=`s*s+r` /\ `s*s<=(NEG p)<(s+1)*(s+1)`}}
                         (h (refl_equal ? SUPERIEUR)))
     | ZERO => [h](existS ? [s:Z]{r:Z | `0=s*s+r` /\ `s*s<=0<(s+1)*(s+1)`}
		     `0` (exist Z [r:Z](`0=0*0+r`/\`0*0<=0<(0+1)*(0+1)`)
		     `0` ?))
     end;Try Omega.
Split;[Omega|Rewrite Heq;Ring `(s+1)*(s+1)`;Omega].
Defined.

(** Define a function of type Z->Z that computes the integer square root,
    but only for positive numbers, and 0 for others. *)
Definition Zsqrt_plain : Z->Z :=
  [x]Cases x of
    (POS p)=>Cases (Zsqrt (POS p) (ZERO_le_POS p)) of (existS s _) => s end
   |(NEG p)=>`0`
   |ZERO=>`0`
   end.

(** A basic theorem about Zsqrt_plain *)
Theorem Zsqrt_interval :(x:Z)`0<=x`->
  `(Zsqrt_plain x)*(Zsqrt_plain x)<= x < ((Zsqrt_plain x)+1)*((Zsqrt_plain x)+1)`.
Intros x;Case x.
Unfold Zsqrt_plain;Omega.
Intros p;Unfold Zsqrt_plain;Case (Zsqrt (POS p) (ZERO_le_POS p)).
Intros s (r,(Heq,Hint)) Hle;Assumption.
Intros p Hle;Elim Hle;Auto.
Qed.


