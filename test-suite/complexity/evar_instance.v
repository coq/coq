(* Checks behavior of unification with respect to the size of evar instances *)
(* Expected time < 2.00s *)

(* Note that the exact example chosen is not important as soon as it
   involves a few of each part of the unification algorithme (and especially
   evar-evar unification and evar-term instantiation) *)

(* In 8.2, the example was in O(n^3) in the number of section variables; 
   From current commit it is in O(n^2) *)

(* For the record: with coqtop.byte on a Dual Core 2:

   Nb of extra           T  i  m  e
    variables     8.1    8.2    8.3beta   current
       800       1.6s   188s    185s      1.6s
       400       0.5s    24s     24s      0.43s
       200       0.17s    3s      3.2s    0.12s
       100       0.06s    0.5s    0.48s   0.04s
        50       0.02s    0.08s   0.08s   0.016s
         n      12*a*n^2  a*n^3   a*n^3   8*a*n^2
*)

Set Implicit Arguments.
Parameter t:Set->Set.
Parameter map:forall elt elt' : Set, (elt -> elt') -> t elt -> t elt'.
Parameter avl: forall elt : Set, t elt -> Prop.
Parameter bst: forall elt : Set, t elt -> Prop.
Parameter map_avl: forall (elt elt' : Set) (f : elt -> elt') (m : t elt),
   avl m -> avl (map f m).
Parameter map_bst: forall (elt elt' : Set) (f : elt -> elt') (m : t elt),
   bst m -> bst (map f m).
Record bbst (elt:Set) : Set :=
  Bbst {this :> t elt; is_bst : bst this; is_avl: avl this}.
Definition t' := bbst.
Section B.

Variables
 a b c d e f g h i j k m n o p q r s u v w x y z
 a0 b0 c0 d0 e0 f0 g0 h0 i0 j0 k0 m0 n0 o0 p0 q0 r0 s0 u0 v0 w0 x0 y0 z0
 a1 b1 c1 d1 e1 f1 g1 h1 i1 j1 k1 m1 n1 o1 p1 q1 r1 s1 u1 v1 w1 x1 y1 z1
 a2 b2 c2 d2 e2 f2 g2 h2 i2 j2 k2 m2 n2 o2 p2 q2 r2 s2 u2 v2 w2 x2 y2 z2
 a3 b3 c3 d3 e3 f3 g3 h3 i3 j3 k3 m3 n3 o3 p3 q3 r3 s3 u3 v3 w3 x3 y3 z3
 a4 b4 c4 d4 e4 f4 g4 h4 i4 j4 k4 m4 n4 o4 p4 q4 r4 s4 u4 v4 w4 x4 y4 z4
 a5 b5 c5 d5 e5 f5 g5 h5 i5 j5 k5 m5 n5 o5 p5 q5 r5 s5 u5 v5 w5 x5 y5 z5
 a6 b6 c6 d6 e6 f6 g6 h6 i6 j6 k6 m6 n6 o6 p6 q6 r6 s6 u6 v6 w6 x6 y6 z6

 a7 b7 c7 d7 e7 f7 g7 h7 i7 j7 k7 m7 n7 o7 p7 q7 r7 s7 u7 v7 w7 x7 y7 z7
 a8 b8 c8 d8 e8 f8 g8 h8 i8 j8 k8 m8 n8 o8 p8 q8 r8 s8 u8 v8 w8 x8 y8 z8
 a9 b9 c9 d9 e9 f9 g9 h9 i9 j9 k9 m9 n9 o9 p9 q9 r9 s9 u9 v9 w9 x9 y9 z9
 aA bA cA dA eA fA gA hA iA jA kA mA nA oA pA qA rA sA uA vA wA xA yA zA
 aB bB cB dB eB fB gB hB iB jB kB mB nB oB pB qB rB sB uB vB wB xB yB zB
 aC bC cC dC eC fC gC hC iC jC kC mC nC oC pC qC rC sC uC vC wC xC yC zC
 aD bD cD dD eD fD gD hD iD jD kD mD nD oD pD qD rD sD uD vD wD xD yD zD
 aE bE cE dE eE fE gE hE iE jE kE mE nE oE pE qE rE sE uE vE wE xE yE zE

 aF bF cF dF eF fF gF hF iF jF kF mF nF oF pF qF rF sF uF vF wF xF yF zF
 aG bG cG dG eG fG gG hG iG jG kG mG nG oG pG qG rG sG uG vG wG xG yG zG
 aH bH cH dH eH fH gH hH iH jH kH mH nH oH pH qH rH sH uH vH wH xH yH zH
 aI bI cI dI eI fI gI hI iI jI kI mI nI oI pI qI rI sI uI vI wI xI yI zI
 aJ bJ cJ dJ eJ fJ gJ hJ iJ jJ kJ mJ nJ oJ pJ qJ rJ sJ uJ vJ wJ xJ yJ zJ
 aK bK cK dK eK fK gK hK iK jK kK mK nK oK pK qK rK sK uK vK wK xK yK zK
 aL bL cL dL eL fL gL hL iL jL kL mL nL oL pL qL rL sL uL vL wL xL yL zL
 aM bM cM dM eM fM gM hM iM jM kM mM nM oM pM qM rM sM uM vM wM xM yM zM

 aN bN cN dN eN fN gN hN iN jN kN mN nN oN pN qN rN sN uN vN wN xN yN zN
 aO bO cO dO eO fO gO hO iO jO kO mO nO oO pO qO rO sO uO vO wO xO yO zO
 aP bP cP dP eP fP gP hP iP jP kP mP nP oP pP qP rP sP uP vP wP xP yP zP
 aQ bQ cQ dQ eQ fQ gQ hQ iQ jQ kQ mQ nQ oQ pQ qQ rQ sQ uQ vQ wQ xQ yQ zQ
 aR bR cR dR eR fR gR hR iR jR kR mR nR oR pR qR rR sR uR vR wR xR yR zR
 aS bS cS dS eS fS gS hS iS jS kS mS nS oS pS qS rS sS uS vS wS xS yS zS
 aT bT cT dT eT fT gT hT iT jT kT mT nT oT pT qT rT sT uT vT wT xT yT zT
 aU bU cU dU eU fU gU hU iU jU kU mU nU oU pU qU rU sU uU vU wU xU yU zU

 : nat .

Variables elt elt': Set.
Timeout 5 Time Definition map' f (m:t' elt) : t' elt' :=
  Bbst (map_bst f m.(is_bst)) (map_avl f m.(is_avl)).
