(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

Require Ring.
Require Export Field_Compl.
Require Export Field_Theory.

(**** Interpretation A --> ExprA ****)

Recursive Tactic Definition MemAssoc var lvar :=
  Match lvar With
  | [(nilT ?)] -> false
  | [(consT ? ?1 ?2)] ->
    (Match ?1=var With
     | [?1=?1] -> true
     | _ -> (MemAssoc var ?2)).

Recursive Tactic Definition SeekVarAux FT lvar trm :=
  Let AT     = Eval Cbv Beta Delta [A] Iota in (A FT)
  And AzeroT = Eval Cbv Beta Delta [Azero] Iota in (Azero FT)
  And AoneT  = Eval Cbv Beta Delta [Aone] Iota in (Aone FT)
  And AplusT = Eval Cbv Beta Delta [Aplus] Iota in (Aplus FT)
  And AmultT = Eval Cbv Beta Delta [Amult] Iota in (Amult FT)
  And AoppT  = Eval Cbv Beta Delta [Aopp] Iota in (Aopp FT)
  And AinvT  = Eval Cbv Beta Delta [Ainv] Iota in (Ainv FT) In 
  Match trm With
  | [(AzeroT)] -> lvar
  | [(AoneT)] -> lvar
  | [(AplusT ?1 ?2)] ->
    Let l1 = (SeekVarAux FT lvar ?1) In
    (SeekVarAux FT l1 ?2)
  | [(AmultT ?1 ?2)] ->
    Let l1 = (SeekVarAux FT lvar ?1) In
    (SeekVarAux FT l1 ?2)
  | [(AoppT ?1)] -> (SeekVarAux FT lvar ?1)
  | [(AinvT ?1)] -> (SeekVarAux FT lvar ?1)
  | [?1] ->
    Let res = (MemAssoc ?1 lvar) In
    Match res With
    | [(true)] -> lvar
    | [(false)] -> '(consT AT ?1 lvar).

Tactic Definition SeekVar FT trm :=
  Let AT = Eval Cbv Beta Delta [A] Iota in (A FT) In
  (SeekVarAux FT '(nilT AT) trm).

Recursive Tactic Definition NumberAux lvar cpt :=
  Match lvar With
  | [(nilT ?1)] -> '(nilT (prodT ?1 nat))
  | [(consT ?1 ?2 ?3)] ->
    Let l2 = (NumberAux ?3 '(S cpt)) In
    '(consT (prodT ?1 nat) (pairT ?1 nat ?2 cpt) l2).

Tactic Definition Number lvar := (NumberAux lvar O).

Tactic Definition BuildVarList FT trm :=
  Let lvar = (SeekVar FT trm) In
  (Number lvar).
V7only [
(*Used by contrib Maple *)
Tactic Definition build_var_list := BuildVarList.
].

Recursive Tactic Definition Assoc elt lst :=
  Match lst With
  | [(nilT ?)] -> Fail
  | [(consT (prodT ? nat) (pairT ? nat ?1 ?2) ?3)] ->
    Match elt= ?1 With
    | [?1= ?1] -> ?2
    | _ -> (Assoc elt ?3).

Recursive Meta Definition interp_A FT lvar trm :=
  Let AT     = Eval Cbv Beta Delta [A] Iota in (A FT)
  And AzeroT = Eval Cbv Beta Delta [Azero] Iota in (Azero FT)
  And AoneT  = Eval Cbv Beta Delta [Aone] Iota in (Aone FT)
  And AplusT = Eval Cbv Beta Delta [Aplus] Iota in (Aplus FT)
  And AmultT = Eval Cbv Beta Delta [Amult] Iota in (Amult FT)
  And AoppT  = Eval Cbv Beta Delta [Aopp] Iota in (Aopp FT)
  And AinvT  = Eval Cbv Beta Delta [Ainv] Iota in (Ainv FT) In
  Match trm With
  | [(AzeroT)] -> EAzero
  | [(AoneT)] -> EAone
  | [(AplusT ?1 ?2)] ->
    Let e1 = (interp_A FT lvar ?1)
    And e2 = (interp_A FT lvar ?2) In
    '(EAplus e1 e2)
  | [(AmultT ?1 ?2)] ->
    Let e1 = (interp_A FT lvar ?1)
    And e2 = (interp_A FT lvar ?2) In
    '(EAmult e1 e2)
  | [(AoppT ?1)] ->
    Let e = (interp_A FT lvar ?1) In
    '(EAopp e)
  | [(AinvT ?1)] ->
    Let e = (interp_A FT lvar ?1) In
    '(EAinv e)
  | [?1] ->
    Let idx = (Assoc ?1 lvar) In
    '(EAvar idx).

(************************)
(*    Simplification    *)
(************************)

(**** Generation of the multiplier ****)

Recursive Tactic Definition Remove e l :=
  Match l With
  | [(nilT ?)] -> l
  | [(consT ?1 e ?2)] -> ?2
  | [(consT ?1 ?2 ?3)] ->
    Let nl = (Remove e ?3) In
    '(consT ?1 ?2 nl).

Recursive Tactic Definition Union l1 l2 :=
  Match l1 With
  | [(nilT ?)] -> l2
  | [(consT ?1 ?2 ?3)] ->
    Let nl2 = (Remove ?2 l2) In
    Let nl = (Union ?3 nl2) In
    '(consT ?1 ?2 nl).

Recursive Tactic Definition RawGiveMult trm :=
  Match trm With
  | [(EAinv ?1)] -> '(consT ExprA ?1 (nilT ExprA))
  | [(EAopp ?1)] -> (RawGiveMult ?1)
  | [(EAplus ?1 ?2)] ->
    Let l1 = (RawGiveMult ?1)
    And l2 = (RawGiveMult ?2) In
    (Union l1 l2)
  | [(EAmult ?1 ?2)] ->
    Let l1 = (RawGiveMult ?1)
    And l2 = (RawGiveMult ?2) In
    Eval Compute in (appT ExprA l1 l2)
  | _ -> '(nilT ExprA).

Tactic Definition GiveMult trm :=
  Let ltrm = (RawGiveMult trm) In
  '(mult_of_list ltrm).

(**** Associativity ****)

Tactic Definition ApplyAssoc FT lvar trm :=
  Let t=Eval Compute in (assoc trm) In
  Match t=trm With
  | [ ?1=?1 ] -> Idtac
  | _ -> Rewrite <- (assoc_correct FT trm); Change (assoc trm) with t.

(**** Distribution *****)

Tactic Definition ApplyDistrib FT lvar trm :=
  Let t=Eval Compute in (distrib trm) In
  Match t=trm With
  | [ ?1=?1 ] -> Idtac
  | _ -> Rewrite <- (distrib_correct FT trm); Change (distrib trm) with t.

(**** Multiplication by the inverse product ****)

Tactic Definition GrepMult :=
  Match Context With
    | [ id: ~(interp_ExprA ? ? ?)= ? |- ?] -> id.

Tactic Definition WeakReduce :=
  Match Context With
  | [|-[(interp_ExprA ?1 ?2 ?)]] ->
    Cbv Beta Delta [interp_ExprA assoc_2nd eq_nat_dec mult_of_list ?1 ?2 A
                    Azero Aone Aplus Amult Aopp Ainv] Zeta Iota.

Tactic Definition Multiply mul :=
  Match Context With
  | [|-(interp_ExprA ?1 ?2 ?3)=(interp_ExprA ?1 ?2 ?4)] ->
    Let AzeroT = Eval Cbv Beta Delta [Azero ?1] Iota in (Azero ?1) In
    Cut ~(interp_ExprA ?1 ?2 mul)=AzeroT;
    [Intro;
     Let id = GrepMult In
     Apply (mult_eq ?1 ?3 ?4 mul ?2 id)
    |WeakReduce;
     Let AoneT  = Eval Cbv Beta Delta [Aone ?1] Iota in (Aone ?1)
     And AmultT = Eval Cbv Beta Delta [Amult ?1] Iota in (Amult ?1) In
     Try (Match Context With
          | [|-[(AmultT ? AoneT)]] -> Rewrite (AmultT_1r ?1));Clear ?1 ?2].

Tactic Definition ApplyMultiply FT lvar trm :=
  Let t=Eval Compute in (multiply trm) In
  Match t=trm With
  | [ ?1=?1 ] -> Idtac
  | _ -> Rewrite <- (multiply_correct FT trm); Change (multiply trm) with t.

(**** Permutations and simplification ****)

Tactic Definition ApplyInverse mul FT lvar trm :=
  Let t=Eval Compute in (inverse_simplif mul trm) In
  Match t=trm With
  | [ ?1=?1 ] -> Idtac
  | _ -> Rewrite <- (inverse_correct FT trm mul);
         [Change (inverse_simplif mul trm) with t|Assumption].
(**** Inverse test ****)

Tactic Definition StrongFail tac := First [tac|Fail 2].

Recursive Tactic Definition InverseTestAux FT trm :=
  Let AplusT = Eval Cbv Beta Delta [Aplus] Iota in (Aplus FT)
  And AmultT = Eval Cbv Beta Delta [Amult] Iota in (Amult FT)
  And AoppT  = Eval Cbv Beta Delta [Aopp] Iota in (Aopp FT)
  And AinvT  = Eval Cbv Beta Delta [Ainv] Iota in (Ainv FT) In
  Match trm With
  | [(AinvT ?)] -> Fail 1
  | [(AoppT ?1)] -> StrongFail ((InverseTestAux FT ?1);Idtac)
  | [(AplusT ?1 ?2)] ->
    StrongFail ((InverseTestAux FT ?1);(InverseTestAux FT ?2))
  | [(AmultT ?1 ?2)] ->
    StrongFail ((InverseTestAux FT ?1);(InverseTestAux FT ?2))
  | _ -> Idtac.

Tactic Definition InverseTest FT :=
  Let AplusT = Eval Cbv Beta Delta [Aplus] Iota in (Aplus FT) In
  Match Context With
  | [|- ?1=?2] -> (InverseTestAux FT '(AplusT ?1 ?2)).

(**** Field itself ****)

Tactic Definition ApplySimplif sfun :=
  (Match Context With
   | [|- (interp_ExprA ?1 ?2 ?3)=(interp_ExprA ? ? ?)] ->
     (sfun ?1 ?2 ?3));
  (Match Context With
   | [|- (interp_ExprA ? ? ?)=(interp_ExprA ?1 ?2 ?3)] ->
     (sfun ?1 ?2 ?3)).

Tactic Definition Unfolds FT :=
  (Match Eval Cbv Beta Delta [Aminus] Iota in (Aminus FT) With
   | [(Field_Some ? ?1)] -> Unfold ?1
   | _ -> Idtac);
  (Match Eval Cbv Beta Delta [Adiv] Iota in (Adiv FT) With
   | [(Field_Some ? ?1)] -> Unfold ?1
   | _ -> Idtac).

Tactic Definition Reduce FT :=
  Let AzeroT = Eval Cbv Beta Delta [Azero] Iota in (Azero FT)
  And AoneT  = Eval Cbv Beta Delta [Aone] Iota in (Aone FT)
  And AplusT = Eval Cbv Beta Delta [Aplus] Iota in (Aplus FT)
  And AmultT = Eval Cbv Beta Delta [Amult] Iota in (Amult FT)
  And AoppT  = Eval Cbv Beta Delta [Aopp] Iota in (Aopp FT)
  And AinvT  = Eval Cbv Beta Delta [Ainv] Iota in (Ainv FT) In
  Cbv Beta Delta -[AzeroT AoneT AplusT AmultT AoppT AinvT] Zeta Iota
  Orelse Compute.

Recursive Tactic Definition Field_Gen_Aux FT :=
  Let AplusT = Eval Cbv Beta Delta [Aplus] Iota in (Aplus FT) In
  Match Context With
  | [|- ?1=?2] ->
    Let lvar = (BuildVarList FT '(AplusT ?1 ?2)) In
    Let trm1 = (interp_A FT lvar ?1)
    And trm2 = (interp_A FT lvar ?2) In
    Let mul = (GiveMult '(EAplus trm1 trm2)) In
    Cut [ft:=FT][vm:=lvar](interp_ExprA ft vm trm1)=(interp_ExprA ft vm trm2);
    [Compute;Auto
    |Intros ft vm;(ApplySimplif ApplyDistrib);(ApplySimplif ApplyAssoc);
     (Multiply mul);[(ApplySimplif ApplyMultiply);
       (ApplySimplif (ApplyInverse mul));
       (Let id = GrepMult In Clear id);WeakReduce;Clear ft vm;
       First [(InverseTest FT);Ring|(Field_Gen_Aux FT)]|Idtac]].

Tactic Definition Field_Gen FT :=
  Unfolds FT;((InverseTest FT);Ring) Orelse (Field_Gen_Aux FT).
V7only [Tactic Definition field_gen := Field_Gen.].

(*****************************)
(*    Term Simplification    *)
(*****************************)

(**** Minus and division expansions ****)

Meta Definition InitExp FT trm :=
  Let e =
    (Match Eval Cbv Beta Delta [Aminus] Iota in (Aminus FT) With
     | [(Field_Some ? ?1)] -> Eval Cbv Beta Delta [?1] in trm
     | _ -> trm) In
  Match Eval Cbv Beta Delta [Adiv] Iota in (Adiv FT) With
  | [(Field_Some ? ?1)] -> Eval Cbv Beta Delta [?1] in e
  | _ -> e.
V7only [
(*Used by contrib Maple *)
Tactic Definition init_exp := InitExp.
].

(**** Inverses simplification ****)

Recursive Meta Definition SimplInv trm:=
  Match trm With
  | [(EAplus ?1 ?2)] ->
    Let e1 = (SimplInv ?1)
    And e2 = (SimplInv ?2) In
    '(EAplus e1 e2)
  | [(EAmult ?1 ?2)] ->
    Let e1 = (SimplInv ?1)
    And e2 = (SimplInv ?2) In
    '(EAmult e1 e2)
  | [(EAopp ?1)] -> Let e = (SimplInv ?1) In '(EAopp e)
  | [(EAinv ?1)] -> (SimplInvAux ?1)
  | [?1] -> ?1
And SimplInvAux trm :=
  Match trm With
  | [(EAinv ?1)] -> (SimplInv ?1)
  | [(EAmult ?1 ?2)] ->
    Let e1 = (SimplInv '(EAinv ?1))
    And e2 = (SimplInv '(EAinv ?2)) In
    '(EAmult e1 e2)
  | [?1] -> Let e = (SimplInv ?1) In '(EAinv e).

(**** Monom simplification ****)

Recursive Meta Definition Map fcn lst :=
  Match lst With
  | [(nilT ?)] -> lst
  | [(consT ?1 ?2 ?3)] ->
    Let r = (fcn ?2)
    And t = (Map fcn ?3) In
    '(consT ?1 r t).

Recursive Meta Definition BuildMonomAux lst trm :=
  Match lst With
  | [(nilT ?)] -> Eval Compute in (assoc trm)
  | [(consT ? ?1 ?2)] -> BuildMonomAux ?2 '(EAmult trm ?1).

Recursive Meta Definition BuildMonom lnum lden :=
  Let ildn = (Map (Fun e -> '(EAinv e)) lden) In
  Let ltot = Eval Compute in (appT ExprA lnum ildn) In
  Let trm = (BuildMonomAux ltot EAone) In
  Match trm With
  | [(EAmult ? ?1)] -> ?1
  | [?1] -> ?1.

Recursive Meta Definition SimplMonomAux lnum lden trm :=
  Match trm With
  | [(EAmult (EAinv ?1) ?2)] ->
    Let mma = (MemAssoc ?1 lnum) In
    (Match mma With
     | [true] ->
       Let newlnum = (Remove ?1 lnum) In SimplMonomAux newlnum lden ?2
     | [false] -> SimplMonomAux lnum '(consT ExprA ?1 lden) ?2)
  | [(EAmult ?1 ?2)] ->
    Let mma = (MemAssoc ?1 lden) In
    (Match mma With
     | [true] ->
       Let newlden = (Remove ?1 lden) In SimplMonomAux lnum newlden ?2
     | [false] -> SimplMonomAux '(consT ExprA ?1 lnum) lden ?2)
  | [(EAinv ?1)] ->
    Let mma = (MemAssoc ?1 lnum) In
    (Match mma With
     | [true] ->
       Let newlnum = (Remove ?1 lnum) In BuildMonom newlnum lden
     | [false] -> BuildMonom lnum '(consT ExprA ?1 lden))
  | [?1] ->
    Let mma = (MemAssoc ?1 lden) In
    (Match mma With
     | [true] ->
       Let newlden = (Remove ?1 lden) In BuildMonom lnum newlden
     | [false] -> BuildMonom '(consT ExprA ?1 lnum) lden).

Meta Definition SimplMonom trm :=
  SimplMonomAux '(nilT ExprA) '(nilT ExprA) trm.

Recursive Meta Definition SimplAllMonoms trm :=
  Match trm With
  | [(EAplus ?1 ?2)] ->
    Let e1 = (SimplMonom ?1)
    And e2 = (SimplAllMonoms ?2) In
    '(EAplus e1 e2)
  | [?1] -> SimplMonom ?1.

(**** Associativity and distribution ****)

Meta Definition AssocDistrib trm := Eval Compute in (assoc (distrib trm)).

(**** The tactic Field_Term ****)

Tactic Definition EvalWeakReduce trm :=
  Eval Cbv Beta Delta [interp_ExprA assoc_2nd eq_nat_dec mult_of_list A Azero
                       Aone Aplus Amult Aopp Ainv] Zeta Iota in trm.

Tactic Definition Field_Term FT exp :=
  Let newexp = (InitExp FT exp) In
  Let lvar = (BuildVarList FT newexp) In
  Let trm = (interp_A FT lvar newexp) In
  Let tma = Eval Compute in (assoc trm) In
  Let tsmp = (SimplAllMonoms (AssocDistrib (SimplAllMonoms
                (SimplInv tma)))) In
  Let trep = (EvalWeakReduce '(interp_ExprA FT lvar tsmp)) In
  Replace exp with trep;[Ring trep|Field_Gen FT].
