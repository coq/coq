(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

Require Ring.
Require Export Field_Compl.
Require Export Field_Theory.

(**** Interpretation A --> ExprA ****)

Recursive Tactic Definition MemAssoc var lvar :=
  Match lvar With
  | [(nil ?)] -> false
  | [(cons ? ?1 ?2)] ->
    (Match ?1==var With
     | [?1== ?1] -> true
     | _ -> (MemAssoc var ?2)).

Recursive Tactic Definition SeekVarAux FT lvar trm :=
  Let AT     = Eval Compute in (A FT)
  And AzeroT = Eval Compute in (Azero FT)
  And AoneT  = Eval Compute in (Aone FT)
  And AplusT = Eval Compute in (Aplus FT)
  And AmultT = Eval Compute in (Amult FT)
  And AoppT  = Eval Compute in (Aopp FT)
  And AinvT  = Eval Compute in (Ainv FT) In
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
    | [(false)] -> '(cons AT ?1 lvar).

Tactic Definition SeekVar FT trm :=
  Let AT = Eval Compute in (A FT) In
  (SeekVarAux FT '(nil AT) trm).

Recursive Tactic Definition NumberAux lvar cpt :=
  Match lvar With
  | [(nil ?1)] -> '(nil (Sprod ?1 nat))
  | [(cons ?1 ?2 ?3)] ->
    Let l2 = (NumberAux ?3 '(S cpt)) In
    '(cons (Sprod ?1 nat) (Spair ?1 nat ?2 cpt) l2).

Tactic Definition Number lvar := (NumberAux lvar O).

Tactic Definition BuildVarList FT trm :=
  Let lvar = (SeekVar FT trm) In
  (Number lvar).

Recursive Tactic Definition Assoc elt lst :=
  Match lst With
  | [(nil ?)] -> Fail
  | [(cons (Sprod ? nat) (Spair ? nat ?1 ?2) ?3)] ->
    Match elt== ?1 With
    | [?1== ?1] -> ?2
    | _ -> (Assoc elt ?3).

Recursive Tactic Definition interp_A FT lvar trm :=
  Let AT     = Eval Compute in (A FT)
  And AzeroT = Eval Compute in (Azero FT)
  And AoneT  = Eval Compute in (Aone FT)
  And AplusT = Eval Compute in (Aplus FT)
  And AmultT = Eval Compute in (Amult FT)
  And AoppT  = Eval Compute in (Aopp FT)
  And AinvT  = Eval Compute in (Ainv FT) In
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
  | [(nil ?)] -> l
  | [(cons ?1 e ?2)] -> ?2
  | [(cons ?1 ?2 ?3)] ->
    Let nl = (Remove e ?3) In
    '(cons ?1 ?2 nl).

Recursive Tactic Definition Union l1 l2 :=
  Match l1 With
  | [(nil ?)] -> l2
  | [(cons ?1 ?2 ?3)] ->
    Let nl2 = (Remove ?2 l2) In
    Let nl = (Union ?3 nl2) In
    '(cons ?1 ?2 nl).

Recursive Tactic Definition RawGiveMult trm :=
  Match trm With
  | [(EAinv ?1)] -> '(cons ExprA ?1 (nil ExprA))
  | [(EAopp ?1)] -> (RawGiveMult ?1)
  | [(EAplus ?1 ?2)] ->
    Let l1 = (RawGiveMult ?1)
    And l2 = (RawGiveMult ?2) In
    (Union l1 l2)
  | [(EAmult ?1 ?2)] ->
    Let l1 = (RawGiveMult ?1)
    And l2 = (RawGiveMult ?2) In
    Eval Compute in (app ExprA l1 l2)
  | _ -> '(nil ExprA).

Tactic Definition GiveMult trm :=
  Let ltrm = (RawGiveMult trm) In
  '(mult_of_list ltrm).

(**** Associativity ****)

Tactic Definition ApplyAssoc FT lvar trm :=
  Cut (interp_ExprA FT lvar (assoc trm))==(interp_ExprA FT lvar trm);
  [Intro;
   (Match Context With
    | [id:(interp_ExprA ?1 ?2 (assoc ?3))== ?4 |- ?] ->
      Let t=Eval Compute in (assoc ?3) In
      Change (interp_ExprA ?1 ?2 t)== ?4 in id;Try (Rewrite <- id);Clear id)
  |Apply assoc_correct].

(**** Distribution *****)

Tactic Definition ApplyDistrib FT lvar trm :=
  Cut (interp_ExprA FT lvar (distrib trm))==(interp_ExprA FT lvar trm);
  [Intro;
   (Match Context With
    | [id:(interp_ExprA ?1 ?2 (distrib ?3))== ?4 |- ?] ->
      Let t=Eval Compute in (distrib ?3) In
      Change (interp_ExprA ?1 ?2 t)== ?4 in id;Try (Rewrite <- id);Clear id)
  |Apply distrib_correct].

(**** Multiplication by the inverse product ****)

Tactic Definition GrepMult :=
  Match Context With
    | [ id: ~(interp_ExprA ? ? ?)== ? |- ?] -> id.

Tactic Definition Multiply mul :=
  Match Context With
  | [|-(interp_ExprA ?1 ?2 ?3)==(interp_ExprA ?1 ?2 ?4)] ->
    Let AzeroT = Eval Compute in (Azero ?1) In
    Cut ~(interp_ExprA ?1 ?2 mul)==AzeroT;
    [Intro;
     Let id = GrepMult In
     Apply (mult_eq ?1 ?3 ?4 mul ?2 id)(*;
     Cbv Beta Delta -[interp_ExprA] Zeta Iota*)
    |Cbv Beta Delta -[not] Zeta Iota;
     Let AmultT = Eval Compute in (Amult ?1)
     And AoneT = Eval Compute in (Aone ?1) In
     (Match Context With
      | [|-[(AmultT ? AoneT)]] -> Rewrite (AmultT_1r ?1));Clear ?1 ?2].

Tactic Definition ApplyMultiply FT lvar trm :=
  Cut (interp_ExprA FT lvar (multiply trm))==(interp_ExprA FT lvar trm);
  [Intro;
   (Match Context With
    | [id:(interp_ExprA ?1 ?2 (multiply ?3))== ?4 |- ?] ->
      Let t=Eval Compute in (multiply ?3) In
      Change (interp_ExprA ?1 ?2 t)== ?4 in id;Try (Rewrite <- id);Clear id)
  |Apply multiply_correct].

(**** Permutations and simplification ****)

Tactic Definition ApplyInverse mul FT lvar trm :=
  Cut (interp_ExprA FT lvar (inverse_simplif mul trm))==
      (interp_ExprA FT lvar trm);
  [Intro;
   (Match Context With
   | [id:(interp_ExprA ?1 ?2 (inverse_simplif ?3 ?4))== ?5 |- ?] ->
     Let t=Eval Compute in (inverse_simplif ?3 ?4) In
      Change (interp_ExprA ?1 ?2 t)== ?5 in id;Try (Rewrite <- id);Clear id)
  |Apply inverse_correct;Assumption].

(**** Inverse test ****)

Tactic Definition StrongFail tac := First [tac|Fail 2].

Tactic Definition InverseTestAux FT trm :=
  Let AplusT = Eval Compute in (Aplus FT)
  And AmultT = Eval Compute in (Amult FT)
  And AoppT  = Eval Compute in (Aopp FT)
  And AinvT  = Eval Compute in (Ainv FT) In
  Match trm With
  | [(AinvT ?)] -> Fail 1
  | [(AoppT ?1)] -> StrongFail (InverseTestAux FT ?1)
  | [(AplusT ?1 ?2)] ->
    StrongFail ((InverseTestAux FT ?1);(InverseTestAux FT ?2))
  | [(AmultT ?1 ?2)] ->
    StrongFail ((InverseTestAux FT ?1);(InverseTestAux FT ?2))
  | _ -> Idtac.

Tactic Definition InverseTest FT :=
  Let AplusT = Eval Compute in (Aplus FT) In
  Match Context With
  | [|- ?1==?2] -> (InverseTestAux FT '(AplusT ?1 ?2)).

(**** Field itself ****)

Tactic Definition ApplySimplif sfun :=
  (Match Context With
   | [|- (interp_ExprA ?1 ?2 ?3)==(interp_ExprA ? ? ?)] ->
     (sfun ?1 ?2 ?3));
  (Match Context With
   | [|- (interp_ExprA ? ? ?)==(interp_ExprA ?1 ?2 ?3)] ->
     (sfun ?1 ?2 ?3)).

Tactic Definition Unfolds FT :=
  (Match Eval Cbv Beta Delta [Aminus] Iota in (Aminus FT) With
   | [(Some ? ?1)] -> Unfold ?1
   | _ -> Idtac);
  (Match Eval Cbv Beta Delta [Adiv] Iota in (Adiv FT) With
   | [(Some ? ?1)] -> Unfold ?1
   | _ -> Idtac).

Tactic Definition Field_Gen FT :=
  Let AplusT = Eval Compute in (Aplus FT) In
  Unfolds FT;
  Match Context With
  | [|- ?1==?2] ->
    Let lvar = (BuildVarList FT '(AplusT ?1 ?2)) In
    Let trm1 = (interp_A FT lvar ?1)
    And trm2 = (interp_A FT lvar ?2) In
    Let mul = (GiveMult '(EAplus trm1 trm2)) In
    Cut [ft:=FT][vm:=lvar](interp_ExprA ft vm trm1)==(interp_ExprA ft vm trm2);
    [Compute;Auto
    |Intros;(ApplySimplif ApplyDistrib);(ApplySimplif ApplyAssoc);
     (Multiply mul);[(ApplySimplif ApplyMultiply);
       (ApplySimplif (ApplyInverse mul));
       (Let id = GrepMult In Clear id);Compute;
       First [(InverseTest FT);Ring|Clear ft vm;(Field_Gen FT)]|Idtac]].
