Module Sylvain_Boulme.
Module Type Essai.
Parameter T: Type.
Parameter my_eq: T -> T -> Prop.
Parameter my_eq_refl: forall (x:T), (my_eq x x).
Parameter c: T.
End Essai.

Module Type Essai2.
Declare Module M: Essai.
Parameter c2: M.T.
End Essai2.

Module Type Essai3.
Declare Module M: Essai.
Parameter c3: M.T.
End Essai3.

Module Type Lift.
Declare Module Core: Essai.
Declare Module M: Essai.
Parameter lift: Core.T -> M.T.
Parameter lift_prop:forall (x:Core.T), (Core.my_eq x Core.c)->(M.my_eq (lift x) M.c).
End Lift.

Module I2 (X:Essai) <: Essai2.
 Module Core := X.
 Module M<:Essai.
  Definition T:Type :=Prop.
  Definition my_eq:=(@eq Prop).
  Definition c:=True.
  Lemma my_eq_refl: forall (x:T), (my_eq x x).
  Proof.
    unfold my_eq; auto.
  Qed.
 End M.
 Definition c2:=False.
 Definition lift:=fun (_:Core.T) => M.c.
 Definition lift_prop: forall (x:Core.T), (Core.my_eq x Core.c)->(M.my_eq (lift x) M.c).
 Proof.
   unfold lift, M.my_eq; auto.
 Qed.
End I2.

Module I4(X:Essai3) (L: Lift with Module Core := X.M) <: Essai3 with Module
M:=L.M.
  Module M:=L.M.
  Definition c3:=(L.lift X.c3).
End I4.

Module I5(X:Essai3).
  Module Toto<:  Lift with Module Core := X.M := I2(X.M).
  Module E4<: Essai3 with Module M:=Toto.M := I4(X)(Toto).
(*
Le typage de E4 echoue avec le message
 Error: Signature components for label my_eq_refl do not match
 *)

  Module E3<: Essai3 := I4(X)(Toto).

 Definition zarb: forall (x:Toto.M.T), (Toto.M.my_eq x x) := E3.M.my_eq_refl.
End I5.
End Sylvain_Boulme.


Module Jacek.

    Module Type SIG.
    End SIG.
    Module N.
      Definition A:=Set.
    End N.
    Module Type SIG2.
      Declare Module M:SIG.
      Parameter B:Type.
    End SIG2.
    Module F(X:SIG2 with Module M:=N) (Y:SIG2 with Definition B:=X.M.A).
    End F.
End Jacek.


Module anoun.
    Module Type TITI.
    Parameter X: Set.
    End TITI.

    Module Type Ex.
    Declare Module t: TITI.
    Parameter X : t.X -> t.X -> Set.
    End Ex.

    Module unionEx(X1: Ex) (X2:Ex with Module t :=X1.t): Ex.
    Module t:=X1.t.
    Definition X :=fun (a b:t.X) => ((X1.X a b)+(X2.X a b))%type.
    End unionEx.
End anoun.
(* Le warning qui s'affiche lors de la compilation est le suivant :
    TODO:replace module after with!
    Est ce qu'il y'a qq1 qui pourrait m'aider à comprendre le probleme?!
    Je vous remercie d'avance *)
