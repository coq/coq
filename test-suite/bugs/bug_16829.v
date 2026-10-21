From Corelib Require Import PrimInt63.

Open Scope uint63_scope.

Primitive array := #array_type.

Primitive make : forall A, int -> A -> array A := #array_make.
Arguments make {_} _ _.

Primitive get : forall A, array A -> int -> A := #array_get.
Arguments get {_} _ _.

Notation "t .[ i ]" := (get t i)
  (at level 2, left associativity, format "t .[ i ]").

Primitive set : forall A, array A -> int -> A -> array A := #array_set.
Arguments set {_} _ _ _.

Notation "t .[ i <- a ]" := (set t i a)
  (at level 2, left associativity, format "t .[ i <- a ]").

Module Inconsistent.
  Definition P a := 0 = get (get a 1) 0.
  Definition H : P [|[|0|0|]; [|0|0|] |[| |0|]|] := eq_refl.
  Fail Definition bad : P (let m := [| [|0|0|]; [|0|0|] |[| |0|]|] in set (set m 0 (get m 0)) 1 [| 1 |0|]) := H.
  (* Goal False. *)
  (*   enough (eqb 1 0 = eqb 0 0) by (cbv in *; congruence). *)
  (*   rewrite bad; reflexivity. *)
  (* Qed. *)

  Inductive CMP (x:array (unit -> nat)) := C.

  Definition F (x:nat) := fun _:unit => x.

  Definition TARGET := let m := [| F 0; F 0 | F 0 |] in
                       let m := set m 0 (fun _ => get (set m 1 (F 1)) 0 tt) in
                       CMP m.

  Definition EVALED := Eval cbv in TARGET.

  Check C [| F 0; F 0 | F 0 |] : EVALED.
  Check C [| F 0; F 0 | F 0 |] <: EVALED.
  Check C [| F 0; F 0 | F 0 |] <<: EVALED.

  Fail Check C [| F 0; F 1 | F 0 |] : TARGET.
  Fail Check C [| F 0; F 1 | F 0 |] <: TARGET.
  Fail Check C [| F 0; F 1 | F 0 |] <<: TARGET.
End Inconsistent.

Module ShouldWork.

  Definition mem := array (array int).
  Definition SCM  := (mem -> mem) -> mem.
  Definition run  : SCM -> mem                 := fun s     => s (fun x => x).
  Definition ret  : mem -> SCM                 := fun x k   => k x.
  Definition bind : SCM -> (mem -> SCM) -> SCM := fun s f k => s (fun m => f m k).

  Definition m := (make 2 (A:=array int) (make 0 (A:=int) 0))
                  .[0 <- (make 2 (A:=int) 0).[0<-20] ]
                  .[1 <- (make 2 (A:=int) 0).[0<-30].[1<-31] ].

  Definition m_expected := (make 2 (A:=array int) (make 0 (A:=int) 0))
                           .[0 <- (make 2 (A:=int) 0).[0<-200] ]
                           .[1 <- (make 2 (A:=int) 0).[0<-30].[1<-300] ].

  Definition assign_instr :=
    bind
      (bind (ret m) (fun m => ret (m.[0 <- m.[0].[0 <- 200]])))
      (fun m_inter => bind (ret m_inter) (fun m => ret (m.[1 <- m.[1].[1 <- 300]]))).

  Lemma test2 : run assign_instr = m_expected.
  Proof.
    cbv. reflexivity.
  Qed.

End ShouldWork.

Definition bad_norm :=
  let m := make 2 (make 1 false) in
  m.[1 <- m.[1].[0 <- true]].[0 <- m.[0]].

Goal True.
  let x := eval lazy in bad_norm in
    constr_eq x [| [| false | false : bool |]; [| true | false : bool |] | [| false | false : bool |] : array bool |].
Abort.
