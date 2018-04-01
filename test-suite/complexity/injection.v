(* This example, submitted by A. Appel, checks the efficiency of
   injection (see bug #1173) *)
(* Expected time < 1.50s *)

Set Implicit Arguments.

Record joinable (t: Type) : Type := Joinable {
   is_empty: t -> Prop;
   join: t -> t -> t -> Prop;
   join_com: forall a b c, join a b c -> join b a c;
   join_empty: forall e a b, is_empty e -> join e a b -> a=b;
   exists_empty: forall a, exists e, is_empty e /\ join e a a;
   join_empty2: forall a b c, join a b c ->  is_empty c -> is_empty a;
   join_empty3: forall e a, join e a a -> is_empty e;
   join_assoc: forall a b c d e, join a b d -> join d c e ->
                    exists f, join b c f /\ join a f e;
   join_eq: forall x y z z', join x y z -> join x y z' -> z = z';
   cancellation: forall a1 a2 b c, join a1 b c -> join a2 b c -> a1=a2
}.

Record joinmap (key: Type) (t: Type) (j : joinable t) : Type
 := Joinmap {
    jm_t : Type;
    jm_j : joinable jm_t;
    lookup: jm_t -> key -> t;
    prim : forall (f: key -> t) (e: t),
                  (forall k, j.(join) e (f k) (f k)) ->
                  jm_t;
    join_rule: forall s1 s2 s,
                jm_j.(join) s1 s2 s <->
                forall x, j.(join) (lookup s1 x) (lookup s2 x) (lookup s x);
    empty_rule: forall e x, jm_j.(is_empty) e -> j.(is_empty) (lookup e x);
    prim_rule: forall f e pf k, lookup (prim f e pf) k = f k;
    ext: forall s1 s2,
        (forall x, lookup s1 x = lookup s2 x) <-> s1 = s2;
    can_join: forall s1 s2,
            (forall x, exists v,
                j.(join) (lookup s1 x) (lookup s2 x) v) ->
            exists s3, jm_j.(join) s1 s2 s3;
    can_split: forall s1 s3,
            (forall x, exists v,
                j.(join) (lookup s1 x) v (lookup s3 x)) ->
            exists s2, jm_j.(join) s1 s2 s3
}.

Parameter mkJoinmap :   forall (key: Type) (t: Type) (j: joinable t),
joinmap key j.

Parameter ADMIT: forall p: Prop, p.
Arguments ADMIT [p].

Module Share.
Parameter jb : joinable bool.
Definition jm: joinmap nat jb := mkJoinmap nat jb.
Definition t := jm.(jm_t).
Definition j := jm.(jm_j).
Parameter nonempty: t -> Prop.
End Share.

Section Own.

Variable inv : Type.

Inductive own : Type :=
  | NO
  | VAL' : forall sh, Share.nonempty sh -> own
  | LK : forall sh, Share.nonempty sh -> Share.t -> inv -> own
  | CT : forall sh, Share.nonempty sh -> own
  | FUN: forall sh, Share.nonempty sh -> inv -> own.

Definition own_join (a b c: own) : Prop :=
 match a , b , c with
  | NO , _ , _ =>  b=c
  | _ , NO , _ =>  a=c
  | @VAL' sa _, @VAL' sb _, @VAL' sc _ => Share.j.(join) sa sb sc
  | @LK sa pa ha fa, @LK sb pb hb fb, @LK sc pc hc fc =>
      Share.j.(join) sa sb sc /\
      Share.j.(join) ha hb hc /\
      fa=fc /\
      fb=fc
  | @CT sa pa , @CT sb pb, @CT sc pc => Share.j.(join) sa sb sc
  | @FUN sa pa fa, @FUN sb pb fb, @FUN sc pc fc =>
        Share.j.(join) sa sb sc /\ fa=fc /\ fb=fc
  | _ , _ , _ => False
 end.

Definition own_is_empty (a: own) := a=NO.

Definition jown : joinable own :=
  Joinable own_is_empty own_join
     ADMIT ADMIT  ADMIT  ADMIT  ADMIT  ADMIT  ADMIT  ADMIT .
End Own.

Fixpoint sinv (n: nat) : Type :=
  match n with
   | O => unit
   | S n => prodT (sinv n) (own (sinv n) -> unit -> Prop)
 end.

Parameter address: Set.

Definition jm (n: nat) := mkJoinmap address (jown (sinv n)).

Definition worldfun (n: nat) := (jm n).(jm_t).

Inductive world : Type :=
  mk_world: forall n, worldfun n -> world.

Lemma test: forall n1 w1 n2 w2, mk_world n1 w1 = mk_world n2 w2 ->
         n1 = n2.
Proof.
intros.
Timeout 10 Time injection H.
