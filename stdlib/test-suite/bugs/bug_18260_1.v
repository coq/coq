From Stdlib.Init Require Byte.
From Stdlib.Strings Require Byte.
From Stdlib Require ZArith.

Axiom proof_admitted : False.
Tactic Notation "admit" := abstract case proof_admitted.

Import Byte.

Module Export word.
  Class word {width : BinInt.Z} := {
      rep : Type;
    }.
  Arguments word : clear implicits.

End word.
Notation word := word.word.
Global Coercion word.rep : word >-> Sortclass.



Module map.
  Class map {key value:Type} := mk {
                                    rep : Type;
                                  }.
  Arguments map : clear implicits.
  Global Coercion rep : map >-> Sortclass.

End map.
Local Notation map := map.map.
Global Coercion map.rep : map >-> Sortclass.

Definition SuchThat(R: Type)(P: R -> Prop) := R.
Existing Class SuchThat.

Notation "'annotate!' x T" := (match x return T with b => b end)
                                (at level 10, x at level 0, T at level 0, only parsing).

Notation "'infer!' P" :=
  (match _ as ResType return ResType with
   | ResType =>
       match P with
       | Fun => annotate! (annotate! _ (SuchThat ResType Fun)) ResType
       end
   end)
    (at level 0, P at level 100, only parsing).

Global Hint Extern 1 (SuchThat ?RRef ?FRef) =>
         let R := eval cbv delta [RRef] in RRef in
           let r := open_constr:(_ : R) in
           let G := eval cbv beta delta [RRef FRef] in (FRef r) in
             let t := open_constr:(ltac:(cbv beta; typeclasses eauto) : G) in
             match r with
             | ?y => exact y
             end
               : typeclass_instances.

Class Multiplication{A B R: Type}(a: A)(b: B)(r: R) := {}.
Notation "a * b" := (infer! Multiplication a b) (only parsing) : oo_scope.


Import map.

Section Sep.
  Context  {map : Type}.
  Definition sep (p q : map -> Prop) (m:map) : Prop. Admitted.

End Sep.

Import ZArith.

Section Scalars.
  Context {width : Z} {word : word width}.

  Context {mem : map.map word byte}.
  Definition scalar : word -> word -> mem -> Prop. Admitted.

End Scalars.

#[export] Instance MulSepClause{K V: Type}{M: map.map K V}(a b: @map.rep K V M -> Prop)
  : Multiplication a b (sep a b) | 10 := {}.


Class PointsTo{width: Z}{word: word.word width}{mem: map.map word Byte.byte}{V: Type}
  (addr: word)(val: V)(pred: mem -> Prop) := {}.
Global Hint Mode PointsTo + + + + + + - : typeclass_instances.

Class PointsToPredicate{width}{word: word.word width}{mem: Type}
  (V: Type)(pred: word -> V -> mem -> Prop) := {}.

#[export] Instance PointsToPredicate_to_PointsTo
  {width}{word: word.word width}{mem: map.map word Byte.byte}{V: Type}
  (pred: word -> V -> mem -> Prop){p: PointsToPredicate V pred}
  (a: word)(v: V): PointsTo a v (pred a v) := {}.

#[export] Instance PointsToScalarPredicate
  {width}{word: word.word width}{mem: map.map word Byte.byte}:
  PointsToPredicate word scalar := {}.

Section TestNotations.
  Context {width: Z} {word: word.word width} {mem: map.map word Byte.byte}.
  Local Open Scope oo_scope.
  Set Printing All.
  Typeclasses eauto := debug.
  Goal forall (a1 a2 ofs sz v1 v2: word) (R: mem -> Prop) (m: mem),
      (infer! Multiplication R (infer! PointsTo a1 v1)) m.
  Abort.
End TestNotations.
