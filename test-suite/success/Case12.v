(* This example was proposed by Cuihtlauac ALVARADO *)

Require PolyList.

Fixpoint mult2 [n:nat] : nat :=
Cases n of
| O => O
| (S n) => (S (S (mult2 n)))
end.

Inductive list : nat -> Set :=
| nil : (list O)
| cons : (n:nat)(list (mult2 n))->(list (S (S (mult2 n)))).

Type
[P:((n:nat)(list n)->Prop);
 f:(P O nil);
 f0:((n:nat; l:(list (mult2 n)))
      (P (mult2 n) l)->(P (S (S (mult2 n))) (cons n l)))]
 Fix F
   {F [n:nat; l:(list n)] : (P n l) :=
      <P>Cases l of
        nil => f
      | (cons n0 l0) => (f0 n0 l0 (F (mult2 n0) l0))
      end}.

Inductive list' : nat -> Set :=
| nil' : (list' O)
| cons' : (n:nat)[m:=(mult2 n)](list' m)->(list' (S (S m))).

Fixpoint length [n; l:(list' n)] : nat :=
  Cases l of
     nil' => O
  | (cons' _ m l0) => (S (length m l0))
  end.

Type
[P:((n:nat)(list' n)->Prop);
 f:(P O nil');
 f0:((n:nat)
      [m:=(mult2 n)](l:(list' m))(P m l)->(P (S (S m)) (cons' n l)))]
 Fix F
   {F [n:nat; l:(list' n)] : (P n l) :=
      <P>
        Cases l of
          nil' => f
        | (cons' n0 m l0) => (f0 n0 l0 (F m l0))
        end}.

