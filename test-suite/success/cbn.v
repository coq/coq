(* cbn is able to refold mutual recursive calls *)

Fixpoint foo (n : nat) :=
  match n with
  | 0 => true
  | S n => g n
  end
with g (n : nat) : bool :=
  match n with
  | 0 => true
  | S n => foo n
  end.
Goal forall n, foo (S n) = g n.
  intros. cbn.
  match goal with
    |- g _ = g _ => reflexivity
  end.
Qed.

(* simpl nomatch *)

Definition thing n := match n with  0 => True | S n => False end.

Arguments thing _ / : simpl nomatch.

Goal forall x, thing x.
  intros. cbn.
  match goal with |- thing x => idtac end.
Abort.

Definition thing' n := n + n.

Arguments thing' !_ / : simpl nomatch.
Lemma bar n : thing' n = 0.
Proof.
  cbn.
  match goal with |- thing' _ = _ => idtac end.
  Arguments thing' _ / : simpl nomatch.
  cbn.
  match goal with |- _ + _ = _ => idtac end.
Abort.

Module MutualFixCoFixInSection.

Section S.
Variable p:nat.
Fixpoint f n := match n with 0 => p | S n => f n + g n end
with g n := match n with 0 => p | S n => f n + g n end.
End S.

Goal forall n, f n (S n) = g 0 (S n).
intros. cbn.
match goal with [ |- f n n + g n n = f 0 n + g 0 n ] => idtac end.
Abort.

CoInductive stream {A:Type} : Type :=
  | scons: A->stream->stream.
Definition stream_unfold {A} (s: @ stream A) := match s with
| scons a s' => (a, scons a s')
end.

Section C.
Variable (x:nat).
CoFixpoint mut_stream1 (n:nat) := scons n (mut_stream2 (n+x))
with mut_stream2 (n:nat) :=  scons n (mut_stream1  (n+x)).
End C.

Goal (forall x n, stream_unfold (mut_stream1 x n) = stream_unfold (mut_stream2 x n)).
intros. cbn.
match goal with [ |- (n, scons n (mut_stream2 x (n + x))) = (n, scons n (mut_stream1 x (n + x))) ] => idtac end.
Abort.

End MutualFixCoFixInSection.
