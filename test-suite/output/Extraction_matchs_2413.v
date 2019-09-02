(** Extraction : tests of optimizations of pattern matching *)

Require Coq.extraction.Extraction.

(** First, a few basic tests *)

Definition test1 b :=
 match b with
   | true => true
   | false => false
 end.

Extraction test1. (** should be seen as the identity *)

Definition test2 b :=
 match b with
   | true => false
   | false => false
 end.

Extraction test2. (** should be seen a the always-false constant function *)

Inductive hole (A:Set) : Set := Hole | Hole2.

Definition wrong_id (A B : Set) (x:hole A) : hole B :=
 match x with
  | Hole _ => @Hole _
  | Hole2 _ => @Hole2 _
 end.

Extraction wrong_id. (** should _not_ be optimized as an identity *)

Definition test3 (A:Type)(o : option A) :=
 match o with
   | Some x => Some x
   | None  => None
 end.

Extraction test3.  (** Even with type parameters, should be seen as identity *)

Inductive indu : Type := A : nat -> indu | B | C.

Definition test4 n :=
 match n with
   | A m => A (S m)
   | B => B
   | C => C
 end.

Extraction test4. (** should merge branchs B C into a x->x *)

Definition test5 n :=
 match n with
   | A m => A (S m)
   | B => B
   | C => B
 end.

Extraction test5. (** should merge branches B C into _->B *)

Inductive indu' : Type := A' : nat -> indu' | B' | C' | D' | E' | F'.

Definition test6 n :=
 match n with
   | A' m => A' (S m)
   | B' => C'
   | C' => C'
   | D' => C'
   | E' => B'
   | F' => B'
 end.

Extraction test6. (** should merge some branches into a _->C' *)

(** NB : In Coq, "| a => a"  corresponds to n, hence some "| _ -> n" are
    extracted *)

Definition test7 n :=
  match n with
    | A m => Some m
    | B => None
    | C => None
  end.

Extraction test7. (** should merge branches B,C into a _->None *)

(** Script from bug #2413 *)

Set Implicit Arguments.

Section S.

Definition message := nat.
Definition word := nat.
Definition mode := nat.
Definition opcode := nat.

Variable condition : word -> option opcode.

Section decoder_result.

 Variable inst : Type.

 Inductive decoder_result : Type :=
 | DecUndefined : decoder_result
 | DecUnpredictable : decoder_result
 | DecInst : inst -> decoder_result
 | DecError : message -> decoder_result.

End decoder_result.

Definition decode_cond_mode (mode : Type) (f : word -> decoder_result mode)
  (w : word) (inst : Type) (g : mode -> opcode -> inst) :
  decoder_result inst :=
  match condition w with
    | Some oc =>
      match f w with
        | DecInst i => DecInst (g i oc)
        | DecError _ m => @DecError inst m
        | DecUndefined _ => @DecUndefined inst
        | DecUnpredictable _ => @DecUnpredictable inst
      end
    | None => @DecUndefined inst
  end.

End S.

Extraction decode_cond_mode.
(** inner match should not be factorized with a partial x->x (different type) *)

