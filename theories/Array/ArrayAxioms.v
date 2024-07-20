From Stdlib Require Import PrimArray.

Local Notation in_bounds i t := (PrimInt63.ltb i (length t)).

Axiom get_out_of_bounds : forall A (t:array A) i,
  in_bounds i t = false -> t.[i] = default t.

Axiom get_set_same : forall A t i (a:A),
  in_bounds i t = true -> t.[i<-a].[i] = a.
Axiom get_set_other : forall A t i j (a:A), i <> j -> t.[i<-a].[j] = t.[j].
Axiom default_set : forall A t i (a:A), default t.[i<-a] = default t.


Axiom get_make : forall A (a:A) size i, (make size a).[i] = a.

Axiom leb_length : forall A (t:array A),
  PrimInt63.leb (length t) max_length = true.

Axiom length_make : forall A size (a:A),
  length (make size a) = if PrimInt63.leb size max_length then size else max_length.
Axiom length_set : forall A t i (a:A),
  length t.[i<-a] = length t.

Axiom get_copy : forall A (t:array A) i, (copy t).[i] = t.[i].
Axiom length_copy : forall A (t:array A), length (copy t) = length t.

Axiom array_ext : forall A (t1 t2:array A),
  length t1 = length t2 ->
  (forall i, in_bounds i t1 = true -> t1.[i] = t2.[i]) ->
  default t1 = default t2 ->
  t1 = t2.
