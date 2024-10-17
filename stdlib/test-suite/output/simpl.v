(* Simpl with patterns *)

Goal forall x, 0+x = 1+x.
intro x.
simpl (_ + x).
Show.
change (0+x = 1+x).
simpl (_ + x) at 2.
Show.
change (0+x = 1+x).
simpl (0 + _).
Show.
Abort.

From Stdlib Require Import String.
Open Scope string_scope.
Module NonRecursiveDefinition.
Check "** NonRecursiveDefinition".
Open Scope bool_scope.
Eval simpl in true && true.  (* -> true *)
Eval cbn in true && true.    (* -> true *)
Eval hnf in true && true.    (* -> true *)
Arguments andb : simpl never.
Eval simpl in true && true.  (* -> true && true *)
Eval cbn in true && true.    (* -> true && true *)
Eval hnf in true && true.    (* -> true *)
End NonRecursiveDefinition.

Module RecursiveDefinition.
Check "** RecursiveDefinition".
Eval simpl in 0 + 0.  (* -> 0 *)
Eval cbn in 0 + 0.    (* -> 0 *)
Eval hnf in 0 + 0.    (* -> 0 *)
Arguments Nat.add : simpl never.
Eval simpl in 0 + 0.  (* -> 0 + 0 *)
Eval cbn in 0 + 0.    (* -> 0 + 0 *)
Eval hnf in 0 + 0.    (* -> 0 + 0 *) (* hnf modified by simpl never, bug never 2 *)
End RecursiveDefinition.

Set Printing Projections.

Module NonPrimitiveProjection.
Check "** NonPrimitiveProjection".
Module DirectTuple.
Check "DirectTuple (NonPrimitiveProjection)".
Record T := {p:nat}.
Notation TUPLE := {|p:=0|}.
Eval simpl in TUPLE.(p).  (* -> 0 *)
Eval cbn in TUPLE.(p).    (* -> 0 *)
Eval hnf in TUPLE.(p).    (* -> 0 *)
Arguments p : simpl never.
Eval simpl in TUPLE.(p).  (* -> TUPLE.(p) *)
Eval cbn in TUPLE.(p).    (* -> TUPLE.(p) *)
Eval hnf in TUPLE.(p).    (* -> 0 *)
End DirectTuple.

Module NamedTuple.
Check "NamedTuple (NonPrimitiveProjection)".
Record T := {p:nat}.
Definition a := {|p:=0|}.
Eval simpl in a.(p).  (* -> 0 *)
Eval cbn in a.(p).    (* -> 0 *)
Eval hnf in a.(p).    (* -> 0 *)
Arguments p : simpl never.
Eval simpl in a.(p).  (* -> a.(p) *)
Eval cbn in a.(p).    (* -> a.(p) *)
Eval hnf in a.(p).    (* -> 0 *)
Arguments p : simpl nomatch.
Arguments a : simpl never.
Eval simpl in a.(p).  (* -> 0 *) (* never not respected on purpose [*] *)
Eval cbn in a.(p).    (* -> a.(p) *)
Eval hnf in a.(p).    (* -> 0 *)
End NamedTuple.
(* [*] Enrico: https://github.com/coq/coq/pull/18581#issuecomment-1914325999 *)

Module DirectCoFix.
Check "DirectCoFix (NonPrimitiveProjection)".
CoInductive U := {p:U}.
Notation COFIX := (cofix a := {|p:=a|}).
Eval simpl in COFIX.(p).  (* -> COFIX *)
Eval cbn in COFIX.(p).    (* -> COFIX *)
Eval hnf in COFIX.(p).    (* -> COFIX *)
Arguments p : simpl never.
Eval simpl in COFIX.(p).  (* -> COFIX.(p) *)
Eval cbn in COFIX.(p).    (* -> COFIX.(p) *)
Eval hnf in COFIX.(p).    (* -> COFIX *)
End DirectCoFix.

Module NamedCoFix.
Check "NamedCoFix (NonPrimitiveProjection)".
CoInductive U := {p:U}.
CoFixpoint a := {|p:=a|}.
Eval simpl in a.(p).  (* -> a *)
Eval cbn in a.(p).    (* -> a *)
Eval hnf in a.(p).    (* -> a *)
Arguments p : simpl never.
Eval simpl in a.(p).  (* -> a.(p) *)
Eval cbn in a.(p).    (* -> a.(p) *)
Eval hnf in a.(p).    (* -> a *)
Arguments p : simpl nomatch.
Arguments a : simpl never.
Eval simpl in a.(p).  (* -> a *) (* never not respected on purpose *)
Eval cbn in a.(p).    (* -> a.(p) *)
Eval hnf in a.(p).    (* -> a *)
End NamedCoFix.
End NonPrimitiveProjection.

Module PrimitiveProjectionFolded.
Check "** PrimitiveProjectionFolded".
Set Primitive Projections.

Module DirectTuple.
Check "DirectTuple (PrimitiveProjectionFolded)".
Record T := {p:nat}.
Notation TUPLE := {|p:=0|}.
Eval simpl in TUPLE.(p).  (* -> 0 *)
Eval cbn in TUPLE.(p).    (* -> 0 *)
Eval hnf in TUPLE.(p).    (* -> 0 *)
Arguments p : simpl never.
Eval simpl in TUPLE.(p).  (* -> TUPLE.(p) *)
Eval cbn in TUPLE.(p).    (* -> TUPLE.(p) *)
Eval hnf in TUPLE.(p).    (* -> 0 *)
End DirectTuple.

Module NamedTuple.
Check "NamedTuple (PrimitiveProjectionFolded)".
Record T := {p:nat}.
Definition a := {|p:=0|}.
Eval simpl in a.(p).  (* -> 0 *)
Eval cbn in a.(p).    (* -> 0 *)
Eval hnf in a.(p).    (* -> 0 *)
Arguments p : simpl never.
Eval simpl in a.(p).  (* -> a.(p) *)
Eval cbn in a.(p).    (* -> a.(p) *)
Eval hnf in a.(p).    (* -> 0 *)
Arguments p : simpl nomatch.
Arguments a : simpl never.
Eval simpl in a.(p).  (* -> ) *) (* never not respected on purpose *)
Eval cbn in a.(p).    (* -> a.(p) *)
Eval hnf in a.(p).    (* -> 0 *)
End NamedTuple.

Module DirectCoFix.
Check "DirectCoFix (PrimitiveProjectionFolded)".
CoInductive U := {p:U}.
Notation COFIX := (cofix a := {|p:=a|}).
Eval simpl in COFIX.(p).  (* -> COFIX *)
Eval cbn in COFIX.(p).    (* -> COFIX *)
Eval hnf in COFIX.(p).    (* -> COFIX *)
Arguments p : simpl never.
Eval simpl in COFIX.(p).  (* -> COFIX.(p) *)
Eval cbn in COFIX.(p).    (* -> COFIX.(p) *)
Eval hnf in COFIX.(p).    (* -> COFIX *)
End DirectCoFix.

Module NamedCoFix.
Check "NamedCoFix (PrimitiveProjectionFolded)".
CoInductive U := {p:U}.
CoFixpoint a := {|p:=a|}.
Eval simpl in a.(p).     (* -> a *)
Eval cbn in a.(p).       (* -> a *)
Eval hnf in a.(p).       (* -> a *)
Arguments p : simpl never.
Eval simpl in a.(p).     (* -> a.(p) *)
Eval cbn in a.(p).       (* -> a.(p) *)
Eval hnf in a.(p).       (* -> a *)
Arguments p : simpl nomatch.
Arguments a : simpl never.
Eval simpl in a.(p).     (* -> a *) (* never not respected on purpose *)
Eval cbn in a.(p).       (* -> a.(p) *)
Eval hnf in a.(p).       (* -> a *)
End NamedCoFix.
End PrimitiveProjectionFolded.

Module PrimitiveProjectionUnfolded.
Check "** PrimitiveProjectionUnfolded".
(* we use an unfold trick to create an unfolded projection *)
Set Primitive Projections.

Module DirectTuple.
Check "DirectTuple (PrimitiveProjectionUnfolded)".
Record T := {p:nat}.
Definition a := {|p:=0|}.
Axiom P : nat -> Prop.
Goal P a.(p). unfold p. cbv delta [a]. simpl. Show. Abort. (* -> 0 *)
Goal P a.(p). unfold p. cbv delta [a]. cbn. Show. Abort.   (* -> 0 *)
Goal P a.(p). unfold p. cbv delta [a]. hnf. Show. Abort.   (* -> 0 *)
Arguments p : simpl never.
Goal P a.(p). unfold p. cbv delta [a]. simpl. Show. Abort. (* -> 0 *) (* bug never 3 *)
Goal P a.(p). unfold p. cbv delta [a]. cbn. Show. Abort.   (* -> {| p := 0 |}.(p) *)
Goal P a.(p). unfold p. cbv delta [a]. hnf. Show. Abort.   (* -> 0 *)
End DirectTuple.

Module NamedTuple.
Check "NamedTuple (PrimitiveProjectionUnfolded)".
Record T := {p:nat}.
Definition a := {|p:=0|}.
Axiom P : nat -> Prop.
Goal P a.(p). unfold p. simpl. Show. Abort. (* -> 0 *)
Goal P a.(p). unfold p. cbn. Show. Abort.   (* -> 0 *)
Goal P a.(p). unfold p. hnf. Show. Abort.   (* -> a.(p) *) (* bug primproj 2 *)
Arguments p : simpl never.
Goal P a.(p). unfold p. simpl. Show. Abort. (* -> 0 *)     (* bug never 3 *)
Goal P a.(p). unfold p. cbn. Show. Abort.   (* -> a.(p) *)
Goal P a.(p). unfold p. hnf. Show. Abort.   (* -> a.(p) *) (* bug primproj 2 *)
Arguments p : simpl nomatch.
Arguments a : simpl never.
Goal P a.(p). unfold p. simpl. Show. Abort.  (* -> 0 *)     (* bug never 1 *)
Goal P a.(p). unfold p. cbn. Show. Abort.    (* -> a.(p) *)
Goal P a.(p). unfold p. hnf. Show. Abort.    (* -> a.(p) *) (* bug primproj 2 *)
End NamedTuple.

Module DirectCoFix.
Check "DirectCoFix (PrimitiveProjectionUnfolded)".
CoInductive U := {q:U}.
CoFixpoint a := {|q:=a|}.
Notation COFIX := (cofix a := {|q:=a|}).
Axiom P : U -> Prop.
Goal P a.(q). unfold q. cbv delta [a]. simpl. Show. Abort. (* -> COFIX *)
Goal P a.(q). unfold q. cbv delta [a]. cbn. Show. Abort.   (* -> COFIX *)
Goal P a.(q). unfold q. cbv delta [a]. hnf. Show. Abort.   (* -> COFIX *)
Arguments q : simpl never.
Goal P a.(q). unfold q. cbv delta [a]. simpl. Show. Abort. (* -> COFIX *) (* never not respected on purpose *)
Goal P a.(q). unfold q. cbv delta [a]. cbn. Show. Abort.   (* -> COFIX.(q) *)
Goal P a.(q). unfold q. cbv delta [a]. hnf. Show. Abort.   (* -> COFIX *)
End DirectCoFix.

Module NamedCoFix.
Check "NamedCoFix (PrimitiveProjectionUnfolded)".
CoInductive U := {q:U}.
CoFixpoint a := {|q:=a|}.
Notation COFIX := (cofix a := {|q:=a|}).
Axiom P : U -> Prop.
Goal P a.(q). unfold q. simpl. Show. Abort.  (* -> a *)
Goal P a.(q). unfold q. cbn. Show. Abort.    (* -> a *)
Goal P a.(q). unfold q. hnf. Show. Abort.    (* -> a.(q) *) (* bug primproj 4 *)
Arguments q : simpl never.
Goal P a.(q). unfold q. simpl. Show. Abort.  (* -> a *)
Goal P a.(q). unfold q. cbn. Show. Abort.    (* -> a.(q) *)
Goal P a.(q). unfold q. hnf. Show. Abort.    (* -> a.(q) *) (* bug primproj 4 *)
Arguments q : simpl nomatch.
Arguments a : simpl never.
Goal P a.(q). unfold q. simpl. Show. Abort.  (* -> a *)
Goal P a.(q). unfold q. cbn. Show. Abort.    (* -> a.(q) *)
Goal P a.(q). unfold q. hnf. Show. Abort.    (* -> a.(q) *) (* bug primproj 4 *)
End NamedCoFix.
End PrimitiveProjectionUnfolded.

Module PrimitiveProjectionConstant.
Check "** PrimitiveProjectionConstant".
(* we use a partial application to create a projection constant *)
Set Primitive Projections.

Module DirectTuple.
Check "DirectTuple (PrimitiveProjectionConstant)".
Record T := {p:nat}.
Notation TUPLE := {|p:=0|}.
Definition a := {|p:=0|}.
Axiom P : nat -> Prop.
Goal P (id p a). unfold id. cbv delta [a]. simpl. Show. Abort. (* -> 0 *)
Goal P (id p a). unfold id. cbv delta [a]. cbn. Show. Abort.   (* -> 0 *)
Goal P (id p a). unfold id. cbv delta [a]. hnf. Show. Abort.   (* -> TUPLE.(p) *) (* bug primproj 1 *)
Arguments p : simpl never.
Goal P (id p a). unfold id. cbv delta [a]. simpl. Show. Abort. (* -> TUPLE.(p) *)
Goal P (id p a). unfold id. cbv delta [a]. cbn. Show. Abort.   (* -> TUPLE.(p) *)
Goal P (id p a). unfold id. cbv delta [a]. hnf. Show. Abort.   (* -> TUPLE.(p) *) (* bug primproj 1 *)
End DirectTuple.

Module NamedTuple.
Check "NamedTuple (PrimitiveProjectionConstant)".
Record T := {p:nat}.
Definition a := {|p:=0|}.
Axiom P : nat -> Prop.
Goal P (id p a). unfold id. simpl. Show. Abort. (* -> 0 *)
Goal P (id p a). unfold id. cbn. Show. Abort.   (* -> 0 *)
Goal P (id p a). unfold id. hnf. Show. Abort.   (* -> a.(p) *) (* bug primproj 2 *)
Arguments p : simpl never.
Goal P (id p a). unfold id. simpl. Show. Abort. (* -> a.(p) *)
Goal P (id p a). unfold id. cbn. Show. Abort.   (* -> a.(p) *)
Goal P (id p a). unfold id. hnf. Show. Abort.   (* -> a.(p) *) (* bug primproj 2 *)
Arguments p : simpl nomatch.
Arguments a : simpl never.
Goal P (id p a). unfold id. simpl. Show. Abort.  (* -> 0 *) (* never not respected on purpose *)
Goal P (id p a). unfold id. cbn. Show. Abort.    (* -> a.(p) *)
Goal P (id p a). unfold id. hnf. Show. Abort.    (* -> a.(p) *)
End NamedTuple.

Module DirectCoFix.
Check "DirectCoFix (PrimitiveProjectionConstant)".
CoInductive U := {q:U}.
Notation COFIX := (cofix a := {|q:=a|}).
Axiom P : U -> Prop.
Goal P (id q COFIX). unfold id. simpl. Show. Abort.  (* -> COFIX *)
Goal P (id q COFIX). unfold id. cbn. Show. Abort.    (* -> COFIX *)
Goal P (id q COFIX). unfold id. hnf. Show. Abort.    (* -> COFIX.(q) *) (* bug primproj 3 *)
Arguments q : simpl never.
Goal P (id q COFIX). unfold id. simpl. Show. Abort.  (* -> COFIX.(q) *)
Goal P (id q COFIX). unfold id. cbn. Show. Abort.    (* -> COFIX.(q) *)
Goal P (id q COFIX). unfold id. hnf. Show. Abort.    (* -> COFIX.(q) *) (* bug primproj 3 *)
End DirectCoFix.

Module NamedCoFix.
Check "NamedCoFix (PrimitiveProjectionConstant)".
CoInductive U := {q:U}.
CoFixpoint a := {|q:=a|}.
Axiom P : U -> Prop.
Goal P (id q a). unfold id. simpl. Show. Abort.  (* -> a *)
Goal P (id q a). unfold id. cbn. Show. Abort.    (* -> a *)
Goal P (id q a). unfold id. hnf. Show. Abort.    (* -> a.(q) *) (* bug primproj 4 *)
Arguments q : simpl never.
Goal P (id q a). unfold id. simpl. Show. Abort.  (* -> a.(q) *)
Goal P (id q a). unfold id. cbn. Show. Abort.    (* -> a.(q) *)
Goal P (id q a). unfold id. hnf. Show. Abort.    (* -> a.(q) *) (* bug primproj 4 *)
Arguments q : simpl nomatch.
Arguments a : simpl never.
Goal P (id q a). unfold id. simpl. Show. Abort.  (* -> a *) (* never not respected on purpose *)
Goal P (id q a). unfold id. cbn. Show. Abort.    (* -> a.(q) *)
Goal P (id q a). unfold id. hnf. Show. Abort.    (* -> a.(q) *) (* bug primproj 4 *)
End NamedCoFix.
End PrimitiveProjectionConstant.
