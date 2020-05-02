Require Import ssreflect.

Inductive lit : Set :=
| LitP : lit
| LitL : lit
.

Inductive val : Set :=
| Val : lit -> val.

Definition tyref :=
fun (vl : list val) =>
match vl with
| cons (Val LitL) (cons (Val LitP) _)  => False
| _ => False
end.

(** Check that simplification and resolution are performed in the right order
    by "//=" when several goals are under focus. *)
Goal exists vl1 : list val,
  cons (Val LitL) (cons (Val LitL) nil) = vl1 /\
  (tyref vl1)
.
Proof.
eexists (cons _ (cons _ _)).
split =>//=.
Fail progress simpl.
Abort.
