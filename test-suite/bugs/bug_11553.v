Definition var := nat.
Module Import A.
Class Rename (term : Type) := rename : (var -> var) -> term -> term.
End A.

Inductive tm : Type :=
  (* | tv : vl_ -> tm *)
 with vl_ : Type :=
  | var_vl : var -> vl_.

Definition vl := vl_.

Fixpoint tm_rename (sb : var -> var) (t : tm) : tm :=
  let b := vl_rename : Rename vl in
  match t with
  end
with
vl_rename (sb : var -> var) v : vl :=
  let a := tm_rename : Rename tm in
  let b := vl_rename : Rename vl in
  match v with
  | var_vl x => var_vl (sb x)
  end.

Instance rename_vl : Rename vl := vl_rename.

Lemma foo ξ x: rename_vl ξ (var_vl x) = var_vl x.
(* Succeeds *)
cbn. Abort.

Lemma foo ξ x: rename ξ (var_vl x) = var_vl x.
(* Fails *)
cbn.
Abort.
