Attributes deprecated(since="9.0", note="use Init.Wf").

Require Export Stdlib.Init.Wf.

#[deprecated(use=Fix_F_sub, since="9.0")]
Notation Fix_F_sub := Fix_F_sub (only parsing).

#[deprecated(use=Fix_sub, since="9.0")]
Notation Fix_sub := Fix_sub (only parsing).

#[deprecated(use=Fix_F_eq, since="9.0")]
Notation Fix_F_eq := Fix_F_sub_eq (only parsing).

#[deprecated(use=Fix_F_inv, since="9.0")]
Notation Fix_F_inv := Fix_F_sub_inv (only parsing).

#[deprecated(use=Fix_eq, since="9.0")]
Notation Fix_eq := Fix_sub_eq (only parsing).

#[deprecated(use=MR, since="9.0")]
Notation MR := MR (only parsing).

#[deprecated(use=measure_wf, since="9.0")]
Notation measure_wf := measure_wf (only parsing).

#[deprecated(use=F_unfold, since="9.0")]
Notation F_unfold := F_unfold (only parsing).

#[deprecated(use=Fix_F_sub_rect, since="9.0")]
Notation Fix_F_sub_rect:= Fix_F_sub_rect(only parsing).

#[deprecated(use=eq_Fix_F_sub, since="9.0")]
Notation eq_Fix_F_sub := eq_Fix_F_sub (only parsing).

#[deprecated(use=Fix_sub_rect, since="9.0")]
Notation Fix_sub_rect:= Fix_sub_rect(only parsing).

#[deprecated(Note="Use Init.Wf.fold_sub", since="9.0")]
Ltac fold_sub := fold_sub.

Require Import FunctionalExtensionalityWf.

Module WfExtensionality.
  #[deprecated(use=fix_sub_eq_ext, since="9.0")]
  Notation fix_sub_eq_ext := fix_sub_eq_ext (only parsing).
  
  #[deprecated(Note="Use Init.Wf.fold_sub", since="9.0")]
  Ltac unfold_sub := FunctionalExtensionalityWf.unfold_sub.
End WfExtensionality.
