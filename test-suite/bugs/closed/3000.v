Inductive t (t':Type) : Type := A | B.
Definition d := match t with _ => 1 end. (* used to fail on list_chop *)
