(* Check if omission of "as" in return clause works w/ section variables too *)

Section sec.

Variable b: bool.

Definition d' :=
  (match b return b = true \/ b = false with
  | true => or_introl _ (refl_equal true)
  | false => or_intror _ (refl_equal false)
  end).
