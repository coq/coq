Set Primitive Projections.

CoInductive R := mkR { p : unit }.

CoFixpoint foo := mkR tt.

Check (eq_refl tt : p foo = tt).
Check (eq_refl tt <: p foo = tt).
Check (eq_refl tt <<: p foo = tt).
