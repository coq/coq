Check (match true return
    match eq_refl Type return Type with eq_refl => bool end
  with _ => true end).
Check (match true return
    match eq_refl Type with eq_refl => bool end
  with _ => true end).
