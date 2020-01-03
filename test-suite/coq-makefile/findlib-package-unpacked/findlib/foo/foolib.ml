let foo () =
  assert(Str.search_forward (Str.regexp "foo") "barfoobar" 0 = 3)
