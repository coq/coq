#[canonical=yes, canonical=no] Definition a := 3.

#[universes(polymorphic=yes,polymorphic=no)] Definition a := 3.

#[universes(polymorphic=foo)] Definition a := 3.

#[universes(polymorphic(foo))] Definition a := 3.

#[universes(polymorphic(foo,bar))] Definition a := 3.

#[universes(polymorphic=yes, bla=bla)] Definition a := 3.
