Fail #[canonical=yes, canonical=no] Definition a := 3.

Fail #[universes(polymorphic=yes,polymorphic=no)] Definition a := 3.

Fail #[universes(polymorphic=foo)] Definition a := 3.

Fail #[universes(polymorphic(foo))] Definition a := 3.

Fail #[universes(polymorphic(foo,bar))] Definition a := 3.
