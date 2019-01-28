Module Foo.
  Module Closed.
  End Closed.
  Module Type Bar.
    Section Baz.
      (* end-of-compilation error message reports unclosed sections, blocks, and
      module types *)
