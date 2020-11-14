- **Changed:**
  :term:`Boolean attributes <boolean attribute>` are now specified using
  key/value pairs, that is to say :n:`@ident__attr{? = {| yes | no } }`.
  If the value is missing, the default is :n:`yes`.  The old syntax is still
  supported, but produces the ``deprecated-attribute-syntax`` warning.

  Deprecated attributes are :attr:`universes(monomorphic)`,
  :attr:`universes(notemplate)` and :attr:`universes(noncumulative)`, which are
  respectively replaced by :attr:`universes(polymorphic=no) <universes(polymorphic)>`,
  :attr:`universes(template=no) <universes(template)>`
  and :attr:`universes(cumulative=no) <universes(cumulative)>`.
  Attributes :attr:`program` and :attr:`canonical` are also affected,
  with the syntax :n:`@ident__attr(false)` being deprecated in favor of
  :n:`@ident__attr=no`.

  (`#13312 <https://github.com/coq/coq/pull/13312>`_,
  by Emilio Jesus Gallego Arias).
