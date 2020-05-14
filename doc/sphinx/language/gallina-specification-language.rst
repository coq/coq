.. index::
   single: ... : ... (type cast)
   single: ... <: ...
   single: ... <<: ...

Type cast
---------

.. insertprodn term_cast term_cast

.. prodn::
   term_cast ::= @term10 <: @term
   | @term10 <<: @term
   | @term10 : @term
   | @term10 :>

The expression :n:`@term : @type` is a type cast expression. It enforces
the type of :n:`@term` to be :n:`@type`.

:n:`@term <: @type` locally sets up the virtual machine for checking that
:n:`@term` has type :n:`@type`.

:n:`@term <<: @type` uses native compilation for checking that :n:`@term`
has type :n:`@type`.
