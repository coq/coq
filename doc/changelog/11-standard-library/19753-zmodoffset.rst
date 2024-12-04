- **Added:** module :g:`ZModOffset`, a theory of :g:`Z.modulo` with output
  range shifted by a constant. The main definition is :g:`Z.omodulo`, with
  :g:`Z.smodulo` capturing the special case where the offset is equal to half
  of the modulus, such as in two's-complement arithmetic
  (`#19753 <https://github.com/coq/coq/pull/19753>`_,
  by Andres Erbsen).
