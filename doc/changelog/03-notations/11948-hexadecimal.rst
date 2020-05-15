- **Added:**
  Numeral notations now parse hexadecimal constants such as ``0x2a``
  or ``0xb.2ap-2``. Parsers added for :g:`nat`, :g:`positive`, :g:`Z`,
  :g:`N`, :g:`Q`, :g:`R`, primitive integers and primitive floats
  (`#11948 <https://github.com/coq/coq/pull/11948>`_,
  by Pierre Roux).
- **Deprecated:**
  Numeral Notation on ``Decimal.uint``, ``Decimal.int`` and
  ``Decimal.decimal`` are replaced respectively by numeral notations
  on ``Numeral.uint``, ``Numeral.int`` and ``Numeral.numeral``
  (`#11948 <https://github.com/coq/coq/pull/11948>`_,
  by Pierre Roux).
