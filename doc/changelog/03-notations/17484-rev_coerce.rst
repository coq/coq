- **Added:**
  Improve printing of reverse coercions. When a term :g:`x`
  is elaborated to :g:`x'` through a reverse coercion,
  return the term :g:`reverse_coercion x' x` that is convertible
  to :g:`x'` but displayed :g:`x` thanks to the coercion
  :g:`reverse_coercion`
  (`#17484 <https://github.com/coq/coq/pull/17484>`_,
  by Pierre Roux).
