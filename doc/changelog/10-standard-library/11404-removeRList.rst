- **Removed:**
  Type `RList` has been removed.  All uses have been replaced by `list R`.
  Functions from `RList` named `In`, `Rlength`, `cons_Rlist`, `app_Rlist`
  have also been removed as they are essentially the same as `In`, `length`,
  `app`, and `map` from `List`, modulo the following changes:

    - `RList.In x (RList.cons a l)` used to be convertible to
      `(x = a) \\/ RList.In x l`,
      but `List.In x (a :: l)` is convertible to
      `(a = x) \\/ List.In l`.
      The equality is reversed.
    - `app_Rlist` and `List.map` take arguments in different order.

  (`#11404 <https://github.com/coq/coq/pull/11404>`_,
  by Yves Bertot).
