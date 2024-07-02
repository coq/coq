- **Fixed:**
  Refolding of constants marked as :g:`simpl never` in position of
  argument of a destructor in :tacn:`simpl`; note that this may
  occasionally cause some calls to :tacn:`simpl` to satisfy more
  scrupulously :g:`simpl never` and to stop reducing further in
  subterms that are *not* in position of argument of a destructor, as
  specified by :g:`simpl never`
  (`#18591 <https://github.com/coq/coq/pull/18591>`_,
  fixes `#16040 <https://github.com/coq/coq/issues/16040>`_,
  by Hugo Herbelin).
