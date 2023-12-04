- **Changed:**
  Declarations of the form :g:`(id := body)` in :cmd:`Context` outside a
  section in a :cmd:`Module Type` do not any more try to declare a class
  instance. Assumptions whose type is a class and declared using
  :cmd:`Context` outside a section in a :cmd:`Module Type` are now
  declared as global, instead of local
  (`#18254 <https://github.com/coq/coq/pull/18254>`_,
  by Hugo Herbelin).
