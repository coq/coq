- **Changed:**
  set :g:`n mod 0 = n` uniformly for :g:`nat`, :g:`N`, :g:`Z`, :g:`int63`, :g:`sint63`, :g:`int31`
  such that :g:`m = (m / n) * n + (m mod n)` holds (also for :g:`n = 0`)

  .. warning:: code that relies on :g:`n mod 0 = 0` will break;
     for compatibility with both :g:`n mod 0 = n` and :g:`n mod 0 = 0` you can use
     :g:`n mod 0 = ltac:(match eval hnf in (1 mod 0) with |0 => exact 0 |_ => exact n end)`

  (`#14086 <https://github.com/coq/coq/pull/14086>`_,
  by Andrej Dudenhefner with help of Guillaume Melquiond, Jason Gross, and Kazuhiko Sakaguchi).
