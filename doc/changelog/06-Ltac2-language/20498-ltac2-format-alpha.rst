- **Added:**
  format specifiers `%A` to use unthunked printers and `%m` for already-formatted messages.
  Typically, instead of `printf "foo: %a" (fun () v => print_thing v) v`
  we can now write `printf "foo: %A" print_thing v`
  or `printf "foo: %m" (print_thing v)`
  (`#20498 <https://github.com/rocq-prover/rocq/pull/20498>`_,
  by Gaëtan Gilbert).
