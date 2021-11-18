
Declare ML Module "coq-test-suite.quotation".

Definition x := foobar:{{ hello
  there
}}.

Definition y := foobar:{{ another
  multi line
  thing
}}.
Check foobar:{{ oops
 ips }} y.
