
Declare ML Module "quotation_plugin".

Definition x := foobar:{{ hello
  there
}}.

Definition y := foobar:{{ another
  multi line
  thing
}}.
Check foobar:{{ oops
 ips }} y.
