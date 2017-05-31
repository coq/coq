Section foo.

  Variable bar : Prop.
  Variable H : bar.

  Goal bar.
    typeclasses eauto with foobar.
  Qed.

End foo.
