
Module M.

  Export Set Universe Polymorphism.
  Definition foo := Type.

End M.

Module N.

  Definition bar := Type. Fail Check bar@{_}.

  Import M.
  Definition baz := Type. Check baz@{_}.
End N.

Module Z.
  Import(fake) M.
  Definition bar := Type. Fail Check bar@{_}.

  Import(options) M.
  Definition baz := Type. Check baz@{_}.
End Z.
