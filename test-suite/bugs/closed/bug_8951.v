Module Type T.
  Polymorphic Parameter Inline t@{i} : Type@{i}.
End T.

Module M.
  Polymorphic Definition t@{i} := True.
End M.

Module Make (X:T).
  Include X.

End Make.

Module P := Make M.



Module Type T'.
  Polymorphic Parameter Inline t@{i | Set <= i} : Type@{i}.
End T'.

Module M'.
  Polymorphic Definition t@{i} := nat.
End M'.

Module Make' (X:T').
  Include X.

End Make'.

Module P' := Make' M'.
