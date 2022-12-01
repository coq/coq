Module X.
Inductive t : Type := .
End X.
Notation t := X.t.
About t. (* was raising an anomaly from #12324 *)
Print t.
