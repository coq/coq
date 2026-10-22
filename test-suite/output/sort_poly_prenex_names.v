Fail Definition foo@{SProp;} := True.

Fail Definition foo@{Prop;} := True.

Fail Definition foo@{Type;} := True.

Sort Exc.

Fail Definition foo@{Exc;} := True.
