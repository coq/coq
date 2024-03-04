Record foo := { bar : nat } as id.
About bar.
Class foo' := { bar' : nat } as id'.
About bar'.
CoInductive foo'' := { bar'' : foo'' } as id''.
About bar''.
Set Primitive Projections.
Record foo''' := { bar''' : nat } as id.
Print bar'''.
