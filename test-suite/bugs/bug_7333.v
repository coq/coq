Module Example1.

CoInductive wrap : Type :=
 | item : unit -> wrap.

Definition extract (t : wrap) : unit :=
match t with
| item x => x
end.

CoFixpoint close u : unit -> wrap :=
match u with
| tt => item
end.

Definition table : wrap := close tt tt.

Eval vm_compute in (extract table).
Eval vm_compute in (extract table).

End Example1.

Module Example2.

Set Primitive Projections.
CoInductive wrap : Type :=
 item { extract : unit }.

CoFixpoint close u : unit -> wrap :=
match u with
| tt => item
end.

Definition table : wrap := close tt tt.

Eval vm_compute in (extract table).
Eval vm_compute in (extract table).

End Example2.
