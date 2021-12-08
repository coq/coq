Require Extraction.
Set Extraction Conservative Types.

Inductive data := Data : forall (T:Type), T -> data.
Definition t_of d := match d with Data t _ => t end.
Definition v_of (d : data) := match d return t_of d with Data _ v => v end.
Extraction v_of.
