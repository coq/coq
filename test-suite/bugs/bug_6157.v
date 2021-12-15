(* Check that universe instances of refs are preserved *)

Section U.
Set Universe Polymorphism.
Definition U@{i} := Type@{i}.

Section foo.
Universe i.
Fail Check U@{i} : U@{i}.
Notation Ui := U@{i}. (* syndef path *)
Fail Check Ui : Type@{i}.
Notation "#" := U@{i}. (* non-syndef path *)
Fail Check # : Type@{i}.
End foo.
End U.
