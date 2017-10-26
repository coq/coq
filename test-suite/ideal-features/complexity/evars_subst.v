(* BZ#932 *)
(* Expected time < 1.00s *)

(* Let n be the number of let-in. The complexity comes from the fact
   that each implicit arguments of f was in a larger and larger
   context. To compute the type of "let _ := f ?Tn 0 in f ?T 0",
   "f ?Tn 0" is substituted in the type of "f ?T 0" which is ?T. This
   type is an evar instantiated on the n variables denoting the "f ?Ti 0".
   One obtain "?T[1;...;n-1;f ?Tn[1;...;n-1] 0]". To compute the
   type of "let _ := f ?Tn-1 0 in let _ := f ?Tn 0 in f ?T 0", another
   substitution is done leading to
   "?T[1;...;n-2;f ?Tn[1;...;n-2] 0;f ?Tn[1;...;n-2;f ?Tn[1;...;n-2] 0] 0]"
   and so on. At the end, we get a term of exponential size *)

(* A way to cut the complexity could have been to remove the dependency in
   anonymous variables in evars but this breaks intuitive behaviour
   (see Case15.v); another approach could be to substitute lazily
   and/or to simultaneously substitute let binders and evars *)

Variable P : Set -> Set.
Variable f : forall A : Set, A -> P A.

Time Check
  let _ := f _ 0 in
  let _ := f _ 0 in
  let _ := f _ 0 in
  let _ := f _ 0 in

  let _ := f _ 0 in
  let _ := f _ 0 in
  let _ := f _ 0 in
  let _ := f _ 0 in

  let _ := f _ 0 in
  let _ := f _ 0 in
  let _ := f _ 0 in
  let _ := f _ 0 in
  let _ := f _ 0 in

  let _ := f _ 0 in
  let _ := f _ 0 in
  let _ := f _ 0 in
  let _ := f _ 0 in
  let _ := f _ 0 in

  let _ := f _ 0 in
  let _ := f _ 0 in
  let _ := f _ 0 in
  let _ := f _ 0 in
  let _ := f _ 0 in

    f _ 0.

