(* Tested against coq ee596bc *)
 
Set Nonrecursive Elimination Schemes.
Set Primitive Projections.
Set Universe Polymorphism.
 
Record setoid := { base : Type }.
 
Definition catdata (Obj Arr : Type) : Type := nat.
  (* [nat] can be replaced by any other type, it seems,
     without changing the error *)
 
Record cat : Type :=
  {
    obj : setoid;
    arr : Type;
    dta : catdata (base obj) arr
  }.
 
Definition bcwa (C:cat) (B:setoid) :Type := nat.
  (* As above, nothing special about [nat] here. *)
 
Record temp {C}{B} (e:bcwa C B) :=
  { fld : base (obj C) }.
 
Print temp_rect.
