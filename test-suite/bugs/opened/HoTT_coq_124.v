Set Implicit Arguments.
Set Primitive Projections.

Polymorphic Inductive eqp A (x : A) : A -> Type := eqp_refl : eqp x x.
Monomorphic Inductive eqm A (x : A) : A -> Type := eqm_refl : eqm x x.

Polymorphic Record prodp (A B : Type) : Type := pairp { fstp : A; sndp : B }.
Monomorphic Record prodm (A B : Type) : Type := pairm { fstm : A; sndm : B }.

Check eqm_refl _ : eqm (fun x : prodm Set Set => pairm (fstm x) (sndm x)) (fun x => x). (* success *)
Check eqp_refl _ : eqp (fun x : prodm Set Set => pairm (fstm x) (sndm x)) (fun x => x). (* success *)
Check eqm_refl _ : eqm (fun x : prodp Set Set => pairp (fstp x) (sndp x)) (fun x => x). (* Error:
The term
 "eqm_refl (fun x : prodp Set Set => {| fstp := fstp x; sndp := sndp x |})"
has type
 "eqm (fun x : prodp Set Set => {| fstp := fstp x; sndp := sndp x |})
    (fun x : prodp Set Set => {| fstp := fstp x; sndp := sndp x |})"
while it is expected to have type
 "eqm (fun x : prodp Set Set => {| fstp := fstp x; sndp := sndp x |})
    (fun x : prodp Set Set => x)". *)
Check eqp_refl _ : eqp (fun x : prodp Set Set => pairp (fstp x) (sndp x)) (fun x => x). (* Error:
The term
 "eqp_refl (fun x : prodp Set Set => {| fstp := fstp x; sndp := sndp x |})"
has type
 "eqp (fun x : prodp Set Set => {| fstp := fstp x; sndp := sndp x |})
    (fun x : prodp Set Set => {| fstp := fstp x; sndp := sndp x |})"
while it is expected to have type
 "eqp (fun x : prodp Set Set => {| fstp := fstp x; sndp := sndp x |})
    (fun x : prodp Set Set => x)". *)
