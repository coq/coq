
Module Type T. Parameter Inline v : Prop. End T.

Module F(A:T). End F.

Fail Include F.
