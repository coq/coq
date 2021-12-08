Set Primitive Projections.
Class Foo (F : False) := { foo : True }.
Arguments foo F {Foo}.
Print Implicit foo. (* foo : forall F : False, Foo F -> True

Argument Foo is implicit and maximally inserted *)
Check foo _. (* Toplevel input, characters 6-11:
Error: Illegal application (Non-functional construction):
The expression "foo" of type "True"
cannot be applied to the term
 "?36" : "?35" *)
