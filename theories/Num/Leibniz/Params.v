(*i $Id $ i*)

(*s 
  Axiomatisation of a numerical set 
  It will be instantiated by Z and R later on
  We choose to introduce many operation to allow flexibility in definition 
  ([S] is primitive in the definition of [nat] while [add] and [one] 
   are primitive in the definition 
*)

Parameter N:Type.
Parameter zero:N.
Parameter one:N.
Parameter add:N->N->N.
Parameter S:N->N.

(*s Relations, equality is defined separately *)
Parameter lt,le,gt,ge:N->N->Prop.    


