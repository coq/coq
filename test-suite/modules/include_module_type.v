Module Type type1.
  Parameter A : Prop.
End type1.

Module Type type2.
  Parameter B : Prop.
End type2.

Module Type type3 := type1 <+ type2 with Definition B := True.
Print type3.

Module Type type3''.
  Include type1 <+ type2 with Definition B := True.
End type3''.
