Module Type Test.
  Parameter t : Type.
End Test.

Module Type Func (T:Test).
  Parameter x : Type.
End Func.

Module Shortest_path (T : Test).
Print Term Func.
End Shortest_path.
