(* ============================================== *)
(*     To test compilation of dependent case      *)
(*      Multiple Patterns                         *)
(* ============================================== *)
Inductive skel : Type :=
  | PROP : skel
  | PROD : skel -> skel -> skel.

Parameter Can : skel -> Type.
Parameter default_can : forall s : skel, Can s.


Type
  (fun s1 s2 : skel =>
   match s1, s2 return (Can s1) with
   | PROP, PROP => default_can PROP
   | s1, _ => default_can s1
   end).


Type
  (fun s1 s2 : skel =>
   match s1, s2 return (Can s1) with
   | PROP, PROP => default_can PROP
   | PROP as s, _ => default_can s
   | PROD s1 s2 as s, PROP => default_can s
   | PROD s1 s2 as s, _ => default_can s
   end).
