(* ============================================== *)
(*     To test compilation of dependent case      *)
(*      Multiple Patterns                         *)
(* ============================================== *)
Inductive skel: Type :=
     PROP: skel
   | PROD: skel->skel->skel.

Parameter Can : skel -> Type.
Parameter default_can : (s:skel) (Can s).


Type [s1,s2:skel]
      <[s1,_:skel](Can s1)>Cases s1 s2 of
          PROP PROP => (default_can PROP)
        | s1 _ => (default_can s1)
        end.


Type [s1,s2:skel]
<[s1:skel][_:skel](Can s1)>Cases s1 s2 of
  PROP                 PROP => (default_can PROP)
| (PROP as s)             _ => (default_can s)
| ((PROD s1 s2) as s)  PROP => (default_can s)
| ((PROD s1 s2) as s)   _   => (default_can s)
end.
