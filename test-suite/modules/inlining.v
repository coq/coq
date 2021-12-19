Module Type T. Parameter Inline(50) t : Type. End T.

Module Type F (X : T). Parameter p : X.t. End F.

Module M. Definition t := nat. End M.

Set Inline Level 49.

Module G
  (X : F M [inline at level 49])
  (Y : F M [inline at level 50])
  (Z : F M) : F M [inline at level 50].

(* M.t should not be inlined in the type of X.p, because 49 < 50 *)
Goal X.p = X.p.
match goal with |- _ = _ :> M.t => idtac | _ => fail end.
Fail match goal with |- _ = _ :> nat => idtac | _ => fail end.
Abort.

(* M.t should be inlined in the type of Y.p, because 50 >= 50 *)
Goal Y.p = Y.p.
Fail match goal with |- _ = _ :> M.t => idtac | _ => fail end.
match goal with |- _ = _ :> nat => idtac | _ => fail end.
Abort.

(* M.t should not be inlined in the type of Z.p, because default level < 50 *)
Goal Z.p = Z.p.
match goal with |- _ = _ :> M.t => idtac | _ => fail end.
Fail match goal with |- _ = _ :> nat => idtac | _ => fail end.
Abort.

Definition p := X.p.
End G.

Module N. Definition p := 0. End N.

Module P := G N N N.

(* M.t should be inlined in the type of P.p, because 50 >= 50 *)
Goal P.p = P.p.
Fail match goal with |- _ = _ :> M.t => idtac | _ => fail end.
match goal with |- _ = _ :> nat => idtac | _ => fail end.
Abort.

Set Inline Level 50.

Module G'
  (X : F M [inline at level 49])
  (Y : F M [inline at level 50])
  (Z : F M) : F M [inline at level 49].

(* M.t should be inlined in the type of Z.p, because default level >= 50 *)
Goal Z.p = Z.p.
Fail match goal with |- _ = _ :> M.t => idtac | _ => fail end.
match goal with |- _ = _ :> nat => idtac | _ => fail end.
Abort.

Definition p := X.p.
End G'.

Module P' := G' N N N.

(* M.t should not be inlined in the type of P'.p, because 49 < 50 *)
Goal P'.p = P'.p.
match goal with |- _ = _ :> M.t => idtac | _ => fail end.
Fail match goal with |- _ = _ :> nat => idtac | _ => fail end.
Abort.

Set Inline Level 50.

Module G''
  (X : F M [inline at level 49])
  (Y : F M [inline at level 50])
  (Z : F M) : F M.
Definition p := X.p.
End G''.

Module P'' := G'' N N N.

(* M.t should not be inlined in the type of P''.p, because default level >= 50 *)
Goal P''.p = P''.p.
Fail match goal with |- _ = _ :> M.t => idtac | _ => fail end.
match goal with |- _ = _ :> nat => idtac | _ => fail end.
Abort.

Set Inline Level 49.

Module G'''
  (X : F M [inline at level 49])
  (Y : F M [inline at level 50])
  (Z : F M) : F M.
Definition p := X.p.
End G'''.

Module P''' := G''' N N N.

(* M.t should not be inlined in the type of P'.p, because default level < 50 *)
Goal P'''.p = P'''.p.
match goal with |- _ = _ :> M.t => idtac | _ => fail end.
Fail match goal with |- _ = _ :> nat => idtac | _ => fail end.
Abort.
