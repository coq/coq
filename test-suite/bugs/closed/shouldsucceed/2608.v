
Module Type T.
  Parameter Inline t : Type.
End T.

Module M.
  Definition t := nat.
End M.

Module Make (X:T).
  Include X.

  (* here t is : (Top.Make.t,Top.X.t) *)

  (* in libobject HEAD : EvalConstRef (Top.X.t,Top.X.t)
     which is substituted by : {Top.X |-> Top.Make [, Top.Make.t=>Top.X.t]}
     which gives : EvalConstRef (Top.Make.t,Top.X.t) *)

End Make.

Module P := Make M.

  (* resolver returned by add_module : Top.P.t=>inline *)
  (* then constant_of_delta_kn P.t produces (Top.P.t,Top.P.t) *)

  (* in libobject HEAD : EvalConstRef (Top.Make.t,Top.X.t)
     given to subst = {<X#1> |-> Top.M [, Top.M.t=>inline]}
     which used to give : EvalConstRef (Top.Make.t,Top.M.t)
     given to subst = {Top.Make |-> Top.P [, Top.P.t=>inline]}
     which used to give : EvalConstRef (Top.P.t,Top.M.t) *)

Definition u := P.t.
 (* was raising Not_found since Heads.head_map knows of (Top.P.t,Top.M.t)
    and not of (Top.P.t,Top.P.t) *)
