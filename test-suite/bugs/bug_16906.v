Require Import Coq.Program.Program.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope list_scope.
Program Fixpoint foo
  (_local_inst := tt) (decls : list unit) {struct decls} : list unit
  := match decls with | [] => [] | _ => [] end.
(* Was raising a Not_found *)
