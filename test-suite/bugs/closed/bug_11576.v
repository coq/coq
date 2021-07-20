Global Set Asymmetric Patterns.
Inductive type := base | arrow (s d : type).
Fixpoint for_each_lhs_of_arrow (f : Type) (t : type) : Type
  := match t with
     | base => unit
     | arrow s d => f * @for_each_lhs_of_arrow f d
     end.
Inductive expr {var : Type} : type -> Type :=
| Var {t} (v : var) : expr t
| Abs {s d} (f : var -> expr d) : expr (arrow s d)
.
Class parameters := {}.
Record rep {p : parameters} := {}.
Axiom listZ_local : forall {p}, @rep p.
Axiom p : parameters.
#[export] Existing Instance p.
Axiom cmd : forall {p : parameters}, Type.
Axiom ltype : forall {p : parameters} {listZ : @rep p}, Type.
Axiom translate_cmd
  : forall {p : parameters}
           (e : expr (var:=@ltype p (@listZ_local p)) base),
    cmd.
Axiom admit : forall {T}, T.
Existing Class rep.
Fixpoint translate_func' (pv:=_) {t} (e : @expr ltype t)
  : for_each_lhs_of_arrow ltype t -> @cmd pv :=
  match e with
  | Abs base d f =>
    fun (args : _ * for_each_lhs_of_arrow _ d) =>
      translate_func' (f (fst args)) (snd args)
  | Var base v =>
    fun _ => translate_cmd (Var v)
  | _ => fun _ => admit
  end.
(* Used to be: File "./bug_01.v", line 30, characters 30-31:
Error: Cannot infer this placeholder of type "parameters" (no type class
instance found).*)
