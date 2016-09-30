Require Import Coq.FSets.FMapPositive Coq.PArith.BinPos Coq.Lists.List.

Set Asymmetric Patterns.

Notation eta x := (fst x, snd x).

Inductive expr {var : Type} : Type :=
| Const : expr
| LetIn : expr -> (var -> expr) -> expr.

Definition Expr := forall var, @expr var.

Fixpoint count_binders (e : @expr unit) : nat :=
match e with
| LetIn _ eC => 1 + @count_binders (eC tt)
| _ => 0
end.

Definition CountBinders (e : Expr) : nat := count_binders (e _).

Class Context (Name : Type) (var : Type) :=
  { ContextT : Type;
    extendb : ContextT -> Name -> var -> ContextT;
    empty : ContextT }.
Coercion ContextT : Context >-> Sortclass.
Arguments ContextT {_ _ _}, {_ _} _.
Arguments extendb {_ _ _} _ _ _.
Arguments empty {_ _ _}.

Module Export Named.
Inductive expr Name : Type :=
| Const : expr Name
| LetIn : Name -> expr Name -> expr Name -> expr Name.
End Named.

Global Arguments Const {_}.
Global Arguments LetIn {_} _ _ _.

Definition split_onames {Name : Type} (ls : list (option Name))
  : option (Name) * list (option Name)
  := match ls with
          | cons n ls'
            => (n, ls')
          | nil => (None, nil)
     end.

Section internal.
  Context (InName OutName : Type)
          {InContext : Context InName (OutName)}
          {ReverseContext : Context OutName (InName)}
          (InName_beq : InName -> InName -> bool).

  Fixpoint register_reassign (ctxi : InContext) (ctxr : ReverseContext)
           (e : expr InName) (new_names : list (option OutName))
    : option (expr OutName)
    := match e in Named.expr _ return option (expr _) with
       | Const => Some Const
       | LetIn n ex eC
         => let '(n', new_names') := eta (split_onames new_names) in
            match n', @register_reassign ctxi ctxr ex nil with
            | Some n', Some x
              => let ctxi := @extendb _ _ _ ctxi n n' in
                 let ctxr := @extendb _ _ _ ctxr n' n in
                 option_map (LetIn n' x) (@register_reassign ctxi ctxr eC new_names')
            | None, Some x
              => let ctxi := ctxi in
                 @register_reassign ctxi ctxr eC new_names'
            | _, None => None
            end
       end.

End internal.

Global Instance pos_context (var : Type) : Context positive var
  := { ContextT := PositiveMap.t var;
       extendb ctx key v := PositiveMap.add key v ctx;
       empty := PositiveMap.empty _ }.

Global Arguments register_reassign {_ _ _ _} ctxi ctxr e _.

Section language5.
  Context (Name : Type).

  Local Notation expr := (@Top.expr Name).
  Local Notation nexpr := (@Named.expr Name).

  Fixpoint ocompile (e : expr) (ls : list (option Name)) {struct e}
    : option (nexpr)
    := match e in @Top.expr _ return option (nexpr) with
       | Top.Const => Some Named.Const
       | Top.LetIn ex eC
         => match @ocompile ex nil, split_onames ls with
            | Some x, (Some n, ls')%core
              => option_map (fun C => Named.LetIn n x C) (@ocompile (eC n) ls')
            | _, _ => None
            end
       end.

  Definition compile (e : expr) (ls : list Name) := @ocompile e (List.map (@Some _) ls).
End language5.

Global Arguments compile {_} e ls.

Fixpoint merge_liveness (ls1 ls2 : list unit) :=
  match ls1, ls2 with
  | cons x xs, cons y ys => cons tt (@merge_liveness xs ys)
  | nil, ls | ls, nil => ls
  end.

Section internal1.
  Context (Name : Type)
          (OutName : Type)
          {Context : Context Name (list unit)}.

  Definition compute_livenessf_step
             (compute_livenessf : forall (ctx : Context) (e : expr Name) (prefix : list unit), list unit)
             (ctx : Context)
             (e : expr Name) (prefix : list unit)
    : list unit
    := match e with
       | Const => prefix
       | LetIn n ex eC
         => let lx := @compute_livenessf ctx ex prefix in
            let lx := merge_liveness lx (prefix ++ repeat tt 1) in
            let ctx := @extendb _ _ _ ctx n (lx) in
            @compute_livenessf ctx eC (prefix ++ repeat tt 1)
       end.

  Fixpoint compute_liveness ctx e prefix
    := @compute_livenessf_step (@compute_liveness) ctx e prefix.

  Fixpoint insert_dead_names_gen def (ls : list unit) (lsn : list OutName)
    : list (option OutName)
    := match ls with
       | nil => nil
       | cons live xs
         => match lsn with
            | cons n lsn' => Some n :: @insert_dead_names_gen def xs lsn'
            | nil => def :: @insert_dead_names_gen def xs nil
            end
       end.
  Definition insert_dead_names def (e : expr Name)
    := insert_dead_names_gen def (compute_liveness empty e nil).
End internal1.

Global Arguments insert_dead_names {_ _ _} def e lsn.

Definition Let_In {A P} (x : A) (f : forall a : A, P a) : P x := let y := x in f y.

Section language7.
  Context {Context : Context unit (positive)}.

  Local Notation nexpr := (@Named.expr unit).

  Definition CompileAndEliminateDeadCode (e : Expr) (ls : list unit)
    : option (nexpr)
    := let e := compile (Name:=positive) (e _) (List.map Pos.of_nat (seq 1 (CountBinders e))) in
       match e with
       | Some e => Let_In (insert_dead_names None e ls) (* help vm_compute by factoring this out *)
                          (fun names => register_reassign empty empty e names)
       | None => None
       end.
End language7.

Global Arguments CompileAndEliminateDeadCode {_} e ls.

Definition ContextOn {Name1 Name2} f {var} (Ctx : Context Name1 var) : Context Name2 var
  := {| ContextT := Ctx;
        extendb ctx n v := extendb ctx (f n) v;
        empty := empty |}.

Definition Register := Datatypes.unit.

Global Instance RegisterContext {var : Type} : Context Register var
  := ContextOn (fun _ => 1%positive) (pos_context var).

Definition syntax := Named.expr Register.

Definition AssembleSyntax e ls (res := CompileAndEliminateDeadCode e ls)
  := match res return match res with None => _ | _ => _ end with
     | Some v => v
     | None => I
     end.

Definition dummy_registers (n : nat) : list Register
  := List.map (fun _ => tt) (seq 0 n).
Definition DefaultRegisters (e : Expr) : list Register
  := dummy_registers (CountBinders e).

Definition DefaultAssembleSyntax e := @AssembleSyntax e (DefaultRegisters e).

Notation "'slet' x := A 'in' b" := (Top.LetIn A (fun x => b)) (at level 200, b at level 200).
Notation "#[ var ]#" := (@Top.Const var).

Definition compiled_syntax : Expr := fun (var : Type) =>
(
  slet x1 := #[ var ]# in
  slet x1 := #[ var ]# in
  slet x1 := #[ var ]# in
  slet x1 := #[ var ]# in
  slet x1 := #[ var ]# in
  slet x1 := #[ var ]# in
  slet x1 := #[ var ]# in
  slet x1 := #[ var ]# in
  slet x1 := #[ var ]# in
  slet x1 := #[ var ]# in
  slet x1 := #[ var ]# in
  slet x1 := #[ var ]# in
  slet x1 := #[ var ]# in
  slet x1 := #[ var ]# in
  slet x1 := #[ var ]# in
  slet x1 := #[ var ]# in
  slet x1 := #[ var ]# in
 @Top.Const var).

Definition v :=
  Eval cbv [compiled_syntax] in (DefaultAssembleSyntax (compiled_syntax)).

Timeout 2 Eval vm_compute in v.
