(* -*- mode: coq; coq-prog-args: ("-emacs" "-top" "atomic" "-Q" "." "iris" "-R" "." "stdpp") -*- *)
(* File reduced by coq-bug-finder from original input, then from 140 lines to 26 lines, then from 141 lines to 27 lines, then from 142 lines to 27 lines, then from 272 lines to 61 lines, then from 291 lines to 94 lines, then from 678 lines to 142 lines, then from 418 lines to 161 lines, then from 538 lines to 189 lines, then from 840 lines to 493 lines, then from 751 lines to 567 lines, then from 913 lines to 649 lines, then from 875 lines to 666 lines, then from 784 lines to 568 lines, then from 655 lines to 173 lines, then from 317 lines to 94 lines, then from 172 lines to 86 lines, then from 102 lines to 86 lines, then from 130 lines to 86 lines, then from 332 lines to 112 lines, then from 279 lines to 111 lines, then from 3996 lines to 5697 lines, then from 153 lines to 117 lines, then from 146 lines to 108 lines, then from 124 lines to 108 lines *)
(* coqc version 8.8.0 (May 2018) compiled on May 2 2018 16:49:46 with OCaml 4.02.3
   coqtop version 8.8.0 (May 2018) *)

(* This was triggering a "Not_found" at the time of printing/showing the goal *)

Require Coq.Unicode.Utf8.

Notation "t $ r" := (t r)
  (at level 65, right associativity, only parsing).

Inductive tele : Type :=
  | TeleO : tele
  | TeleS {X} (binder : X -> tele) : tele.

Fixpoint tele_fun (TT : tele) (T : Type) : Type :=
  match TT with
  | TeleO => T
  | TeleS b => forall x, tele_fun (b x) T
  end.

Inductive tele_arg : tele -> Type :=
| TargO : tele_arg TeleO
| TargS {X} {binder} (x : X) : tele_arg (binder x) -> tele_arg (TeleS binder).

Axiom tele_app : forall {TT : tele} {T} (f : tele_fun TT T), tele_arg TT -> T.

Coercion tele_arg : tele >-> Sortclass.

Inductive val :=
  | LitV
  | PairV (v1 v2 : val)
  | InjLV (v : val)
  | InjRV (v : val).
Axiom coPset : Set.
Axiom atomic_update : forall {PROP : Type} {TA TB : tele}, coPset -> coPset -> (TA -> PROP) -> (TA -> TB -> PROP) -> (TA -> TB -> PROP) -> PROP.
Import Coq.Unicode.Utf8.
Notation "'AU' '<<' ∀ x1 .. xn , α '>>' @ Eo , Ei '<<' β , 'COMM' Φ '>>'" :=
  (atomic_update (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
                 (TB:=TeleO)
                 Eo Ei
                 (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn, α) ..)
                 (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn, tele_app (TT:=TeleO) β) .. )
                 (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn, tele_app (TT:=TeleO) Φ) .. )
  )
  (at level 20, Eo, Ei, α, β, Φ at level 200, x1 binder, xn binder,
   format "'[   ' 'AU'  '<<'  ∀  x1  ..  xn ,  α  '>>'  '/' @  Eo ,  Ei  '/' '[   ' '<<'  β ,  '/' COMM  Φ  '>>' ']' ']'") : bi_scope.

Axiom ident : Set.
Inductive env (A : Type) : Type :=  Enil : env A | Esnoc : env A → ident → A → env A.
Record envs (PROP : Type) : Type
  := Envs { env_spatial : env PROP }.
Axiom positive : Set.
Axiom Qp : Set.
Axiom one : positive.
Goal   forall (T : Type) (T0 : forall _ : T, Type) (P : Set)
    (u : T) (γs : P) (Q : T0 u) (Φ o : forall _ : val, T0 u)
    (stack_content0 : forall (_ : P) (_ : list val), T0 u)
    (c c0 : coPset) (l : forall (A : Type) (_ : list A), list A)
    (e0 : forall (_ : env (T0 u)) (_ : positive), envs (T0 u))
    (i0 : ident) (o1 : forall (_ : Qp) (_ : val), T0 u)
    (b0 : forall _ : env (T0 u), T0 u) (P0 : forall _ : T0 u, Type)
    (u0 : forall (_ : T0 u) (_ : T0 u), T0 u),
  P0
    (@atomic_update (T0 u)
       (@TeleS val (fun _ : val => @TeleS Qp (fun _ : Qp => TeleO))) TeleO c c0
       (@tele_app (@TeleS val (fun _ : val => @TeleS Qp (fun _ : Qp => TeleO)))
          (T0 u) (fun (v : val) (q : Qp) => o1 q v))
       (@tele_app (@TeleS val (fun _ : val => @TeleS Qp (fun _ : Qp => TeleO)))
          (forall _ : tele_arg TeleO, T0 u)
          (fun (v : val) (q : Qp) => @tele_app TeleO (T0 u) (o1 q v)))
       (@tele_app (@TeleS val (fun _ : val => @TeleS Qp (fun _ : Qp => TeleO)))
          (forall _ : tele_arg TeleO, T0 u)
          (fun (x : val) (_ : Qp) =>
           @tele_app TeleO (T0 u)
             (u0
                (b0
                   match
                     e0
                       (@Esnoc (T0 u) (@Enil (T0 u)) i0
                          (@atomic_update (T0 u)
                             (@TeleS (list val) (fun _ : list val => TeleO)) TeleO
                             c c0
                             (@tele_app
                                (@TeleS (list val) (fun _ : list val => TeleO))
                                (T0 u) (fun l0 : list val => stack_content0 γs l0))
                             (@tele_app
                                (@TeleS (list val) (fun _ : list val => TeleO))
                                (forall _ : tele_arg TeleO, T0 u)
                                (fun l0 : list val =>
                                 @tele_app TeleO (T0 u)
                                   (stack_content0 γs (l val l0))))
                             (@tele_app
                                (@TeleS (list val) (fun _ : list val => TeleO))
                                (forall _ : tele_arg TeleO, T0 u)
                                (fun x1 : list val =>
                                 @tele_app TeleO (T0 u)
                                   (u0 Q
                                      (Φ
                                         match x1 return val with
                                         | nil => InjLV LitV
                                         | cons v _ => InjRV v
                                         end)))))) one
                     return (env (T0 u))
                   with
                   | Envs _ env_spatial0 => env_spatial0
                   end) (o x)))))
.
  Show.
Abort.
