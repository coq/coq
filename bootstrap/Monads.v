(* -*- coq-prog-args: ("-emacs-U" "-impredicative-set") -*- *)

Reserved Notation "'do' M x ':=' e 'in' u" (at level 200, M at level 0, x ident, e at level 200, u at level 200).
(*Reserved Notation "'do' e ; u" (at level 200, e at level 200, u at level 200).*)

(*** Unit ***)

Extract Inductive unit => unit [
  "()"
].
Notation "()" := tt.

(*** Bool ***)
Extract Inductive bool => bool [
  "true"
  "false"
].

(*** List ***)
Extract Inductive list => list [
  "[]"
  "(::)"
].
Opaque app.
Extraction Implicit app [A].
Extract Inlined Constant app => "List.append".

(*** Prod ***)
Extract Inductive prod => "(*)" [
  "(,)"
].
Opaque fst.
Extraction Implicit fst [A B].
Extract Inlined Constant fst => "fst".
Extraction Implicit snd [A B].
Opaque snd.
Extract Inlined Constant snd => "snd".


(*** Closure elimination **)

(* [freeze] is used to help OCaml figure where partial applications
   are usually made. This way, the compiler will output code optimised
   for partial applications to happen at this point. It happens to
   make the monadic code substantially faster.

   Documentation on that particular behaviour can be found at:
   https://ocaml.janestreet.com/?q=node/30
*)

Parameter freeze : forall (A : Set), A -> A.
Extraction Implicit freeze [A].
Extract Inlined Constant freeze => "();".

(*** Exceptions ***)

Parameter Exception : Set.
Extract Inlined Constant Exception => exn.

Parameter tactic_failure : Exception -> Exception.
Extract Inlined Constant tactic_failure => "(fun e -> Proof_errors.TacticFailure e)".

(*** Basic integers ***)

Parameter Int : Set.
Extract Inlined Constant Int => int.

(*** Char ***)

Parameter Char : Set.
Extract Inlined Constant Char => char.

(*** Primitive strings ***)

Parameter String : Set.
Extract Inlined Constant String => string.

(*** Pretty printer ***)

Parameter Ppcmds : Set.
Extract Inlined Constant Ppcmds => "Pp.std_ppcmds".

(*** A view datatype for the [split] primitive ***)

Inductive list_view (A B:Set) : Set :=
| Nil : Exception -> list_view A B
| Cons : A -> B -> list_view A B
.

(*** Monoids ***)

Module Monoid.

Record T (M:Set) := {
  zero : M;
  prod : M -> M -> M
}.

(** Cartesian product of monoids *)
Definition cart {M₁} (Mon₁:T M₁) {M₂} (Mon₂:T M₂) : T (M₁*M₂) := {|
  zero := (Mon₁.(zero _),Mon₂.(zero _));
  prod x y := (Mon₁.(prod _) (fst x) (fst y), Mon₂.(prod _) (snd x) (snd y))
|}.

Definition BoolAnd : T bool := {|
  zero := true;
  prod := andb
|}.

Definition List {A:Set} : T (list A) := {|
  zero := nil ;
  prod := @app _
|}.

End Monoid.

(*** Monads and related interfaces ***)
(* spiwack: the interfaces are presented in a mixin style.
   I haven't tested other presentation, it just felt
   convenient when I started *)

Record Monad (T:Set->Set) := {
  ret : forall{A:Set}, A->T A;
  bind : forall{A B:Set}, T A -> (A -> T B) -> T B;
  ignore : forall{A:Set}, T A -> T unit;
  seq : forall{A:Set}, T unit -> T A -> T A;
  map : forall {A B : Set}, (A -> B) -> T A -> T B
}.

Notation "'do' M x ':=' e 'in' u" := (bind _ M e (fun x => u)).

Record State (S:Set) (T:Set->Set) := {
  set : S -> T unit;
  get : T S ;
  modify : (S -> S) -> T unit
}.

(* spiwack: Environment and Writer are given distinct interfaces from
   State (rather than state beeing the composition of these) because I
   don't really know how to combine the three together. However, we
   might want to be able to arrange things so that we can say "I have a
   number of things I can get, and a number of things I can set, some
   of which can be got, and the other being monoids, then I have a
   monad". I have yet to find how to do that though.*)
Record Environment (E:Set) (T:Set->Set) := { current : T E }.

Record Writer (M:Set) (T:Set->Set) := {
  put : M -> T unit
}.

Record Logic (T:Set -> Set) := {
  (* [zero] is usually argument free, but Coq likes to explain errors,
     hence error messages should be carried around. *)
  zero : forall {A}, Exception -> T A;
  plus : forall {A}, T A -> (Exception -> T A) -> T A
}.
(** Writing (+) for plus and (>>=) for bind, we shall require that

    x+(y+z) = (x+y)+z

    zero+x = x

    x+zero = x

    (x+y)>>=k = (x>>=k)+(y>>=k) *)
(* The [T] argument represents the "global" effect: it is not
   backtracked when backtracking occurs at a [plus]. *)
(* spiwack: hence, [T] will not be instanciated with a state monad
   representing the proofs, we will use a surrounding state transformer
   to that effect. [T] is meant to be instantiated with [IO]. *)


Module Id.

 Definition M : Monad (fun A => A) := {|
   ret := fun _ x => x;
   bind := fun _ _ x k => k x;
   ignore := fun _ x => ();
   seq := fun _ x k => k;
   map := fun _ _ f x => f x
 |}.

End Id.

Module IOBase.

 Parameter T : Set -> Set.
 Extract Constant T "'a" => "unit -> 'a".
 Parameter Ref : Set -> Set.
 Extract Constant Ref "'a" => "'a Pervasives.ref".

 Parameter ret : forall (A:Set), A -> T A.
 Extract Constant ret => "fun a -> (); fun () -> a".
 Extraction Implicit ret [A].
 Parameter bind : forall A B, T A -> (A->T B) -> T B.
 Extract Constant bind => "fun a k -> (); fun () -> k (a ()) ()".
 Extraction Implicit bind [A B].
 Parameter ignore : forall A, T A -> T unit.
 Extract Constant ignore => "fun a -> (); fun () -> ignore (a ())".
 Extraction Implicit ignore [A].
 Parameter seq : forall A, T unit -> T A -> T A.
 Extract Constant seq => "fun a k -> (); fun () -> a (); k ()".
 Extraction Implicit seq [A].
 Parameter map : forall (A B : Set), (A -> B) -> T A -> T B.
 Extract Constant map => "fun f a -> (); fun () -> f (a ())".
 Extraction Implicit map [A B].

 Parameter ref : forall (A:Set), A -> T (Ref A).
 Extract Constant ref => "fun a -> (); fun () -> Pervasives.ref a".
 Extraction Implicit ref [A].
 Parameter set : forall A, Ref A -> A -> T unit.
 Extract Constant set => "fun r a -> (); fun () -> Pervasives.(:=) r a".
 Extraction Implicit set [A].
 Parameter get : forall A, Ref A -> T A.
 Extract Constant get => "fun r -> (); fun () -> Pervasives.(!) r".
 Extraction Implicit get [A].

 Parameter raise : forall A, Exception -> T A.
 Extract Constant raise => "fun e -> (); fun () -> raise (Proof_errors.Exception e)".
 Extraction Implicit raise [A].
 Parameter catch : forall A, T A -> (Exception -> T A) -> T A.
 Extract Constant catch => "fun s h -> ();
  fun () -> try s ()
  with Proof_errors.Exception e as src ->
    let src = Errors.push src in
    let e = Backtrace.app_backtrace ~src ~dst:e in
    h e ()".
 Extraction Implicit catch [A].

 Parameter read_line : T String.
 Extract Constant read_line => "fun () -> try Pervasives.read_line () with e -> let e = Errors.push e in raise e ()".
 Parameter print_char : Char -> T unit.
 Extract Constant print_char => "fun c -> (); fun () -> print_char c".
 Parameter print : Ppcmds -> T unit.
 Extract Constant print => "fun s -> (); fun () -> try Pp.pp s; Pp.pp_flush () with e -> let e = Errors.push e in raise e ()".

 Parameter timeout: forall A, Int -> T A -> T A.
 Extract Constant timeout => "fun n t -> (); fun () ->
    let timeout_handler _ = Pervasives.raise (Proof_errors.Exception Proof_errors.Timeout) in
    let psh = Sys.signal Sys.sigalrm (Sys.Signal_handle timeout_handler) in
    Pervasives.ignore (Unix.alarm n);
    let restore_timeout () =
      Pervasives.ignore (Unix.alarm 0);
      Sys.set_signal Sys.sigalrm psh
    in
    try
      let res = t () in
      restore_timeout ();
      res
    with
    | e ->
      let e = Errors.push e in
      restore_timeout ();
      Pervasives.raise e
 ".
 Extraction Implicit timeout [A].

End IOBase.

(* spiwack: IO is split in two modules to avoid moot dependencies and
   useless extracted code. *)
Module IO.

 Record S (Ref:Set->Set) (T:Set->Set) : Set := {
   ref : forall {A:Set}, A -> T (Ref A);
   set : forall {A:Set}, Ref A -> A -> T unit;
   get : forall {A:Set}, Ref A -> T A;

   read_line : T String;
   print_char : Char -> T unit;
   print : Ppcmds -> T unit;

   raise : forall {A:Set}, Exception -> T A;
   catch : forall {A:Set}, T A -> (Exception -> T A) -> T A;
   timeout : forall {A:Set}, Int -> T A -> T A
 }.

 Definition T : Set -> Set := IOBase.T.
 Definition Ref : Set -> Set := IOBase.Ref.

 Definition M : Monad T := {|
   ret := IOBase.ret;
   bind := IOBase.bind;
   ignore := IOBase.ignore;
   seq := IOBase.seq;
   map := IOBase.map
 |}.

 Definition IO : S Ref T := {|
   ref := IOBase.ref;
   set := IOBase.set;
   get := IOBase.get;

   read_line := IOBase.read_line;
   print_char := IOBase.print_char;
   print := IOBase.print;

   raise := IOBase.raise;
   catch := IOBase.catch;
   timeout := IOBase.timeout
 |}.

End IO.

Module State.
(** The impredicative encoding of the usual State monad transformer
    (StateT in Haskell). The impredicative encoding allows to avoid
    creating blocks (val,state) at each bind. *)

Section Common.

 Variables (S:Set) (T₀:Set->Set) (M:Monad T₀).

 Definition T (A:Set):= forall R:Set, (A -> S -> T₀ R) -> S -> T₀ R.

 Definition F : Monad T := {|
   ret A x := fun R k s => k x s ;
   bind A B x f := fun R k s =>
            x R (fun a s' => f a R k s') s ;
   ignore A x := fun R k s =>
            x R (fun _ s' => k tt s') s ;
   seq A x y := fun R k s =>
           x R (fun _ s' => y R k s') s;
   map A B f x := fun R k s => x R (fun a s => k (f a) s) s
 |}.

 Definition State : State S T := {|
   set s := (fun R k _ => k () s) : T unit  ;
   get := fun R k s => k s s ;
   modify := fun f R k s => k () (f s)
 |}.

 Definition lift {A} (x:T₀ A) : T A := fun R k s =>
   do M x := x in
   k x s
 .

 Definition run {A} (x:T A) (s:S) : T₀ (A*S) := x _ (fun a s' => ret _ M (a,s')) s.
 Definition reflect {A:Set} (x:S -> T₀ (A*S)) : T A := fun R k s =>
   do M x' := x s in
   let '(a,s') := x' in
   k a s'
 .


 Variable (L:Logic T₀).

 Definition Logic : Logic T := {|
   zero A e := lift (zero _ L e);
   plus A x y := fun R k s => plus _ L (x R k s) (fun e => y e R k s)
 |}.

 Variable (Env:Set) (E:Environment Env T₀).

 Definition Environment : Environment Env T := {|
   current := lift (current _ _ E)
 |}.

 Variable (C:Set) (W:Writer C T₀).

 Definition Writer : Writer C T := {|
   put x := lift (put _ _ W x)
 |}.

End Common.

End State.


Module Environment.
(** The impredicative encoding of the usual environment monad
    transformer (ReaderT in Haskell). The impredicative encoding
    allows to avoid using the binding operations of the underlying
    monad when it isn't explicitly needed. *)

Section Common.

 Variable (E:Set) (T₀:Set->Set) (M:Monad T₀).

 Definition T (A:Set) := forall (R:Set), (A -> T₀ R)-> E-> T₀ R.

 Definition F : Monad T := {|
   ret A x := fun R k e => k x;
   bind A B x f := fun R k e => x _ (fun a => f a _ k e) e;
   ignore A x := fun R k e => x _ (fun _ => k tt) e;
   seq A x y := fun R k e => x _ (fun _ => y _ k e) e;
   map A B f x := fun R k e => x _ (fun a => k (f a)) e
 |}.

 Definition Environment : Environment E T := {|
   current := fun R k e => k e 
 |}.


 Definition lift {A:Set} (x:T₀ A) : T A := fun R k _ =>
   do M x := x in
   k x
 .

 Definition run {A:Set} (x:T A) (e:E) : T₀ A := x _ (fun a => ret _ M a) e.
 Definition reflect {A:Set} (m:E->T₀ A) : T A := fun R k e =>
   do M m' := m e in
   k m'
 .


 Variable (L:Logic T₀).

 Definition Logic : Logic T := {|
   zero A e := lift (zero _ L e);
   plus A x y := fun R k e => plus _ L (x _ k e) (fun exc => y exc _ k e)
 |}.

 Variable (C:Set) (W:Writer C T₀).

 Definition Writer : Writer C T := {|
   put x := lift (put _ _ W x)
 |}.

End Common.

End Environment.

Module Writer.
(** The impredicative encoding of the usual "writer" monad
    transformer (WriterT in Haskell). The impredicative encoding
    allows to avoid using the binding operations of the underlying
    monad when it isn't explicitly needed and to avoid constructing
    and deconstructing values of the form (val,c). *)

Section Common.

 Variables (C:Set) (m:Monoid.T C) (T₀:Set->Set) (M:Monad T₀).

 Definition T (A:Set) := forall (R:Set), (A->C->T₀ R) -> T₀ R.

 Definition F : Monad T := {|
   ret A x := fun R k => k x (Monoid.zero _ m);
   bind A B x f := fun R k =>
     x _ (fun a c => f a _ (fun b c' => k b (Monoid.prod _ m c c')));
   ignore A x := fun R k => x _ (fun _ c => k tt c);
   seq A x y := fun R k =>
     x _ (fun _ c => y _ (fun b c' => k b (Monoid.prod _ m c c')));
   map A B f x := fun R k => x _ (fun a c => k (f a) c)
 |}.

 Definition Writer : Writer C T := {|
   put c := ((fun R (k:unit->C->T₀ R) => k tt c):T unit)
 |}.

 Definition lift {A} (x:T₀ A) : T A := fun R k =>
   do M x := x in
   k x (Monoid.zero _ m)
 .

 Definition run {A} (x:T A) : T₀ (A*C)%type := x _ (fun a c => ret _ M (a,c)).
 Definition reflect {A:Set} (x:T₀ (A*C)) :T A := fun R k =>
   do M x := x in
   let '(a,c) := x in
   k a c
 .

 Variable (L:Logic T₀).

 Definition Logic : Logic T := {|
   zero A e := lift (zero _ L e);
   plus A x y := fun R k => plus _ L (x _ k) (fun exc => y exc _ k)
 |}.

End Common.

End Writer.


Module Logic.

(* Double-continuation backtracking monads are reasonable folklore for
   "search" implementations (including Tac interactive prover's
   tactics). Yet it's quite hard to wrap your head around these.  I
   recommand reading a few times the "Backtracking, Interleaving, and
   Terminating Monad Transformers" paper by O. Kiselyov, C. Shan,
   D. Friedman, and A. Sabry.  The peculiar shape of the monadic type
   is reminiscent of that of the continuation monad transformer.

   The paper also contains the rational for the [split] abstraction.

   An explanation of how to derive such a monad from mathematical
   principles can be found in "Kan Extensions for Program
   Optimisation" by Ralf Hinze.

   One way to think of the [Logic] functor is to imagine ['a
   Logic(X).t] to represent list of ['a] with an exception at the
   bottom (leaving the monad-transforming issues aside, as they don't
   really work well with lists). Each of the element is a valid
   result, sequentialising with a [f:'a -> 'b t] is done by applying
   [f] to each element and then flatten the list, [plus] is
   concatenation, and [split] is pattern-matching. *)

Section Common.

 Variables (T₀:Set->Set) (M:Monad T₀).

 Definition FK (R:Set) : Set := Exception -> R.
 Definition SK (A R:Set) : Set := A -> FK R -> R.
 Definition T (A:Set) : Set := forall (R:Set), SK A (T₀ R) -> FK (T₀ R) -> T₀ R.
 (* spiwack: the implementation is an adaptation of the aforementionned
    "Backtracking, Interleaving, and Terminating Monad Transformers"
    paper *)
 (* spiwack: [fk] stands for failure continuation, and [sk] for success
    continuation. *)

 Definition F : Monad T := {|
   ret A x R sk fk := sk x fk;
   bind A B x k R sk fk :=
      x _ (fun a fk => k a _ sk fk) fk;
   ignore A x R sk fk :=
      x _ (fun _ fk => sk () fk) fk;
   seq A x k R sk fk :=
      x _ (fun _ fk => k _ sk fk) fk;
   map A B f x R sk fk := x _ (fun a fk => sk (f a) fk) fk
 |}.

 Definition lift {A} (x:T₀ A) : T A := fun _ sk fk =>
   do M x := x in
   sk x fk
 .

 Definition _zero {A:Set} (e:Exception) : T A := fun _ _ fk => fk e.
 Definition _plus {A:Set} (x:T A) (y:Exception -> T A) : T A := fun _ sk fk =>
   x _ sk (fun e => y e _ sk fk)
 .

 (* For [reflect] and [split] see the "Backtracking, Interleaving, and
    Terminating Monad Transformers" paper.  *)
 Definition reflect {A:Set} (x:list_view A (Exception -> T A)) : T A :=
   match x with
   | Nil _ _ e => _zero e
   | Cons _ _ a x => _plus (ret _ F a) x
   end
 .
 Definition reify {A:Set} (x:T A) : T₀ (list_view A (Exception -> T A)) :=
   let fk e := ret _ M (Nil _ _ e) in
   let lift_fk fk e := do F y := lift (fk e) in reflect y in
   let sk a fk := ret _ M (Cons _ _ a (lift_fk fk)) in
   x _ sk fk
 .

 Definition split {A:Set} (x:T A) : T (list_view A (Exception -> T A)) :=
   lift (reify x)
 .

 Definition Logic : Logic T := {|
   zero := @_zero;
   plus := @_plus
 |}.

 Variable (Ref:Set->Set) (IO:IO.S Ref T₀).

 Definition run {A:Set} (x:T A) : T₀ A :=
   let sk (a:A) _ : T₀ A := ret _ M a in
   let fk e : T₀ A := IO.raise _ _ IO (tactic_failure e) in
   x _ sk fk
 .

End Common.

End Logic.


(*** Extraction **)

Parameters (constr types evar_map goal env seffs:Set).
Extract Inlined Constant constr => "Term.constr".
Extract Inlined Constant types => "Term.types".
Extract Inlined Constant evar_map => "Evd.evar_map".
Extract Inlined Constant goal => "Goal.goal".
Extract Inlined Constant env => "Environ.env".

Record proofview := {
  solution : evar_map;
  comb : list goal
}.

Definition LogicalState := proofview.
(** Logical Message: status (safe/unsafe) * ( shelved goals * given up ) *)
Definition LogicalMessageType := ( bool * ( list goal * list goal ))%type.
Definition LogicalEnvironment := env.
Definition LogicalMessage : Monoid.T LogicalMessageType :=
  Monoid.cart Monoid.BoolAnd (Monoid.cart Monoid.List Monoid.List)
.

Definition NonLogicalType := IO.T.
Definition NonLogicalMonad : Monad NonLogicalType := IO.M.
Definition NonLogicalIO : IO.S IO.Ref NonLogicalType := IO.IO.

Definition LogicType := Logic.T NonLogicalType.
Definition WriterType := Writer.T LogicalMessageType LogicType.
Definition EnvironmentType := Environment.T LogicalEnvironment WriterType.
Definition LogicalType := State.T LogicalState EnvironmentType.
Definition LogicalMonadBase := Logic.F NonLogicalType.
Definition LogicalMonadWriter := Writer.F _ LogicalMessage LogicType.
Definition LogicalMonadEnv := Environment.F LogicalEnvironment WriterType.
Definition LogicalMonad : Monad LogicalType := State.F LogicalState _.
Definition LogicalStateM : State LogicalState LogicalType := State.State LogicalState _.
Definition LogicalReaderE : Environment LogicalEnvironment _ := Environment.Environment LogicalEnvironment WriterType.
Definition LogicalReader : Environment LogicalEnvironment LogicalType := State.Environment _ _ LogicalMonadEnv _ LogicalReaderE.
Definition LogicalWriterW : Writer LogicalMessageType  _ := Writer.Writer LogicalMessageType LogicType.
Definition LogicalWriterE : Writer LogicalMessageType _ := Environment.Writer LogicalEnvironment _ LogicalMonadWriter LogicalMessageType LogicalWriterW.
Definition LogicalWriter : Writer LogicalMessageType LogicalType := State.Writer _ _ LogicalMonadEnv _ LogicalWriterE.
Definition LogicalLogic : Logic LogicalType := State.Logic _ _ LogicalMonadEnv (Environment.Logic _ _ LogicalMonadWriter (Writer.Logic _ LogicalMessage _ LogicalMonadBase (Logic.Logic _))).


(* The function [split] will be define as the normal form of
   [split0]. It reifies the monad transformer stack until we can read
   back a more syntactic form, then reflects the result back. *)
Definition split0 {a:Set} (x:LogicalType a) : LogicalType (list_view a (Exception -> LogicalType a)) :=
  State.reflect _ _ LogicalMonadEnv (fun s =>
  Environment.reflect _ _ LogicalMonadWriter (fun e =>
  Writer.reflect _ _ LogicalMonadBase (
    do LogicalMonadBase x' :=
        Logic.split _ NonLogicalMonad (Writer.run _ _ LogicalMonadBase (Environment.run _ _ LogicalMonadWriter (State.run _ _ LogicalMonadEnv x s) e)) in
    match x' with
    | Nil _ _ exc => ret _ LogicalMonadBase ((Nil _ _ exc),s, Monoid.zero _ LogicalMessage)
    | Cons _ _ (a',s',m') y =>
      let y' exc :=
          State.reflect _ _ LogicalMonadEnv (fun _ =>
          Environment.reflect _ _ LogicalMonadWriter (fun _ =>
          Writer.reflect _ _ LogicalMonadBase (y exc)))
      in
      ret _ LogicalMonadBase (Cons _ _ a' y',s',m')
    end
  )))
.


Module NonLogical.

 Definition t (a:Set) := Eval compute in NonLogicalType a.
 Definition ref (a:Set) := Eval compute in IO.Ref a.

 Definition ret {a:Set} (x:a) : t a := Eval compute in ret _ NonLogicalMonad x.
 Extraction Implicit ret [a].
 Definition bind {a b:Set} (x:t a) (k:a-> t b) : t b := Eval compute in bind _ NonLogicalMonad x k.
 Extraction Implicit bind [a b].

 Definition ignore {a:Set} (x:t a) : t unit := Eval compute in ignore _ NonLogicalMonad x.
 Extraction Implicit ignore [a].
 Definition seq {a:Set} (x:t unit) (k:t a) : t a := Eval compute in seq _ NonLogicalMonad x k.
 Extraction Implicit seq [a].
 Definition map {a b:Set} (f:a -> b) (x:t a) : t b := Eval compute in freeze _ (map _ NonLogicalMonad f x).
 Extraction Implicit map [a b].

 Definition new_ref {a:Set} (x:a) : t (ref a) := Eval compute in IO.ref _ _ NonLogicalIO x.
 Extraction Implicit new_ref [a].
 Definition set {a:Set} (r:ref a) (x:a) : t unit := Eval compute in IO.set _ _ NonLogicalIO r x.
 Extraction Implicit set [a].
 Definition get {a:Set} (r:ref a) : t a := Eval compute in IO.get _ _ NonLogicalIO r.
 Extraction Implicit get [a].

 Definition raise {a:Set} (e:Exception) : t a := Eval compute in IO.raise _ _ NonLogicalIO e.
 Extraction Implicit raise [a].
 Definition catch {a:Set} (s:t a) (h:Exception -> t a) : t a := Eval compute in IO.catch _ _ NonLogicalIO s h.
 Extraction Implicit catch [a].
 Definition timeout {a:Set} n (x:t a) : t a := Eval compute in IO.timeout _ _ NonLogicalIO n x.
 Extraction Implicit timeout [a].

 Definition read_line : t String := Eval compute in IO.read_line _ _ NonLogicalIO.
 Definition print_char (c:Char) : t unit := Eval compute in IO.print_char _ _ NonLogicalIO c.
 Definition print (s:Ppcmds) : t unit := Eval compute in IO.print _ _ NonLogicalIO s.

 (* /!\ The extracted code for [run] performs effects. /!\ *)
 Parameter run : forall a:Set, t a -> a.
 Extract Constant run => "fun x ->
  try x () with Proof_errors.Exception e as src ->
    let src = Errors.push src in
    let e = Backtrace.app_backtrace ~src ~dst:e in
    Pervasives.raise e".
 Extraction Implicit run [a].

End NonLogical.

Module Logical.

 Definition t (a:Set) := Eval compute in LogicalType a.

 Definition ret {a:Set} (x:a) : t a := Eval compute in freeze _ (ret _ LogicalMonad x).
 Extraction Implicit ret [a].
 Definition bind {a b:Set} (x:t a) (k:a-> t b) : t b := Eval compute in freeze _ (bind _ LogicalMonad x k).
 Extraction Implicit bind [a b].
 Definition ignore {a:Set} (x:t a) : t unit := Eval compute in freeze _ (ignore _ LogicalMonad x).
 Extraction Implicit ignore [a].
 Definition seq {a:Set} (x:t unit) (k:t a) : t a := Eval compute in freeze _ (seq _ LogicalMonad x k).
 Extraction Implicit seq [a].
 Definition map {a b:Set} (f:a -> b) (x:t a) : t b := Eval compute in freeze _ (map _ LogicalMonad f x).
 Extraction Implicit map [a b].

 Definition set (s:LogicalState) : t unit := Eval compute in freeze _ (set _ _ LogicalStateM s).
 Definition get : t LogicalState := Eval compute in get _ _ LogicalStateM.
 Definition modify (f : LogicalState -> LogicalState) : t unit := Eval compute in freeze _ (modify _ _ LogicalStateM f).
 Definition put (m:LogicalMessageType) : t unit := Eval compute in freeze _ (put _ _ LogicalWriter m).
 Definition current : t LogicalEnvironment := Eval compute in current _ _ LogicalReader.

 Definition zero {a:Set} (e:Exception) : t a := Eval compute in freeze _ (zero _ LogicalLogic e).
 Extraction Implicit zero [a].
 Definition plus {a:Set} (x:t a) (y:Exception -> t a) : t a := Eval compute in freeze _ (plus _ LogicalLogic x y).
 Extraction Implicit plus [a].

 Definition split {a:Set} (x:t a) : t (list_view a (Exception -> t a)) :=
   Eval compute in freeze _ (split0 x).
 Extraction Implicit split [a].
 Definition lift {a:Set} (x:NonLogical.t a) : t a := Eval compute in
  freeze _ (State.lift _ _ LogicalMonadEnv (Environment.lift _ _ LogicalMonadWriter (Writer.lift _ LogicalMessage _ LogicalMonadBase (Logic.lift _ NonLogicalMonad x)))).
 Extraction Implicit lift [a].

 Definition run {a:Set} (x:t a) (e:LogicalEnvironment) (s:LogicalState) : NonLogical.t ((a*LogicalState)*LogicalMessageType) := Eval compute in
  Logic.run _ NonLogicalMonad _ NonLogicalIO (Writer.run _ _ LogicalMonadBase (Environment.run _ _ LogicalMonadWriter (State.run _ _ LogicalMonadEnv x s) e))
 .
 Extraction Implicit run [a].

End Logical.

Set Extraction Flag 1007.
Set Extraction Conservative Types.
Set Extraction File Comment "
This file has been generated by extraction of bootstrap/Monads.v.
It shouldn't be modified directly. To regenerate it run
coqtop -batch -impredicative-set -l bootstrap/Monads.v in Coq's source
directory.
".

Extraction "proofs/proofview_gen.ml" NonLogical Logical.
