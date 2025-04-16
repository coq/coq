(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Ltac2.Init.
Require Ltac2.Ind Ltac2.Array.

Ltac2 @ external type : constr -> constr := "rocq-runtime.plugins.ltac2" "constr_type".
(** Return the type of a term *)

Ltac2 @ external equal : constr -> constr -> bool := "rocq-runtime.plugins.ltac2" "constr_equal".
(** Strict syntactic equality: only up to α-conversion and evar expansion *)

Module Binder.

Ltac2 Type relevance_var.
Ltac2 Type relevance := [ Relevant | Irrelevant | RelevanceVar (relevance_var) ].

Ltac2 @ external make : ident option -> constr -> binder := "rocq-runtime.plugins.ltac2" "constr_binder_make".
(** Create a binder given the name and the type of the bound variable.
    Fails if the type is not a type in the current goal. *)

Ltac2 @ external unsafe_make : ident option -> relevance -> constr -> binder := "rocq-runtime.plugins.ltac2" "constr_binder_unsafe_make".
(** Create a binder given the name and the type and relevance of the bound variable. *)

Ltac2 @ external name : binder -> ident option := "rocq-runtime.plugins.ltac2" "constr_binder_name".
(** Retrieve the name of a binder. *)

Ltac2 @ external type : binder -> constr := "rocq-runtime.plugins.ltac2" "constr_binder_type".
(** Retrieve the type of a binder. *)

Ltac2 @ external relevance : binder -> relevance := "rocq-runtime.plugins.ltac2" "constr_binder_relevance".
(** Retrieve the relevance of a binder. *)

End Binder.

Module Unsafe.

(** Low-level access to kernel terms. Use with care! *)

Ltac2 Type case.
(** A value of [case] is data carried by a pattern match expression that
    contains a reference to the inductive type being matched on. Given an
    inductive type, one can use the [case] function below to construct pattern
    match expressions on that type, or given a pattern match expression one can
    use the [Case.inductive] function to get the inductive type associated to
    the pattern match. *)

Ltac2 Type case_invert
(** A piece of metadata attached to a pattern match expression which
tells Rocq which reduction rule to use for the pattern match *)
  := [
  | NoInvert
  (** The normal reduction rule: reduce the pattern match exactly when the
      scrutinee is a constructor. *)
  | CaseInvert (constr array)
  (** The special reduction rule for eliminating out of an [SProp] into a
      non-[SProp]. Normally such elimination is only legal when the [SProp] has no
      constructors, in which case the match is irreducible. If the [SProp] was
      defined with the [Definitional UIP] flag on, and the [SProp] has one
      constructor which takes no non-parameter arguments, then the match is
      reducible if the indices for the scrutinee are unifiable with the indices
      for the unique constructor. See the [Definitional UIP] section of the
      [SProp] documentation in the refman for more information. *)
].

Ltac2 Type kind := [
  | Rel (int)
  (** de Bruijn local variable, bound by a surrounding binder such as [forall], [fun], etc.
      No [Rel] is bound in a goal's context: the goal context is all [Var]s. *)
  | Var (ident)
  (** Named variable (section variables and proof context variables are treated identically) *)
  | Meta (meta)
  (** An older, legacy implementation of unification variables. This is probably
      dead code. *)
  | Evar (evar, constr array)
  (** Existential variable (unification variable). In [Evar evar array], [evar] is the existential variable
      itself and [array] is the local variable instance, i.e. values for each of the variables in the evar's context.
      For an evar [x : T1, y : T2 |- ?e : Te], [?e@{x:=e1; y:=e2}] gives array [[|e2; e1|]].
      See also flag [Printing Existential Instances] in the refman. *)
  | Sort (sort)
  (** A sort such as Prop, SProp, Type@{u}, a polymorphic sort Type@{s|u}, etc. (cf. refman Core language > Sorts) *)
  | Cast (constr, cast, constr)
  (** [Cast t1 k t2] corresponds to the syntactic term [(t1 : t2)], i.e.,
      the programmer declares that [t1] is of type [t2]. [k] is a flag telling
      the kernel what strategy should be used to validate this assertion,
      e.g., VM or native evaluation. *)
  | Prod (binder, constr)
  (** Concrete syntax ["forall A:B,C"] is represented as [Prod (A:B) C].
      [A] is bound as a [Rel] in [C]. *)
  | Lambda (binder, constr)
  (** Concrete syntax ["fun A:B => C"] is represented as [Lambda (A:B) C].
      [A] is bound as a [Rel] in [C]. *)
  | LetIn (binder, constr, constr)
  (** Concrete syntax ["let A:C := B in D"] is represented as
      [LetIn (A:C) B D]. [A] is bound as a [Rel] in [D]. *)
  | App (constr, constr array)
  (** Application is n-ary. Concrete syntax ["(F P1 P2 ...  Pn)"] is represented as [App (F, [|P1; P2; ...; Pn|])]. *)
  | Constant (constant, instance)
  (** [Constant c ui] is the constant [c] @ universe instance [ui]. *)
  | Ind (inductive, instance)
  (** A name of an inductive or coinductive type. [Ind ind ui] is [ind@[ui]] *)
  | Constructor (constructor, instance)
  (** A constructor of an inductive type. [Constructor c ui] is [c@[ui]]. *)
  | Case (case, (constr * Binder.relevance), case_invert, constr, constr array)
  (** [Case case (fun u1 u2 ... un v => rettype, _) ci scrut
          [|(fun x1 x2 => t1);(fun y1 y2 y3 => t2));...|]]
      corresponds to
      [match scrut in I u1 u2 ... as v return rettype with
       | c0 _ _ x1 x2 => t1
       | c1 _ _ y1 y2 y3 => t2
       | (...)
      end].
      [ci] is of interest when [scrut] inhabits an [SProp], see comments on the type
      [case_invert] above. [case] contains a reference to the inductive type of the scrutinee.*)
  | Fix (int array, int, binder array, constr array)
  (** [fix fun0 (b00 : B00) (b01 : B01) (...) {struct b0_k0} : C0 := t0 with
           fun1 (b10 : B10) (b11 : B11) (...) {struct b1_k1} : C1 := t1 with
           (...)
           for funi]
      is represented as
      [Fix [|k0;k1;...|] i [|
          fun0 : forall (b00 : B00) (b01 : B01) (...), C0;
          fun1 : forall (b10 : B10) (b11 : B11) (...), C1;
          (...)
       |] [|
          fun b00 b01 (...) => t0;
          fun b00 b01 (...) => t1;
          (...)
       |]] *)
  | CoFix (int, binder array, constr array)
  | Proj (projection, Binder.relevance, constr)
  (** [Proj p r c] is [c.(p)]. The relevance is the relevance of the whole term. *)
  | Uint63 (uint63)
  | Float (float)
  | String (pstring)
  | Array (instance, constr array, constr, constr)
   (** [Array u vals def t] is the primitive array literal [[|vals | def : t|]@{u}]. *)
].

Ltac2 @ external kind : constr -> kind := "rocq-runtime.plugins.ltac2" "constr_kind".

Ltac2 rec kind_nocast c :=
  match kind c with
  | Cast c _ _ => kind_nocast c
  | k => k
  end.

Ltac2 @ external make : kind -> constr := "rocq-runtime.plugins.ltac2" "constr_make".

Ltac2 @ external check : constr -> constr result := "rocq-runtime.plugins.ltac2" "constr_check".
(** Checks that a constr generated by unsafe means is indeed safe in the
    current environment, and returns it, or the error otherwise. Panics if
    not focused. *)

Ltac2 @ external liftn : int -> int -> constr -> constr := "rocq-runtime.plugins.ltac2" "constr_liftn".
(** [liftn n k c] lifts by [n] indices greater than or equal to [k] in [c]
    Note that with respect to substitution calculi's terminology, [n]
    is the _shift_ and [k] is the _lift_. *)

Ltac2 @ external substnl : constr list -> int -> constr -> constr := "rocq-runtime.plugins.ltac2" "constr_substnl".
(** [substnl [r₁;...;rₙ] k c] substitutes in parallel [Rel(k+1); ...; Rel(k+n)] with
    [r₁;...;rₙ] in [c]. *)

Ltac2 @ external closenl : ident list -> int -> constr -> constr := "rocq-runtime.plugins.ltac2" "constr_closenl".
(** [closenl [x₁;...;xₙ] k c] abstracts over variables [x₁;...;xₙ] and replaces them with
    [Rel(k); ...; Rel(k+n-1)] in [c]. If two names are identical, the one of least index is kept. *)

Ltac2 @ external closedn : int -> constr -> bool := "rocq-runtime.plugins.ltac2" "constr_closedn".
(** [closedn n c] is true iff [c] is a closed term under [n] binders *)

Ltac2 is_closed (c : constr) : bool := closedn 0 c.
(** [is_closed c] is true iff [c] is a closed term (contains no [Rel]s) *)

Ltac2 @ external noccur_between : int -> int -> constr -> bool := "rocq-runtime.plugins.ltac2" "constr_noccur_between".
(** [noccur_between n m c] returns true iff [Rel p] does not occur in term [c]
  for [n <= p < n+m] *)

#[deprecated(since="9.0", note="occur_between currently behaves as noccur_between.
Use noccur_between instead if you want [true] for variables which do not occur in the term
and its negation if you want [false].")]
Ltac2 occur_between := noccur_between.

Ltac2 noccurn (n : int) (c : constr) : bool := noccur_between n 1 c.
(** [noccurn n c] returns true iff [Rel n] does not occur in term [c] *)

#[deprecated(since="9.0", note="occurn currently behaves as noccurn.
Use noccurn instead if you want [true] for variables which do not occur in the term
and its negation if you want [false].")]
Ltac2 occurn (n : int) (c : constr) : bool := noccur_between n 1 c.

Ltac2 @ external case : inductive -> case := "rocq-runtime.plugins.ltac2" "constr_case".
(** Generate the case information for a given inductive type. *)

Ltac2 constructor (ind : inductive) (i : int) : constructor :=
  Ind.get_constructor (Ind.data ind) i.
(** Generate the i-th constructor for a given inductive type. Indexing starts
    at 0. Panics if there is no such constructor. *)

Module Case.
  Ltac2 @ external equal : case -> case -> bool := "rocq-runtime.plugins.ltac2" "constr_case_equal".
  (** Checks equality of the inductive components of the
      case info. When comparing the inductives, those obtained through
      module aliases or Include are not considered equal by this
      function. *)

  Ltac2 @ external inductive : case -> inductive := "rocq-runtime.plugins.ltac2" "case_to_inductive".
  (** Get the inductive type being matched on in a pattern match expression. *)
End Case.

(** Open recursion combinators *)

Local Ltac2 iter_invert (f : constr -> unit) (ci : case_invert) : unit :=
  match ci with
  | NoInvert => ()
  | CaseInvert indices => Array.iter f indices
  end.

(** [iter f c] iterates [f] on the immediate subterms of [c]; it is
   not recursive and the order with which subterms are processed is
   not specified *)
Ltac2 iter (f : constr -> unit) (c : constr) : unit :=
  match kind c with
  | Rel _ | Meta _ | Var _ | Sort _ | Constant _ _ | Ind _ _
  | Constructor _ _ | Uint63 _ | Float _ | String _ => ()
  | Cast c _ t => f c; f t
  | Prod b c => f (Binder.type b); f c
  | Lambda b c => f (Binder.type b); f c
  | LetIn b t c => f (Binder.type b); f t; f c
  | App c l => f c; Array.iter f l
  | Evar _ l => Array.iter f l
  | Case _ x iv y bl =>
      match x with (x,_) => f x end;
      iter_invert f iv;
      f y;
      Array.iter f bl
  | Proj _p _ c => f c
  | Fix _ _ tl bl =>
      Array.iter (fun b => f (Binder.type b)) tl;
      Array.iter f bl
  | CoFix _ tl bl =>
      Array.iter (fun b => f (Binder.type b)) tl;
      Array.iter f bl
  | Array _u t def ty =>
      f ty; Array.iter f t; f def
  end.

(** [iter_with_binders g f n c] iterates [f n] on the immediate
   subterms of [c]; it carries an extra data [n] (typically a lift
   index) which is processed by [g] (which typically add 1 to [n]) at
   each binder traversal; it is not recursive and the order with which
   subterms are processed is not specified *)
Ltac2 iter_with_binders (g : 'a -> binder -> 'a) (f : 'a -> constr -> unit) (n : 'a) (c : constr) : unit :=
  match kind c with
  | Rel _ | Meta _ | Var _ | Sort _ | Constant _ _ | Ind _ _
  | Constructor _ _ | Uint63 _ | Float _ | String _ => ()
  | Cast c _ t => f n c; f n t
  | Prod b c => f n (Binder.type b); f (g n b) c
  | Lambda b c => f n (Binder.type b); f (g n b) c
  | LetIn b t c => f n (Binder.type b); f n t; f (g n b) c
  | App c l => f n c; Array.iter (f n) l
  | Evar _ l => Array.iter (f n) l
  | Case _ x iv y bl =>
      match x with (x,_) => f n x end;
      iter_invert (f n) iv;
      f n y;
      Array.iter (f n) bl
  | Proj _p _ c => f n c
  | Fix _ _ tl bl =>
      Array.iter (fun b => f n (Binder.type b)) tl;
      let n := Array.fold_left g n tl in
      Array.iter (f n) bl
  | CoFix _ tl bl =>
      Array.iter (fun b => f n (Binder.type b)) tl;
      let n := Array.fold_left g n tl in
      Array.iter (f n) bl
  | Array _u t def ty =>
      f n ty;
      Array.iter (f n) t;
      f n def
  end.

Local Ltac2 binder_map (f : constr -> constr) (b : binder) : binder :=
  Binder.unsafe_make (Binder.name b) (Binder.relevance b) (f (Binder.type b)).

Local Ltac2 map_invert (f : constr -> constr) (iv : case_invert) : case_invert :=
  match iv with
  | NoInvert => NoInvert
  | CaseInvert indices => CaseInvert (Array.map f indices)
  end.

(** [map f c] maps [f] on the immediate subterms of [c]; it is
   not recursive and the order with which subterms are processed is
   not specified *)
Ltac2 map (f : constr -> constr) (c : constr) : constr :=
  match kind c with
  | Rel _ | Meta _ | Var _ | Sort _ | Constant _ _ | Ind _ _
  | Constructor _ _ | Uint63 _ | Float _ | String _ => c
  | Cast c k t =>
      let c := f c
      with t := f t in
      make (Cast c k t)
  | Prod b c =>
      let b := binder_map f b
      with c := f c in
      make (Prod b c)
  | Lambda b c =>
      let b := binder_map f b
      with c := f c in
      make (Lambda b c)
  | LetIn b t c =>
      let b := binder_map f b
      with t := f t
      with c := f c in
      make (LetIn b t c)
  | App c l =>
      let c := f c
      with l := Array.map f l in
      make (App c l)
  | Evar e l =>
      let l := Array.map f l in
      make (Evar e l)
  | Case info x iv y bl =>
      let x := match x with (x,x') => (f x, x') end
      with iv := map_invert f iv
      with y := f y
      with bl := Array.map f bl in
      make (Case info x iv y bl)
  | Proj p r c =>
      let c := f c in
      make (Proj p r c)
  | Fix structs which tl bl =>
      let tl := Array.map (binder_map f) tl
      with bl := Array.map f bl in
      make (Fix structs which tl bl)
  | CoFix which tl bl =>
      let tl := Array.map (binder_map f) tl
      with bl := Array.map f bl in
      make (CoFix which tl bl)
  | Array u t def ty =>
      let ty := f ty
      with t := Array.map f t
      with def := f def in
      make (Array u t def ty)
  end.

(** [map_with_binders g f n c] maps [f n] on the immediate subterms of [c];
   it carries an extra data [n] (typically a lift index) which is processed by [g]
   (which typically add 1 to [n]) at each binder traversal;
   it is not recursive and the order with which subterms are processed is not specified. *)
Ltac2 map_with_binders (lift : 'a -> binder -> 'a) (f : 'a -> constr -> constr) (n : 'a) (c : constr) : constr :=
  match kind c with
  | Rel _ | Meta _ | Var _ | Sort _ | Constant _ _ | Ind _ _
  | Constructor _ _ | Uint63 _ | Float _ | String _ => c
  | Cast c k t =>
      let c := f n c
      with t := f n t in
      make (Cast c k t)
  | Prod b c =>
      let b := binder_map (f n) b
      with c := f (lift n b) c in
      make (Prod b c)
  | Lambda b c =>
      let b := binder_map (f n) b
      with c := f (lift n b) c in
      make (Lambda b c)
  | LetIn b t c =>
      let b := binder_map (f n) b
      with t := f n t
      with c := f (lift n b) c in
      make (LetIn b t c)
  | App c l =>
      let c := f n c
      with l := Array.map (f n) l in
      make (App c l)
  | Evar e l =>
      let l := Array.map (f n) l in
      make (Evar e l)
  | Case info x iv y bl =>
      let x := match x with (x,x') => (f n x, x') end
      with iv := map_invert (f n) iv
      with y := f n y
      with bl := Array.map (f n) bl in
      make (Case info x iv y bl)
  | Proj p r c =>
      let c := f n c in
      make (Proj p r c)
  | Fix structs which tl bl =>
      let tl := Array.map (binder_map (f n)) tl in
      let n_bl := Array.fold_left lift n tl in
      let bl := Array.map (f n_bl) bl in
      make (Fix structs which tl bl)
  | CoFix which tl bl =>
      let tl := Array.map (binder_map (f n)) tl in
      let n_bl := Array.fold_left lift n tl in
      let bl := Array.map (f n_bl) bl in
      make (CoFix which tl bl)
  | Array u t def ty =>
      let ty := f n ty
      with t := Array.map (f n) t
      with def := f n def in
      make (Array u t def ty)
  end.

End Unsafe.

Module Cast.

  Ltac2 @ external default : cast := "rocq-runtime.plugins.ltac2" "constr_cast_default".
  Ltac2 @ external vm : cast := "rocq-runtime.plugins.ltac2" "constr_cast_vm".
  Ltac2 @ external native : cast := "rocq-runtime.plugins.ltac2" "constr_cast_native".

  Ltac2 @ external equal : cast -> cast -> bool := "rocq-runtime.plugins.ltac2" "constr_cast_equal".

End Cast.

Ltac2 @ external in_context : ident -> constr -> (unit -> unit) -> constr := "rocq-runtime.plugins.ltac2" "constr_in_context".
(** On a focused goal [Γ ⊢ A], [in_context id c tac] evaluates [tac] in a
    focused goal [Γ, id : c ⊢ ?X] and returns [fun (id : c) => t] where [t] is
    the proof built by the tactic. *)

Module Pretype.
  Module Flags.
    Ltac2 Type t.

    Ltac2 @ external constr_flags : t := "rocq-runtime.plugins.ltac2" "constr_flags".
    (** The flags used by constr:(). *)

    Ltac2 @external set_use_coercions : bool -> t -> t
      := "rocq-runtime.plugins.ltac2" "pretype_flags_set_use_coercions".
    (** Use coercions during pretyping. [true] in [constr_flags]. *)

    Ltac2 @external set_use_typeclasses : bool -> t -> t
      := "rocq-runtime.plugins.ltac2" "pretype_flags_set_use_typeclasses".
    (** Run typeclass inference at the end of pretyping and when
        needed according to flag "Typeclass Resolution For Conversion".
        [true] in [constr_flags]. *)

    Ltac2 @external set_allow_evars : bool -> t -> t
      := "rocq-runtime.plugins.ltac2" "pretype_flags_set_allow_evars".
    (** Allow pretyping to produce new unresolved evars.
        [false] in [constr_flags]. *)

    Ltac2 @external set_nf_evars : bool -> t -> t
      := "rocq-runtime.plugins.ltac2" "pretype_flags_set_nf_evars".
    (** Evar-normalize the result of pretyping. This should not impact
        anything other than performance.
        [true] in [constr_flags]. *)

    Ltac2 Notation open_constr_flags_with_tc :=
      set_nf_evars false (set_allow_evars true constr_flags).

    Local Ltac2 open_constr_flags_with_tc_kn () := open_constr_flags_with_tc.
    (** Code generation uses this as using the notation is not convenient. *)

    Ltac2 Notation open_constr_flags_no_tc :=
      set_use_typeclasses false open_constr_flags_with_tc.
    (** The flags used by open_constr:() and its alias [']. *)

    #[deprecated(since="8.20", note="use open_constr_flags_with_tc (or open_constr_flags_no_tc as desired)")]
    Ltac2 Notation open_constr_flags := open_constr_flags_with_tc.
  End Flags.

  Ltac2 Type expected_type.

  Ltac2 @ external expected_istype : expected_type
    := "rocq-runtime.plugins.ltac2" "expected_istype".

  Ltac2 @ external expected_oftype : constr -> expected_type
    := "rocq-runtime.plugins.ltac2" "expected_oftype".

  Ltac2 @ external expected_without_type_constraint : expected_type
    := "rocq-runtime.plugins.ltac2" "expected_without_type_constraint".

  Ltac2 @ external pretype : Flags.t -> expected_type -> preterm -> constr
    := "rocq-runtime.plugins.ltac2" "constr_pretype".
  (** Pretype the provided preterm. Assumes the goal to be focussed. *)
End Pretype.

Ltac2 pretype (c : preterm) : constr :=
  Pretype.pretype Pretype.Flags.constr_flags Pretype.expected_without_type_constraint c.
(** Pretype the provided preterm. Assumes the goal to be focussed. *)

Ltac2 decompose_app_list (c : constr) :=
  match Unsafe.kind c with
    | Unsafe.App f cl => (f, Array.to_list cl)
    | _ => (c,[])
  end.

Ltac2 decompose_app (c : constr) :=
  match Unsafe.kind c with
    | Unsafe.App f cl => (f, cl)
    | _ => (c,[| |])
  end.

Ltac2 is_evar(c: constr) :=
  match Unsafe.kind c with
  | Unsafe.Evar _ _ => true
  | _ => false
  end.

Ltac2 @ external has_evar : constr -> bool := "rocq-runtime.plugins.ltac2" "constr_has_evar".

Ltac2 is_var(c: constr) :=
  match Unsafe.kind c with
  | Unsafe.Var _ => true
  | _ => false
  end.

Ltac2 is_fix(c: constr) :=
  match Unsafe.kind c with
  | Unsafe.Fix _ _ _ _ => true
  | _ => false
  end.

Ltac2 is_cofix(c: constr) :=
  match Unsafe.kind c with
  | Unsafe.CoFix _ _ _ => true
  | _ => false
  end.

Ltac2 is_ind(c: constr) :=
  match Unsafe.kind c with
  | Unsafe.Ind _ _ => true
  | _ => false
  end.

Ltac2 is_constructor(c: constr) :=
  match Unsafe.kind c with
  | Unsafe.Constructor _ _ => true
  | _ => false
  end.

Ltac2 is_proj(c: constr) :=
  match Unsafe.kind c with
  | Unsafe.Proj _ _ _ => true
  | _ => false
  end.

Ltac2 is_const(c: constr) :=
  match Unsafe.kind c with
  | Unsafe.Constant _ _ => true
  | _ => false
  end.

Ltac2 is_float(c: constr) :=
  match Unsafe.kind c with
  | Unsafe.Float _ => true
  | _ => false
  end.

Ltac2 is_uint63(c: constr) :=
  match Unsafe.kind c with
  | Unsafe.Uint63 _ => true
  | _ => false
  end.

Ltac2 is_string(c: constr) :=
  match Unsafe.kind c with
  | Unsafe.String _ => true
  | _ => false
  end.

Ltac2 is_array(c: constr) :=
  match Unsafe.kind c with
  | Unsafe.Array _ _ _ _ => true
  | _ => false
  end.

Ltac2 is_sort(c: constr) :=
  match Unsafe.kind c with
  | Unsafe.Sort _ => true
  | _ => false
  end.
