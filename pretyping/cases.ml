(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Disable warning 40: Constructor or label name used out of scope.
   (Type-directed constructor and label selection.) *)
[@@@ocaml.warning "-40"]

(** {5 Compilation of pattern-matching } *)

(** {6 Pattern-matching errors } *)
type pattern_matching_error =
  | BadPattern of Names.constructor * EConstr.constr
  | BadConstructor of Names.constructor * Names.inductive
  | WrongNumargConstructor of
      {cstr:Names.constructor; expanded:bool; nargs:int; expected_nassums:int; expected_ndecls:int}
  | WrongNumargInductive of
      {ind:Names.inductive; expanded:bool; nargs:int; expected_nassums:int; expected_ndecls:int}
  | UnusedClause of Glob_term.cases_pattern list
  | NonExhaustive of Glob_term.cases_pattern list
  | CannotInferPredicate of (EConstr.constr * EConstr.types) array

exception PatternMatchingError of
  Environ.env * Evd.evar_map * pattern_matching_error

let raise_pattern_matching_error ?loc (env,sigma,te) =
  Loc.raise ?loc (PatternMatchingError(env,sigma,te))

(*
let error_bad_constructor ?loc env cstr ind =
  raise_pattern_matching_error ?loc
    (env, Evd.empty, BadConstructor (cstr,ind))
*)

let error_wrong_numarg_constructor ?loc env ~cstr ~expanded ~nargs ~expected_nassums ~expected_ndecls =
  raise_pattern_matching_error ?loc (env, Evd.empty,
    WrongNumargConstructor {cstr; expanded; nargs; expected_nassums; expected_ndecls})

let error_wrong_numarg_inductive ?loc env ~ind ~expanded ~nargs ~expected_nassums ~expected_ndecls =
  raise_pattern_matching_error ?loc (env, Evd.empty,
    WrongNumargInductive {ind; expanded; nargs; expected_nassums; expected_ndecls})

let error_non_exhaustive ?loc env cases =
  raise_pattern_matching_error ?loc (env, Evd.empty, NonExhaustive cases)

let rec irrefutable env (pat : Glob_term.cases_pattern) =
  match DAst.get pat with
  | PatVar name -> true
  | PatCstr (cstr,args,_) ->
      let ind = Names.inductive_of_constructor cstr in
      let (_,mip) = Inductive.lookup_mind_specif env ind in
      let one_constr = Int.equal (Array.length mip.mind_user_lc) 1 in
      one_constr && List.for_all (irrefutable env) args

type compile_cases_typing_fun =
    Evardefine.type_constraint -> GlobEnv.t -> Evd.evar_map ->
      Glob_term.glob_constr -> Evd.evar_map * EConstr.unsafe_judgment

module type TypeS = sig
  type t
end

module Eq = struct
   type ('a, 'b) t = ('a, 'b) Util.eq = Refl : ('a, 'a) t

   let sym : type a b . (a, b) t -> (b, a) t = Util.sym

   let trans : type a b c . (a, b) t -> (b, c) t -> (a, c) t =
   fun Refl Refl -> Refl

   let ( ++ ) = trans

   let cast : type a b . (a, b) t -> a -> b = fun Refl -> Fun.id

   let option : type a b . (a, b) t -> (a option, b option) t = fun Refl -> Refl

   let list : type a b . (a, b) t -> (a list, b list) t = fun Refl -> Refl

   let array : type a b . (a, b) t -> (a array, b array) t = fun Refl -> Refl

   let pair : type a b c d . (a, b) t -> (c, d) t -> (a * c, b * d) t =
   fun Refl Refl -> Refl

   let t3 : type a b c d e f. (a, b) t -> (c, d) t -> (e, f) t ->
     (a * c * e, b * d * f) t =
   fun Refl Refl Refl -> Refl

   let ( ^* ) = pair

   let arrow : type a b c d. (a, b) t -> (c, d) t -> (a -> c, b -> d) t =
   fun Refl Refl -> Refl

   let ( ^-> ) = arrow

(*
   let endo eq = arrow eq eq
*)
end

module Phantom (Type : TypeS) : sig
  type 'a t

  val eq : ('a t, Type.t) Eq.t

  val transtype : ('a t, 'b t) Eq.t
end = struct
  type 'a t = Type.t

  let eq = Eq.Refl

  let transtype = Eq.Refl
end

module Phantom2 (Type : TypeS) : sig
  type ('a, 'b) t

  val eq : (('a, 'b) t, Type.t) Eq.t

  val transtype : (('a, 'b) t, ('c, 'd) t) Eq.t
end = struct
  type ('a, 'b) t = Type.t

  let eq = Eq.Refl

  let transtype = Eq.Refl
end

(*
module Phantom3 (Type : TypeS) : sig
  type ('a, 'b, 'c) t

(*
  val eq : (('a, 'b, 'c) t, Type.t) Eq.t

  val transtype : (('a, 'b, 'c) t, ('d, 'e, 'f) t) Eq.t
*)
end = struct
  type ('a, 'b, 'c) t = Type.t

(*
  let eq = Eq.Refl

  let transtype = Eq.Refl
*)
end
*)

module type Type1S = sig
  type 'a t
end

(*
module type Type2S = sig
  type ('a, 'b) t
end
*)

module type Type3S = sig
  type ('a, 'b, 'c) t
end

(*
module type Type4S = sig
  type ('a, 'b, 'c, 'd) t
end
*)

module type Type5S = sig
  type ('a, 'b, 'c, 'd, 'e) t
end

module PhantomPoly (Type : Type1S) : sig
  type ('a, 'b) t

  val eq : (('a, 'b) t, 'a Type.t) Eq.t

(*
  val transtype : (('a, 'b) t, ('a, 'c) t) Eq.t

  val morphism : ('a, 'b) Eq.t -> (('a, 'c) t, ('b, 'c) t) Eq.t
*)
end = struct
  type ('a, 'b) t = 'a Type.t

  let eq = Eq.Refl

(*
  let transtype = Eq.Refl

  let morphism : type a b c . (a, b) Eq.t -> ((a, c) t, (b, c) t) Eq.t =
    fun Refl -> Refl
*)
end

module Monad = struct
  module type S = sig
     type ('a, 'p) t

     module Ops : sig
       val return : 'a -> ('a, 'p) t

       val ( let* ) : ('a, 'p) t -> ('a -> ('b, 'p) t) -> ('b, 'p) t
     end
  end

  module Utils (M : S) = struct
    let eq :
    type a b p q . (a, b) Eq.t -> (p, q) Eq.t -> ((a, p) M.t, (b, q) M.t) Eq.t =
    fun Refl Refl -> Refl

(*
    let rec list_map : type a b p .
          (a -> (b, p) M.t) -> a list -> (b list, p) M.t =
    fun f l ->
      let open M.Ops in
      match l with
      | [] -> return []
      | h :: t ->
          let* h' = f h in
          let* t' = list_map f t in
          return (h' :: t')

    let option_map : type a b p .
          (a -> (b, p) M.t) -> a option -> (b option, p) M.t =
    fun f o ->
      let open M.Ops in
      match o with
      | None -> return None
      | Some x ->
          let* x' = f x in
          return (Some x')
*)
  end

  module Map = struct
    module Self = struct
      type ('a, _) t = 'a

      module Ops = struct
        let return x = x

        let ( let* ) x f = f x
      end
    end

    include Self

    include Utils (Self)
  end

  module OptionT (M : S) = struct
    module Self = struct
      type ('a, 'p) t = ('a option, 'p) M.t

      module Ops = struct
        let return x = M.Ops.return (Some x)

        let ( let* ) x f =
          let open M.Ops in
          let* x = x in
          match x with
          | None -> M.Ops.return None
          | Some x -> f x
      end
    end

    include Self

    include Utils (Self)
  end

  module Option = OptionT (Map)

  module StateT (M : S) = struct
    module Self = struct
      type ('a, 'state) t = 'state -> ('state * 'a, 'state) M.t

      module Ops = struct
       let return x s =
         M.Ops.return (s, x)

       let ( let* ) x f s =
         let open M.Ops in
         let* (s', x) = x s in
         f x s'
      end
    end

    include Self

    include Utils (Self)

    let get : type state . (state, state) t =
      fun state -> M.Ops.return (state, state)

    let set : type state . state -> (unit, state) t =
      fun new_state state -> M.Ops.return (new_state, ())
  end

  module State = struct
    include StateT (Map)

    let run : type state a . state -> (a, state) t -> state * a =
      fun state m -> m state

    let array_init : type a p . int -> (int -> (a, p) t) -> (a array, p) t =
    fun len f state ->
       let state_ref = ref state in
       let result =
         Array.init len (fun i ->
           let state, result = f i !state_ref in
           state_ref := state;
           result) in
       !state_ref, result

    let array_map : type a b p .
          (a -> (b, p) t) -> a array -> (b array, p) t =
    fun f a ->
      array_init (Array.length a) (fun i -> f (Array.unsafe_get a i))

(*
    let array_mapi : type a b p .
          (int -> a -> (b, p) t) -> a array -> (b array, p) t =
    fun f a ->
      array_init (Array.length a) (fun i -> f i (Array.unsafe_get a i))
*)
  end
end

(*
module Monoid = struct
  module type S = sig
    type 'a t

    val unit : 'a t

    val ( * ) : 'a t -> 'a t -> 'a t
  end

(*
  module List = struct
    type 'a t = 'a list

    let unit = []

    let ( * ) = ( @ )
  end
*)

(*
  module Exists = struct
    type 'a t = bool

    let unit = false

    let ( * ) = ( || )
  end
*)

  module Monad (M : S) = struct
    module Self = struct
      type ('a, 'p) t = 'a * 'p M.t

      module Ops = struct
        let return x = x, M.unit

        let ( let* ) (x, m) f =
          let y, m' = f x in
          y, M.(m * m')
      end

(*
      let push item = (), item
*)
    end

    include Self

    include Monad.Utils (Self)
  end
end
*)

module Nat = struct
  (* Constructors Zero and Succ are never used:
     they are here for injectivity. *)

  type zero = [`Zero]

  type 'a succ = [`Succ of 'a]

  type 'a t =
    | O : zero t
    | S : 'a t -> 'a succ t

  type one = zero succ

  let one : one t = S O

(*
  type two = one succ

  let two : two t = S one
*)

  let rec to_int : type a . ?add:int -> a t -> int  = fun ?(add = 0) a ->
    match a with
    | O -> add
    | S a -> to_int ~add:(succ add) a

  type exists = Exists : 'a t -> exists [@@ocaml.unboxed]

  let rec is_eq : type a b . a t -> b t -> (a, b) Eq.t option = fun n m ->
  match n, m with
  | O, O -> Some Refl
  | S n, S m ->
    begin match is_eq n m with
    | None -> None
    | Some Refl -> Some Refl
    end
  | _ -> None

  let of_int ?accu n =
    let rec aux : type a . a t -> int -> exists = fun accu n ->
      if n > 0 then
        aux (S accu) (pred n)
      else if n = 0 then
        Exists accu
      else
        assert false in
    match accu with
    | None -> aux O n
    | Some accu -> aux accu n

  type ('a, 'b, 'a_plus_b) plus =
    | Zero_l : (zero, 'a, 'a) plus
    | Succ_plus : ('a, 'b, 'c) plus -> ('a succ, 'b, 'c succ) plus

  let rec plus_to_int :
  type a b c. ?add:int -> (a, b, c) plus -> int  = fun ?(add = 0) a ->
    match a with
    | Zero_l -> add
    | Succ_plus a -> plus_to_int ~add:(succ add) a

  let rec plus_nat : type a b c . (a, b, c) plus -> b t -> c t =
  fun p b ->
    match p with
    | Zero_l -> b
    | Succ_plus p -> S (plus_nat p b)

(*
  let rec plus_l : type a b c . (a, b, c) plus -> a t =
  fun p ->
    match p with
    | Zero_l -> O
    | Succ_plus p -> S (plus_l p)
*)
  external plus_l : ('a, 'b, 'c) plus -> 'a t = "%identity"

  let rec plus_fun : type a b c c' .
        (a, b, c) plus -> (a, b, c') plus -> (c, c') Eq.t = fun p p' ->
    match p, p' with
    | Zero_l, Zero_l -> Refl
    | Succ_plus p, Succ_plus p' ->
        let Refl = plus_fun p p' in
        Refl

  type ('a, 'b) to_plus =
    Exists : ('a, 'b, 'a_plus_b) plus -> ('a, 'b) to_plus [@@ocaml.unboxed]
(*
  let rec to_plus : type a b . a t -> (a, b) to_plus = fun a ->
    match a with
    | O -> Exists Zero_l
    | S a ->
        let Exists a_plus_b = to_plus a in
        Exists (Succ_plus a_plus_b)
*)

  let to_plus : type a b . a t -> (a, b) to_plus = fun a ->
    Exists (Obj.magic a)

(*
  let rec plus_shift :
  type a b c d . (a, b, c) plus -> (a, d) to_plus = fun a ->
    match a with
    | Zero_l -> Exists Zero_l
    | Succ_plus a ->
        let Exists a_plus_b = plus_shift a in
        Exists (Succ_plus a_plus_b)
*)

  let plus_shift :
  type a b c d . (a, b, c) plus -> (a, d) to_plus = fun a ->
    Exists (Obj.magic a)

  type ('a, 'b) add =
    Exists : {
      sum : 'a_plus_b t;
      plus : ('a, 'b, 'a_plus_b) plus;
    } -> ('a, 'b) add

  let add (type a b) (a : a t) (b : b t) : (a, b) add =
    let Exists plus = to_plus a in
    Exists { sum = plus_nat plus b; plus }

  module Diff = struct
    type ('a, 'b) t =
      Exists : ('diff, 'b, 'a) plus -> ('a, 'b) t [@@ocaml.unboxed]

    let zero (type a) : (a, a) t = Exists Zero_l

    let succ (type a b) (Exists plus : (a, b) t) : (a succ, b) t =
      Exists (Succ_plus plus)

(*
    let to_nat (type a b) (Exists plus : (a, b) t) (b : b nat) : a nat =
      plus_nat plus b
*)
  end

  let pred : type a . a succ t -> a t = fun (S a) -> a

  module Ops = struct
    let ( + ) = add
  end
(*
  let rec plus_succ : type a b a_plus_b .
        (a, b, a_plus_b) plus -> (a, b succ, a_plus_b succ) plus = fun plus ->
    match plus with
    | Zero_l -> Zero_l
    | Succ_plus plus -> Succ_plus (plus_succ plus)
          *)

  external plus_succ :
      ('a, 'b, 'a_plus_b) plus -> ('a, 'b succ, 'a_plus_b succ) plus =
        "%identity"
(*
  let rec move_succ_left : type a b a_plus_b .
        (a, b succ, a_plus_b) plus -> (a succ, b, a_plus_b) plus = fun plus ->
    match plus with
    | Zero_l -> Succ_plus Zero_l
    | Succ_plus plus -> Succ_plus (move_succ_left plus)
*)
  let move_succ_left : type a b a_plus_b .
        (a, b succ, a_plus_b) plus -> (a succ, b, a_plus_b) plus = fun plus ->
          Obj.magic (Succ_plus plus)

(*
  let rec zero_r : type a . a t -> (a, zero, a) plus = fun a ->
    match a with
    | O -> Zero_l
    | S a -> Succ_plus (zero_r a)
*)

  external zero_r : 'a t -> ('a, zero, 'a) plus = "%identity"

  let zero_r_eq (type a b) (plus : (a, zero, b) plus) : (a, b) Eq.t =
    plus_fun (zero_r (plus_l plus)) plus

  let zero_l_eq (type a b) (Zero_l : (zero, a, b) plus) : (a, b) Eq.t =
    Refl
(*
  let rec plus_commut : type a b sum .
        b t -> (a, b, sum) plus -> (b, a, sum) plus = fun b plus ->
    match plus with
    | Zero_l -> zero_r b
    | Succ_plus plus -> plus_succ (plus_commut b plus)
*)
  let plus_commut : type a b sum .
        b t -> (a, b, sum) plus -> (b, a, sum) plus = fun b plus ->
    Obj.magic b

  let plus_one (type a) (a : a t) : (a, one, a succ) plus =
    plus_succ (zero_r a)

(*
  let rec inj_r : type a b b' c . (a, b, c) plus -> (a, b', c) plus ->
    (b, b') Eq.t =
  fun plus plus' ->
    match plus, plus' with
    | Zero_l, Zero_l -> Refl
    | Succ_plus plus, Succ_plus plus' ->
        let Refl = inj_r plus plus' in
        Refl
*)

(*
  let inj_l : type a a' b c . b t -> (a, b, c) plus -> (a', b, c) plus ->
    (a, a') Eq.t =
  fun b plus plus' ->
    inj_r (plus_commut b plus) (plus_commut b plus')
*)

  let rec plus_assoc_rec :
  type a b c x y z . (x, a, b) plus -> (y, b, c) plus ->
    (y, x, z) plus -> (z, a, c) plus =
  fun x y z ->
    match y, z with
    | Zero_l, Zero_l -> x
    | Succ_plus y, Succ_plus z ->
        Succ_plus (plus_assoc_rec x y z)

(*
  let plus_assoc (type a b c x y) (x : (x, a, b) plus) (y : (y, b, c) plus) :
      (c, a) Diff.t =
    let Exists z = plus_shift y in
    Exists (plus_assoc_rec x y z)
*)
end

(*
module Rank = struct
  type 'upper t =
    | O : _ t
    | S : 'a t -> 'a Nat.succ t
end
*)

module Fin = struct
  type 'a t =
    Exists : ('x, 'y Nat.succ, 'a) Nat.plus -> 'a t [@@ocaml.unboxed]

  let zero = Exists Nat.Zero_l

  let succ (Exists plus) = Exists (Succ_plus plus)

  let one = succ zero

  let to_int (Exists n) = Nat.to_int (Nat.plus_l n)

  let rec add : type n d m . (d, n, m) Nat.plus -> n t -> m t =
  fun plus n ->
    match plus with
    | Zero_l -> n
    | Succ_plus plus ->
        let Exists m = add plus n in
        Exists (Succ_plus m)
end

module Vector = struct
  type ('a, 'length, 'end_length) section =
    | [] : ('a, 'end_length, 'end_length) section
    | (::) :
        'a * ('a, 'length, 'end_length) section ->
          ('a, 'length Nat.succ, 'end_length) section

  type ('a, 'length) t = ('a, 'length, Nat.zero) section

  type 'a exists = Exists : ('a, 'length) t -> 'a exists [@@ocaml.unboxed]

  let eq (type a b) (Refl : (a, b) Eq.t) :
      ((a, 'length, 'end_length) section,
        (b, 'length, 'end_length) section) Eq.t =
    Refl

  let eq_length (type a b) (Refl : (a, b) Eq.t) :
      (('x, a) t, ('x, b) t) Eq.t = Refl

(*
  let rec make : type length . length Nat.t -> 'a -> ('a, length) t = fun n x ->
    match n with
    | O -> []
    | S n -> x :: make n x
*)

  let rec init_aux :
  type i l l' . i Nat.t -> l' Nat.t -> (i, l', l) Nat.plus ->
    (l Fin.t -> 'a) -> ('a, l') t =
  fun i l' diff f ->
    match l' with
    | O -> []
    | S l' ->
       f (Exists diff) :: init_aux (S i) l' (Nat.move_succ_left diff) f

  let init (type l) (l : l Nat.t) (f : l Fin.t -> 'a) : ('a, l) t =
    init_aux O l Zero_l f

  let rec of_list : type a . a list -> a exists = fun l ->
    match l with
    | [] -> Exists []
    | hd :: tl ->
        let Exists tl = of_list tl in
        Exists (hd :: tl)

  let rec of_list_of_length : type a length . a list -> length Nat.t ->
    (a, length) t option = fun l len ->
    let open Monad.Option.Ops in
    match l, len with
    | [], Nat.O -> return []
    | hd :: tl, Nat.S len ->
        let* tl = of_list_of_length tl len in
        return (hd :: tl)
    | _ -> None

(*
  let rec of_list_map : type a b . (a -> b) -> a list -> b exists = fun f l ->
    match l with
    | [] -> Exists []
    | hd :: tl ->
        let Exists tl = of_list_map f tl in
        Exists (f hd :: tl)
*)

  let rec to_list : type a length . (a, length) t -> a list = fun l ->
    match l with
    | [] -> []
    | hd :: tl -> hd :: to_list tl

  let to_array v = Array.of_list (to_list v)

  let rec length : type a length . (a, length) t -> length Nat.t = fun l ->
    match l with
    | [] -> O
    | _hd :: tl -> S (length tl)

(*
  let rec find : type length . ('a -> bool) -> ('a, length) t -> 'a = fun p l ->
    match l with
    | [] -> raise Not_found
    | hd :: tl ->
        if p hd then hd
        else find p tl
*)

  let rec find_opt : type length . ('a -> 'b option) -> ('a, length) t ->
    'b option = fun p l ->
    match l with
    | [] -> None
    | hd :: tl ->
        match p hd with
        | None -> find_opt p tl
        | x -> x

(*
  let exists (p : 'a -> bool) (v : ('a, 'length) t) : bool =
    find_opt (fun x -> if p x then Some () else None) v = Some ()
*)

  let rec findi_aux :
  type i l l' . i Nat.t -> l' Nat.t -> (i, l', l) Nat.plus ->
    (l Fin.t -> 'a -> 'b option) -> ('a, l') t -> 'b option =
  fun i l' diff f l ->
    match l, l' with
    | [], O -> None
    | hd :: tl, S l' ->
       match f (Exists diff) hd with
       | None -> findi_aux (S i) l' (Nat.move_succ_left diff) f tl
       | x -> x

  let findi (type l) (f : l Fin.t -> 'a -> 'b option) (l : ('a, l) t) :
      'b option =
    findi_aux O (length l) Zero_l f l

  let find_name (to_name : 'a -> Names.Name.t) vars : Names.Name.t =
    match find_opt (fun item ->
      match to_name item with Anonymous -> None | name -> Some name) vars with
    | None -> Anonymous
    | Some name -> name

  let rec iter : type length . ('a -> unit) -> ('a, length) t -> unit =
  fun f l ->
    match l with
    | [] -> ()
    | hd :: tl ->
        f hd;
        iter f tl

  let rec map : type length end_length .
        ('a -> 'b) -> ('a, length, end_length) section ->
          ('b, length, end_length) section =
  fun f l ->
    match l with
    | [] -> []
    | hd :: tl -> f hd :: map f tl

  let rec map2 : type length .
    ('a -> 'b -> 'c) -> ('a, length) t -> ('b, length) t -> ('c, length) t =
  fun f l1 l2 ->
    match l1, l2 with
    | [], [] -> []
    | hd1 :: tl1, hd2 :: tl2 -> f hd1 hd2 :: map2 f tl1 tl2

  let rec map_split : type length .
    ('a -> 'b * 'c) -> ('a, length) t -> ('b, length) t * ('c, length) t =
  fun f l ->
    match l with
    | [] -> [], []
    | hd :: tl ->
        let hd0, hd1 = f hd in
        let tl0, tl1 = map_split f tl in
        hd0 :: tl0, hd1 :: tl1

  let split v =
    map_split Fun.id v


  let join v v' =
    map2 (fun x x' -> x, x') v v'

  let rec map_rev_append : type l l0 l1 .
        ('a -> 'b) -> ('a, l0) t -> ('b, l1) t -> (l0, l1, l) Nat.plus ->
        ('b, l) t = fun f l0 l1 plus ->
    match l0, plus with
    | [], Zero_l -> l1
    | hd :: tl, Succ_plus plus ->
        map_rev_append f tl (f hd :: l1) (Nat.plus_succ plus)

  let rev_map : type l . ('a -> 'b) -> ('a, l) t -> ('b, l) t = fun f l ->
    map_rev_append f l [] (Nat.zero_r (length l))

  let rev : type l . ('a, l) t -> ('a, l) t = fun l ->
    rev_map Fun.id l

  let rev_append_plus : type l l0 l1 .
      ('a, l0) t -> ('b, l1) t -> (l0, l1, l) Nat.plus -> ('a, l) t =
  fun l0 l1 plus ->
    map_rev_append Fun.id l0 l1 plus

  let append_plus : type l l0 l1 .
      ('a, l0) t -> ('a, l1) t -> (l0, l1, l) Nat.plus -> ('a, l) t =
  fun l0 l1 plus ->
    rev_append_plus (rev l0) l1 plus

  let map_append_plus : type l l0 l1 .
      ('a -> 'b) -> ('a, l0) t -> ('b, l1) t -> (l0, l1, l) Nat.plus ->
        ('b, l) t =
  fun f l0 l1 plus ->
    map_rev_append f (rev l0) l1 plus

  type ('a, 'l0, 'l1) append = Exists : {
      vector : ('a, 'l) t;
      plus : ('l0, 'l1, 'l) Nat.plus;
    } -> ('a, 'l0, 'l1) append

  let rev_append : type l0 l1 .
      ('a, l0) t -> ('a, l1) t -> ('a, l0, l1) append =
  fun l0 l1 ->
    let Exists plus = Nat.to_plus (length l0) in
    Exists { vector = map_rev_append Fun.id l0 l1 plus; plus }

  let append : type l0 l1 .
      ('a, l0) t -> ('a, l1) t -> ('a, l0, l1) append =
  fun l0 l1 ->
    rev_append (rev l0) l1

  let rec append_section : type l0 l1 l2 .
      ('a, l0, l1) section -> ('a, l1, l2) section -> ('a, l0, l2) section =
   fun l0 l1 ->
     match l0 with
     | [] -> l1
     | hd :: tl -> hd :: append_section tl l1

  let rec mapi_aux :
  type i l l' . i Nat.t -> l' Nat.t -> (i, l', l) Nat.plus ->
    (l Fin.t -> 'a -> 'b) -> ('a, l') t -> ('b, l') t =
  fun i l' diff f l ->
    match l, l' with
    | [], O -> []
    | hd :: tl, S l' ->
       f (Exists diff) hd :: mapi_aux (S i) l'
         (Nat.move_succ_left diff) f tl

  let mapi (type l) (f : l Fin.t -> 'a -> 'b) (l : ('a, l) t) : ('b, l) t =
    mapi_aux O (length l) Zero_l f l

(*
  let rec filter_map : type length . ('a -> 'b option) -> ('a, length) t ->
    'b exists =
  fun f l ->
    match l with
    | [] -> Exists []
    | hd :: tl ->
        let tl = filter_map f tl in
        match f hd with
        | None -> tl
        | Some hd ->
            let Exists tl = tl in
            Exists (hd :: tl)
*)

  let rec cut : type l l' l'' . (l, l', l'') Nat.plus -> ('a, l'') t ->
    ('a, l) t * ('a, l') t =
  fun plus v ->
    match plus with
    | Zero_l -> [], v
    | Succ_plus plus ->
        let hd :: tl = v in
        let left, right = cut plus tl in
        hd :: left, right

  let rec get_aux : type i l l' .
    (i, l' Nat.succ, l) Nat.plus -> ('a, l) t -> 'a =
  fun plus l ->
    match plus, l with
    | Zero_l, hd :: _ -> hd
    | Succ_plus plus, _ :: tl ->
        get_aux plus tl
    | _ -> .

  module Ops = struct
    let (.%()) (type l) (l : ('a, l) t) (Exists plus : l Fin.t) : 'a =
      get_aux plus l

    let ( @ ) l0 l1 = append l0 l1
  end

(*
  let rec for_all : type length . ('a -> bool) -> ('a, length) t -> bool =
  fun p l ->
    match l with
    | [] -> true
    | hd :: tl -> p hd && for_all p tl
*)

  module UseMonad (M : Monad.S) = struct
(*
    let rec iter : type length a p .
          (a -> (unit, p) M.t) -> (a, length) t -> (unit, p) M.t =
    fun f v ->
      let open M.Ops in
      match v with
      | [] -> return ()
      | h :: t ->
          let* () = f h in
          iter f t
*)

    let rec map : type length a b p .
          (a -> (b, p) M.t) -> (a, length) t ->
            ((b, length) t, p) M.t =
    fun f v ->
      let open M.Ops in
      match v with
      | [] -> return []
      | h :: t ->
          let* h' = f h in
          let* t' = map f t in
          return (h' :: t')

    let rec mapi_aux :
    type i l l' . i Nat.t -> l' Nat.t -> (i, l', l) Nat.plus ->
      (l Fin.t -> 'a -> ('b, 'p) M.t) -> ('a, l') t -> (('b, l') t, 'p) M.t =
    fun i l' diff f l ->
      let open M.Ops in
      match l, l' with
      | [], O -> return []
      | hd :: tl, S l' ->
          let* h' = f (Exists diff) hd in
          let* t' = mapi_aux (S i) l' (Nat.move_succ_left diff) f tl in
          return (h' :: t')

    let mapi (type l) (f : l Fin.t -> 'a -> ('b, 'p) M.t) (l : ('a, l) t) :
        (('b, l) t, 'p) M.t =
      mapi_aux O (length l) Zero_l f l
  end

  type ('x, 'size_a, 'a, 'b) replace = Exists : {
      section : ('x, 'size_b, 'b) section;
      diff_a : ('diff, 'a, 'size_a) Nat.plus;
      diff_b : ('diff, 'b, 'size_b) Nat.plus;
    } -> ('x, 'size_a, 'a, 'b) replace

  let rec replace :
  type size a b . ('x, size, a) section -> ('x, size, a, b) replace =
  fun v ->
    match v with
    | [] -> Exists { section = []; diff_a = Zero_l; diff_b = Zero_l }
    | hd :: tl ->
        let Exists tl = replace tl in
        Exists { section = hd :: tl.section;
          diff_a = Succ_plus tl.diff_a;
          diff_b = Succ_plus tl.diff_b }

end

module Env = struct
  include Phantom (struct type t = Environ.env end)

(*
  let pair :
    type a b c d . (a t, b t) Eq.t -> (c t, d t) Eq.t ->
      ((a * c) t, (b * d) t) Eq.t = fun _ _ -> transtype
*)

  let zero_l : type env . ((Nat.zero * env) t, env t) Eq.t = transtype

  let zero_r : type env . ((env * Nat.zero) t, env t) Eq.t = transtype

  let succ : type a . ((a * Nat.one) t, a Nat.succ t) Eq.t = transtype

  let rev_succ : type a . ((Nat.one * a) t, a Nat.succ t) Eq.t = transtype

  let assoc : type a b c . (((a * b) * c) t, (a * (b * c)) t) Eq.t = transtype

(*
  let commut : type a b . ((a * b) t, (b * a) t) Eq.t = transtype
*)

  let morphism : type a b c d .
    (a t, b t) Eq.t -> (c t, d t) Eq.t -> ((a * c) t, (b * d) t) Eq.t =
  fun _ _ -> transtype

  let plus :
    type a b . (a, b, 'c) Nat.plus -> ((a * b) t, 'c t) Eq.t =
  fun _ -> transtype

  let rev_plus :
    type a b . (a, b, 'c) Nat.plus -> ((b * a) t, 'c t) Eq.t =
  fun _ -> transtype

(*
  let inj_l :
    type a b c . ((a * c) t, (b * c) t) Eq.t -> (a t, b t) Eq.t =
  fun _ -> transtype

  let inj_r :
    type a b c . ((a * b) t, (a * c) t) Eq.t -> (b t, c t) Eq.t =
  fun _ -> transtype
*)

  let plus_succ :
  type a b . unit -> ((a * b) Nat.succ t, (a * b Nat.succ) t) Eq.t =
  fun () -> Eq.(sym succ ++ assoc ++ morphism Refl succ)

  let print (env : 'env t) : Pp.t =
    Termops.Internal.print_env (Eq.cast eq env)
  [@@ocaml.warning "-32"] (* can be unused *)
end

module Height = struct
  include Phantom (struct type t = int end)

  type ('a, 'b) eq = ('a Env.t, 'b Env.t) Eq.t

  let morphism (type a b) (_ : (a Env.t, b Env.t) Eq.t) : (a t, b t) Eq.t =
    transtype

  let zero : Nat.zero t = Eq.cast (Eq.sym eq) 0

  let one : (Nat.one) t = Eq.cast (Eq.sym eq) 1

  let add (type a b) (a : a t) (b : b t) : (a * b) t =
    Eq.cast (Eq.sym eq) (Eq.cast eq a + Eq.cast eq b)

  module Ops = struct
    let ( + ) = add
  end

  let succ (type a) (a : a t) : (a Nat.succ) t =
    Eq.cast (Eq.sym eq) (succ (Eq.cast eq a))

  let of_nat : type n . n Nat.t -> n t = fun n ->
    Eq.cast (Eq.sym eq) (Nat.to_int n)

  let of_plus : type n . (n, _, _) Nat.plus -> n t = fun n ->
    Eq.cast (Eq.sym eq) (Nat.plus_to_int n)

(*
  let is_eq (type a b) (a : a t) (b : b t) : (a Env.t, b Env.t) Eq.t option =
    if Eq.cast eq a = Eq.cast eq b then
      Some Env.transtype
    else
      None
*)

  type 'n to_nat = Exists : {
    nat : 'm Nat.t;
    eq : ('m Env.t, 'n Env.t) Eq.t;
    } -> 'n to_nat

  let to_nat : type n . n t -> n to_nat = fun n ->
    let n = Eq.cast eq n in
    let Exists nat = Nat.of_int n in
    Exists { nat; eq = Env.transtype }

  let to_int n =
    Eq.cast eq n
  [@@ocaml.warning "-32"] (* can be unused *)

  type ('a, 'b) diff = Exists : {
      diff : 'diff t;
      plus : (('diff * 'b) Env.t, 'a Env.t) Eq.t;
    } -> ('a, 'b) diff

  let diff_zero : type a . (a, a) diff = Exists {
      diff = zero;
      plus = Env.zero_l;
    }

  let diff_add (type a b c) (a : a t) (Exists b : (b, c) diff) :
      (a * b, c) diff = Exists {
      diff = add a b.diff;
      plus = Eq.trans Env.assoc (Env.morphism Refl b.plus);
    }

(*
  type ('a, 'b) sub = Exists : {
      diff : 'diff t;
      plus : (('b * 'diff) Env.t, 'a Env.t) Eq.t;
    } -> ('a, 'b) sub

  let sub (type a b) (a : a t) (b : b t) : (a, b) sub =
    Exists {
      diff = Eq.(cast (sym (eq ^-> eq ^-> eq))) (-) a b;
      plus = Env.transtype;
  }
*)

  let env (type env h) (h : h t) (env : (env * h) Env.t) : env Env.t =
    Eq.(cast (sym (eq ^-> Env.eq ^-> Env.eq))) Environ.env_of_rel h env

  module Vector = struct
    type ('a, 'height) t =
      | Exists : {
        vector : ('a, 'length) Vector.t;
        eq : ('height, 'length) eq;
      } -> ('a, 'height) t

(*
    let morphism (type a h h') (eq' : (h, h') eq) (v : (a, h) t) :
        (a, h') t =
      let Exists { vector; eq } = v in
      Exists { vector; eq = Eq.(sym eq' ++ eq) }
*)

    let of_vector vector = Exists { vector; eq = Refl }

    let map f (Exists { vector; eq }) =
      Exists { vector = Vector.map f vector; eq }

    let rev (Exists {vector; eq }) =
      Exists { vector = Vector.rev vector; eq }

    let to_list (Exists { vector; _ }) =
      Vector.to_list vector
    [@@ocaml.warning "-32"]
  end
end

module Index = struct
  include Phantom (struct type t = int end)

  let morphism (type a b) (_ : (a, b) Height.eq) : (a t, b t) Eq.t =
    transtype

  let zero (type n) () : n Nat.succ t =
    Eq.(cast (sym eq)) 0

  let succ (type n) (n : n t) : n Nat.succ t =
    Eq.(cast (sym (eq ^-> eq))) succ n

  let to_int (type n) (n : n t) : int =
    Eq.cast eq n

  let of_fin (type env n) (n : n Fin.t) : (env * n) t =
    Eq.(cast (sym eq)) (Fin.to_int n)
(*
  let equal (type env) (a : env t) (b : env t) : bool =
    Eq.(cast (sym (eq ^-> eq ^-> Refl))) Int.equal a b
*)
(*
  let compare (type env) (a : env t) (b : env t) : int =
    Eq.(cast (sym (eq ^-> eq ^-> Refl))) Int.compare a b
*)
end

module Tuple = struct
  include PhantomPoly (struct type 'a t = 'a array end)

  module Ops = struct
    let (.%()) (type length) (tuple : ('a, length) t) (index : length Index.t) =
      Array.unsafe_get (Eq.cast eq tuple) (Eq.cast Index.eq index)

    let (.%()<-) (type length) (tuple : ('a, length) t)
        (index : length Index.t) (value : 'a) =
      Array.unsafe_set (Eq.cast eq tuple) (Eq.cast Index.eq index) value
  end

  let length (type length) (t : ('a, length) t) : length Height.t =
    Eq.cast (Eq.sym (Eq.arrow eq Height.eq)) Array.length t

(*
  let make (l : 'length Height.t) (default : 'a) : ('a, 'length) t =
    Eq.cast Eq.(sym (Height.eq ^-> Refl ^-> eq)) Array.make l default
*)

  let init (l : 'length Height.t) (f : 'length Index.t -> 'a) :
    ('a, 'length) t =
    Eq.(cast (sym (Height.eq ^-> (Index.eq ^-> Refl) ^-> eq))) Array.init l f

  let iter (t : ('a, 'length) t) (f : 'length Index.t -> unit) : unit =
    for i = 0 to Array.length (Eq.cast eq t) - 1 do
      f (Eq.cast (Eq.sym Index.eq) i)
    done
(*
  let map (f : ('a -> 'b)) (t : ('a, 'length) t) : ('b, 'length) t =
    Eq.(cast (sym (Refl ^-> eq ^-> eq))) Array.map f t
*)
(*
  type 'a exists = Exists : ('a, 'length) t -> 'a exists
*)

  module State = struct
    let map : type a b p l .
          (a -> (b, p) Monad.State.t) -> (a, l) t ->
            ((b, l) t, p) Monad.State.t =
    fun f t ->
      Eq.(cast (sym (eq ^-> Monad.State.eq eq Refl)))
        (Monad.State.array_map f) t

(*
    let mapi : type a b p l .
          (l Index.t -> a -> (b, p) Monad.State.t) -> (a, l) t ->
            ((b, l) t, p) Monad.State.t =
    fun f t ->
      Eq.(cast (sym
          ((Index.eq ^-> Refl ^-> Refl) ^-> eq ^-> Monad.State.eq eq Refl)))
        Monad.State.array_mapi f t
*)
  end
end

module type Type = sig
  type t
end

module InductiveDef = struct
  include Phantom (struct type t = Names.inductive end)

  let equal (type ind ind') (ind : ind t) (ind' : ind' t) :
      (ind t, ind' t) Eq.t option =
    if Names.Ind.CanOrd.equal (Eq.cast eq ind) (Eq.cast eq ind') then
      Some transtype
    else
      None
end

module type ConcreteTermS = sig
  type t

  type rel_declaration = (t, t) Context.Rel.Declaration.pt

  type rel_context = (t, t) Context.Rel.pt

  val exliftn : Esubst.lift -> t -> t

  val mkRel : int -> t

  val mkProp : t

  val mkInd : Names.inductive -> t

  val mkApp : t * t array -> t

  val mkLambda : Names.Name.t Context.binder_annot * t * t -> t

  val mkProd : Names.Name.t Context.binder_annot * t * t -> t

  val it_mkProd_or_LetIn : t -> rel_context -> t

  val it_mkLambda_or_LetIn : t -> rel_context -> t

  val subst_of_rel_context_instance : rel_context -> t array -> t list

  val substnl : t list -> int -> t -> t

  val substl : t list -> t -> t
end

module type ConcreteLiftableS = sig
  module Phantom : Type5S

  module Concrete : TypeS

  val unsafe_map :
      (Concrete.t -> Concrete.t) ->
        ('a, 'p, 'q, 'r, 's) Phantom.t -> ('b, 'p, 'q, 'r, 's) Phantom.t

  val exliftn : Esubst.lift -> Concrete.t -> Concrete.t
end

module Lift = struct
  include Phantom2 (struct type t = Esubst.lift end)

  let morphism (type a b a' b') (_ : (a, a') Height.eq) (_ : (b, b') Height.eq)
    : ((a, b) t, (a', b') t) Eq.t = transtype

  let of_eq (type a b) (_ : (a, b) Height.eq) : (a, b) t =
    Eq.(cast (sym eq)) Esubst.el_id

  let id (type a) () : (a, a) t = of_eq Refl

  let shift (type n a b) (n : n Height.t) (l : (a * n, b) t) : (a, b) t =
    Eq.(cast (sym (Height.eq ^-> eq ^-> eq))) Esubst.el_shft n l

  let ( & ) = shift

  let ( ~+ ) a = a & id ()

  let liftn (type n a b) (n : n Height.t) (l : (a, b) t) : (a * n, b * n) t =
    Eq.(cast (sym (Height.eq ^-> eq ^-> eq))) Esubst.el_liftn n l

  let rec unsafe_comp (l : Esubst.lift) (l' : Esubst.lift) : Esubst.lift =
    match l' with
    | ELID -> l
    | ELSHFT (l', i) -> Esubst.el_shft i (unsafe_comp l l')
    | ELLFT (i, l') -> Esubst.el_liftn i (unsafe_comp l l')

  let comp (type a b c) (l : (b, c) t) (l' : (a, b) t) : (a, c) t =
    Eq.(cast (sym (eq ^-> eq ^-> eq))) unsafe_comp l l'
end

module type LiftableS = sig
  type ('env, 'p, 'q, 'r, 's) t

  val exliftn : ('a, 'b) Lift.t -> ('a, 'p, 'q, 'r, 's) t ->
      ('b, 'p, 'q, 'r, 's) t

  val liftn : 'n Height.t -> 'm Height.t -> ('env * 'm, 'p, 'q, 'r, 's) t ->
      (('env * 'n) * 'm, 'p, 'q, 'r, 's) t

  val lift :
      'n Height.t -> ('env, 'p, 'q, 'r, 's) t -> ('env * 'n, 'p, 'q, 'r, 's) t
end

module Liftable (X : ConcreteLiftableS) :
    LiftableS with
type ('env, 'p, 'q, 'r, 's) t := ('env, 'p, 'q, 'r, 's) X.Phantom.t =
  struct
  let exliftn (type a b)
      (el : (a, b) Lift.t) (term : (a, 'p, 'q, 'r, 's) X.Phantom.t) :
      (b, 'p, 'q, 'r, 's) X.Phantom.t =
    match Eq.cast Lift.eq el with
    | ELID -> X.unsafe_map Fun.id term
    | el -> X.unsafe_map (X.exliftn el) term

  let liftn (type env n m)
      (n : n Height.t) (m : m Height.t)
      (term : (env * m, 'p, 'q, 'r, 's) X.Phantom.t) :
      ((env * n) * m, 'p, 'q, 'r, 's) X.Phantom.t =
    exliftn Lift.(liftn m (+ n)) term

  let lift (type env n) (n : n Height.t)
      (term : (env, 'p, 'q, 'r, 's) X.Phantom.t) :
      (env * n, 'p, 'q, 'r, 's) X.Phantom.t =
    exliftn Lift.(+ n) term
end

module Constructor = struct
  include Phantom (struct type t = Names.constructor end)

  type exists = Exists : 'ind t -> exists

  let of_concrete (cstr : Names.constructor) : exists =
    Exists (Eq.cast (Eq.sym eq) cstr)

  let to_concrete cstr =
    Eq.cast eq cstr

  let inductive (cstr : 'ind t) : 'ind InductiveDef.t =
    Eq.cast (Eq.sym (Eq.arrow eq InductiveDef.eq))
      Names.inductive_of_constructor cstr

  let index (cstr : 'ind t) : 'ind Index.t =
    Eq.cast (Eq.sym (Eq.arrow eq Index.eq))
      (fun c -> pred (Names.index_of_constructor c)) cstr

  let make (ind : 'ind InductiveDef.t) (i : 'ind Index.t) : 'ind t =
    Eq.(cast (sym (InductiveDef.eq ^-> Refl ^-> eq)))
      Names.ith_constructor_of_inductive ind (succ (Index.to_int i))

  let morphism (_ : ('ind InductiveDef.t, 'ind' InductiveDef.t) Eq.t) :
      ('ind t, 'ind' t) Eq.t =
    transtype

  let equal (cstr : _ t) (cstr' : _ t) : bool =
    Eq.(cast (sym (eq ^-> eq ^-> Refl))) Names.Construct.CanOrd.equal
      cstr cstr'

  let error_bad ?loc env cstr ind =
    raise_pattern_matching_error ?loc
      (Eq.cast Env.eq env, Evd.empty,
        BadConstructor (Eq.cast eq cstr, Eq.cast InductiveDef.eq ind))

  let error_wrong_numarg ?loc env ~cstr ~expanded ~nargs
      ~expected_nassums ~expected_ndecls =
    let cstr = Eq.cast eq cstr in
    raise_pattern_matching_error ?loc (Eq.cast Env.eq env, Evd.empty,
      WrongNumargConstructor
        {cstr; expanded; nargs; expected_nassums; expected_ndecls})
end

module Rel = struct
  include Index

  let unsafe_of_concrete (type env) (x : int) : env t =
    Eq.(cast (sym eq)) (pred x)

(*
  let to_concrete (type env) (x : env t) =
    Stdlib.succ (Eq.(cast eq) x)
*)

  let exliftn (type a b) (el : (a, b) Lift.t) (x : a t) : b t =
    Eq.(cast (sym eq)) (pred (Esubst.reloc_rel (Stdlib.succ (Eq.cast eq x))
      (Eq.cast Lift.eq el)))

  let lift (type n env) (n : n Height.t) (x : env t) : (env * n) t =
    Eq.(cast (sym (Height.eq ^-> eq ^-> eq))) (+) n x

(*
  let liftn (type n m env) (n : n Height.t) (m : m Height.t) (x : (env * m) t) :
      ((env * n) * m) t =
    let unsafe_liftn n m x =
      if x < m then
        x
      else
        n + x in
    Eq.(cast (sym (Height.eq ^-> Height.eq ^-> eq ^-> eq))) unsafe_liftn n m x
*)
(*
  let is_above (type env n) (n : n Height.t) (x : (env * n) t) :
      (env t, n t) result =
    let x = Eq.cast eq x in
    let n = Eq.cast Height.eq n in
    if x >= n then
      Ok (Eq.(cast (sym eq)) (x - n))
    else
      Error (Eq.(cast (sym eq)) x)
*)
  let of_height (type env h) (h : h Nat.succ Height.t) :
      (env * h Nat.succ) t =
    unsafe_of_concrete (Eq.cast Height.eq h)
(*
  let extend (type env n) (n : n t) : (env * n) t =
    Eq.cast transtype n
*)
  type 'env to_height = Exists : {
    height : 'h Height.t;
    eq : (('env' * 'h), 'env) Height.eq
  } -> 'env to_height

  let to_height (type env) (r : env t) : env to_height =
    Exists {
      height = Eq.(cast (sym Height.eq)) (Stdlib.succ (Eq.cast eq r));
      eq = Env.transtype;
  }
end

module type AbstractTermS = sig
  module Concrete : ConcreteTermS

  type 'a t

  val eq : ('a t, Concrete.t) Eq.t

  val morphism : ('a Env.t, 'b Env.t) Eq.t -> ('a t, 'b t) Eq.t

  include LiftableS with type ('env, 'p, 'q, 'r, 's) t := 'env t

  val mkRel : 'a Rel.t -> 'a t

  val mkReln : 'i Rel.t -> 'n Height.t -> ('i * 'n) t

  val mkProp : unit -> 'a t

  val mkInd : 'ind InductiveDef.t -> 'env t

  val mkApp : 'env t -> 'env t array -> 'env t

  val mkLambda :
      Names.Name.t Context.binder_annot -> 'env t -> 'env Nat.succ t -> 'env t

  val mkProd :
      Names.Name.t Context.binder_annot -> 'env t -> 'env Nat.succ t -> 'env t

  val substnl :
      ('env t, 'l) Height.Vector.t -> 'n Height.t -> (('env * 'l) * 'n) t ->
        ('env * 'n) t

  val substl : ('env t, 'l) Height.Vector.t -> ('env * 'l) t -> 'env t
end

module AbstractTerm (X : ConcreteTermS) :
    AbstractTermS with module Concrete = X = struct
  module Concrete = X

  include Phantom (struct type t = X.t end)

  let morphism (type a b) (_ : (a Env.t, b Env.t) Eq.t) :
      (a t, b t) Eq.t =
    transtype

  include Liftable (struct
    module Phantom = struct type nonrec ('a, 'p, 'q, 'r, 's) t = 'a t end
    module Concrete = X
    let unsafe_map f =
      Eq.(cast (sym (eq ^-> eq))) f
    let exliftn = X.exliftn
  end)

  let mkRel (i : 'env Index.t) : 'env t =
    Eq.(cast (sym eq)) (X.mkRel (succ (Eq.cast Index.eq i)))

  let mkReln (i : 'i Index.t) (n : 'n Height.t) : ('i * 'n) t =
    Eq.(cast (sym eq))
      (X.mkRel (succ (Eq.cast Index.eq i + Eq.cast Height.eq n)))

  let mkProp () : 'env t = Eq.cast (Eq.sym eq) X.mkProp

  let mkInd (ind : 'ind InductiveDef.t) : 'env t =
    Eq.cast (Eq.sym (Eq.arrow InductiveDef.eq eq)) X.mkInd ind

  let mkApp (f : 'env t) (args : 'env t array) : 'env t =
    Eq.cast (Eq.sym eq) (X.mkApp (Eq.cast eq f, Eq.cast (Eq.array eq) args))

  let mkLambda (type env) name (ty : env t) (body : env Nat.succ t) : env t =
    Eq.(cast (sym ((t3 Refl eq eq) ^-> eq))) X.mkLambda (name, ty, body)

  let mkProd (type env) name (ty : env t) (body : env Nat.succ t) : env t =
    Eq.(cast (sym ((t3 Refl eq eq) ^-> eq))) X.mkProd (name, ty, body)

  let substnl (type env n length)
      (Exists substl : (env t, length) Height.Vector.t)
      (n : n Height.t) (t : ((env * length) * n) t) : (env * n) t =
    Eq.(cast (sym (Eq.list eq ^-> Height.eq ^-> eq ^-> eq)))
      X.substnl (Vector.to_list substl.vector) n t

  let substl (type env length) (Exists substl : (env t, length) Height.Vector.t)
      (t : (env * length) t) : env t =
    Eq.(cast (sym (Eq.list eq ^-> eq ^-> eq)))
      X.substl (Vector.to_list substl.vector) t
end

module Term = struct
  include AbstractTerm (struct
    include Constr

    include Term

    include Vars
  end)

(*
  let lookup (type env) (env : env Env.t) (variable : Names.Id.t) : env t =
    Eq.(cast (sym eq))
      (Context.Named.Declaration.get_type
        (Environ.lookup_named variable (Eq.cast (Env.eq) env)))
*)
end

module ETerm = struct
  include AbstractTerm (struct
    include EConstr

    include Vars

    let exliftn el t =
      of_constr (Constr.exliftn el (Evd.MiniEConstr.unsafe_to_constr t))
  end)

  let mkIndU (ind : 'ind InductiveDef.t) instance : 'env t =
    Eq.(cast (sym ((InductiveDef.eq ^* Refl) ^-> eq)))
      EConstr.mkIndU (ind, instance)

  let whd_all (type env) (env : env Env.t) sigma (term : env t) =
    Eq.(cast (sym (Env.eq ^-> Refl ^-> eq ^-> eq)))
      Reductionops.whd_all env sigma term

  let nf_all (type env) (env : env Env.t) sigma (term : env t) =
    Eq.(cast (sym (Env.eq ^-> Refl ^-> eq ^-> eq)))
      Reductionops.nf_all env sigma term
  [@@ocaml.warning "-32"] (* can be unused *)

  let nf_zeta (type env) (env : env Env.t) sigma (term : env t) =
    Eq.(cast (sym (Env.eq ^-> Refl ^-> eq ^-> eq)))
      Reductionops.nf_all env sigma term
  [@@ocaml.warning "-32"] (* can be unused *)

(*
  let noccur_between sigma n m (term : 'env t) : bool =
    EConstr.Vars.noccur_between sigma n m (Eq.cast eq term)
*)

  let of_term (t : 'env Term.t) : 'env t =
    Eq.(cast (sym (Term.eq ^-> eq))) EConstr.of_constr t

  let mkSort (s : Sorts.t) : 'env t =
    Eq.(cast (sym (Refl ^-> eq))) EConstr.mkSort s

  let print (env : 'env Env.t) sigma (term : 'env t) : Pp.t =
    Eq.(cast (sym (Env.eq ^-> Refl ^-> eq ^-> Refl)))
      Termops.Internal.print_constr_env env sigma term
  [@@ocaml.warning "-32"] (* can be unused *)

  let debug_print (term : 'env t) : Pp.t =
    Termops.Internal.debug_print_constr (Eq.cast eq term)
  [@@ocaml.warning "-32"] (* can be unused *)

  let retype_of (type env) (env : env Env.t) sigma (term : env t) : env t =
    Eq.(cast (sym (Env.eq ^-> Refl ^-> eq ^-> eq)))
      Retyping.get_type_of env sigma term

(*
  let get_type_of (type env) (env : env Env.t) (term : env t) : Evd.evar_map -> Evd.evar_map * env t =
    fun sigma ->
    Eq.(cast (sym (Env.eq ^-> Refl ^-> eq ^-> Refl ^* eq)))
      Typing.type_of env sigma term
*)

(*
  type 'env decompose_1 = {
      name : Names.Name.t Context.binder_annot;
      ty : 'env t;
      t : ('env Nat.succ) t;
    }

  let rec decompose_lam_1 : type env . Evd.evar_map -> env t ->
      env decompose_1 =
  fun sigma t ->
    match EConstr.kind sigma (Eq.cast eq t) with
    | Lambda (name, ty, t) ->
        { name; ty = Eq.(cast (sym eq)) ty; t = Eq.(cast (sym eq)) t }
    | Cast (c, _, _) -> decompose_lam_1 sigma (Eq.(cast (sym eq)) c)
    | _ -> failwith "decompose_lam_1: not an abstraction"

  let rec decompose_prod_1 : type env . Evd.evar_map -> env t ->
      env decompose_1 =
  fun sigma t ->
    match EConstr.kind sigma (Eq.cast eq t) with
    | Prod (name, ty, t) ->
        { name; ty = Eq.(cast (sym eq)) ty; t = Eq.(cast (sym eq)) t }
    | Cast (c, _, _) -> decompose_prod_1 sigma (Eq.(cast (sym eq)) c)
    | _ -> failwith "decompose_prod_1: not an assumption"
*)


  let destRel (type env) sigma (t : env t) : env Rel.t option =
    match EConstr.kind sigma (Eq.cast eq t) with
    | Rel p -> Some (Rel.unsafe_of_concrete p)
    | _ -> None

  let destApp (type env) sigma (t : env t) :
      (env t * env t array) option =
    match EConstr.kind sigma (Eq.cast eq t) with
    | App (c, u) -> Some ((Eq.(cast (sym (eq ^* array eq)))) (c, u))
    | _ -> None

  let destConstruct (type env) sigma (t : env t) :
      (Constructor.exists * EConstr.EInstance.t) option =
    match EConstr.kind sigma (Eq.cast eq t) with
    | Construct (c, u) -> Some (Exists (Eq.(cast (sym Constructor.eq) c)), u)
    | _ -> None

  let decompose_app sigma t =
    match destApp sigma t with
    | Some (f, cl) -> (f, Array.to_list cl)
    | None -> (t, [])

  type ('a, 'b) map = {
      f : 'n . 'n Height.t -> ('a * 'n) t -> ('b * 'n) t;
    }

  let map (type a b n) sigma (f : (a, b) map) :
      n Height.t -> (a * n) t -> (b * n) t =
    let f n term =
      Eq.(cast (Height.eq ^-> eq ^-> eq)) f.f n term in
    Eq.(cast (sym (Height.eq ^-> eq ^-> eq)))
      (EConstr.map_with_binders sigma succ f)

  type 'env subst = {
      f : 'n . 'n Height.t -> ('env * 'n) t -> ('env * 'n) t option
    }

  let rec subst_rec :
  type env n . Evd.evar_map -> env subst -> n Height.t -> (env * n) t ->
    (env * n) t =
  fun sigma f n term ->
    match f.f n term with
    | None ->
        map sigma { f = fun n term -> subst_rec sigma f n term } n term
    | Some term' -> term'

  let subst sigma f =
    let eq = morphism Env.zero_r in
    Eq.(cast (eq ^-> eq)) (subst_rec sigma f Height.zero)

  let mkConstructU constructor einstance =
    Eq.(cast (sym ((Constructor.eq ^* Refl) ^-> eq))) EConstr.mkConstructU
      (constructor, einstance)

  let mkApp (type env) (f : env t) (args : env t array) : env t =
    Eq.(cast (sym ((eq ^* array eq) ^-> eq))) EConstr.mkApp (f, args)

  let equal (type env) (sigma : Evd.evar_map) (a : env t) (b : env t) :
      bool =
    Eq.(cast (sym (eq ^-> eq ^-> Refl))) (EConstr.eq_constr sigma) a b

  let get_sort_of (type env) (env : env Env.t) sigma (t : env t) =
    Retyping.get_sort_of (Eq.cast Env.eq env) sigma (Eq.cast eq t)
(*
  let prod_applist (type env) sigma (t : env t) (list : env t list) : env t =
    Eq.(cast (sym (Refl ^-> eq ^-> Eq.list eq ^-> eq)))
      Termops.prod_applist sigma t list
*)
(*
  let nf_evar (type env) sigma (t : env t) : env t =
    Eq.(cast (sym (eq ^-> eq))) (Evarutil.nf_evar sigma) t
*)
end

module EvarMapMonad = struct
  include Monad.State

  type 'a t = ('a, Evd.evar_map) Monad.State.t

  let new_type_evar (env : 'env Env.t) rigid : ('env ETerm.t * Sorts.t) t =
  fun sigma ->
    Eq.cast (Eq.pair Refl (Eq.pair (Eq.sym ETerm.eq) Refl))
      (Evarutil.new_type_evar (Eq.cast Env.eq env) sigma rigid)

  let new_evar (env : 'env Env.t) ?(candidates : 'env ETerm.t list option)
        (ty : 'env ETerm.t) : 'env ETerm.t t =
  fun sigma ->
    Eq.cast (Eq.pair Refl (Eq.sym ETerm.eq))
      (Evarutil.new_evar (Eq.cast Env.eq env) sigma (Eq.cast ETerm.eq ty)
        ?candidates:(Eq.(cast (option (list ETerm.eq))) candidates))

(*
  let merge_context_set ?loc ?sideff rigid ctx : unit t =
    let open Ops in
    let* sigma = get in
    set (Evd.merge_context_set rigid sigma ctx)
*)
  let set_leq_sort env s s' =
    let open Ops in
    let* sigma = get in
    set (Evd.set_leq_sort (Eq.cast Env.eq env) sigma s s')

(*
  let set_eq_sort env s s' =
    let open Ops in
    let* sigma = get in
    set (Evd.set_eq_sort (Eq.cast Env.eq env) sigma s s')
*)

  let fresh_inductive_instance env ind =
    let open Ops in
    let* sigma = get in
    let sigma, pind =
      Eq.(cast (sym (Env.eq ^-> Refl ^-> InductiveDef.eq ^->
        (Refl ^* (InductiveDef.eq ^* Refl)))))
        Evd.fresh_inductive_instance env sigma ind in
    let* () = set sigma in
    return pind
end

module AbstractJudgment = struct
  module Self (X : AbstractTermS) = struct
    type concrete = (X.Concrete.t, X.Concrete.t) Environ.punsafe_judgment

    include Phantom (struct
      type t = concrete
    end)

    let morphism (type a b) (_ : (a Env.t, b Env.t) Eq.t) : (a t, b t) Eq.t =
      transtype

    let uj_val (j : 'env t) : 'env X.t =
      Eq.cast (Eq.sym (Eq.arrow eq X.eq)) (fun j -> j.uj_val) j

    let uj_type (j : 'env t) : 'env X.t =
      Eq.cast (Eq.sym (Eq.arrow eq X.eq)) (fun j -> j.uj_type) j

    let make (type env) (uj_val : env X.t) (uj_type : env X.t) : env t =
      Eq.cast (Eq.sym Eq.(X.eq ^-> X.eq ^-> eq))
        Environ.make_judge uj_val uj_type

    include Liftable (struct
      module Phantom = struct type nonrec ('a, 'p, 'q, 'r, 's) t = 'a t end
      module Concrete = struct type t = concrete end
      let unsafe_map f =
        Eq.(cast (sym (eq ^-> eq))) f
      let exliftn el decl =
        Environ.on_judgment (X.Concrete.exliftn el) decl
    end)
  end

  module Map (X0 : AbstractTermS) (X1 : AbstractTermS) = struct
    module J0 = Self (X0)
    module J1 = Self (X1)

    let map2 (type a b) (on_val : a X0.t -> b X1.t) (on_type : a X0.t -> b X1.t)
        (j : a J0.t) : b J1.t =
      match Eq.cast J0.eq j with
      | { uj_val; uj_type } ->
          Eq.cast (Eq.sym J1.eq) {
            uj_val = Eq.(cast (X0.eq ^-> X1.eq)) on_val uj_val;
            uj_type = Eq.(cast (X0.eq ^-> X1.eq)) on_type uj_type; }

    let map (type a b) (f : a X0.t -> b X1.t) (j : a J0.t) : b J1.t =
      map2 f f j

(*
    module UseMonad (M : Monad.S) = struct
      let map2 (type a b) (on_val : a X0.t -> (b X1.t, 'p) M.t)
          (on_type : a X0.t -> (b X1.t, 'p) M.t) (j : a J0.t) :
          (b J1.t, 'p) M.t =
        let open M.Ops in
        match Eq.cast J0.eq j with
        | { uj_val; uj_type } ->
            let* uj_val = on_val (Eq.(cast (sym X0.eq)) uj_val) in
            let* uj_type = on_type (Eq.(cast (sym X0.eq)) uj_type) in
            return (J1.make uj_val uj_type)

(*
      let map (type a b) (f : a X0.t -> (b X1.t, 'p) M.t) (j : a J0.t) :
          (b J1.t, 'p) M.t =
        map2 f f j
*)
    end
*)
  end

  module Make (X : AbstractTermS) = struct
    include Self (X)

    include Map (X) (X)

    let substnl substl height judgment =
      map (X.substnl substl height) judgment

    let substl substl judgment =
      map (X.substl substl) judgment
  end
end

module EJudgment = struct
  include AbstractJudgment.Make (ETerm)

  let inh_conv_coerce_to (type env) ~program_mode ~resolve_tc ?use_coercions
        ?flags (env : env Env.t) (judgment : env t) (t : env ETerm.t) :
      (env t  * Coercion.coercion_trace option) EvarMapMonad.t =
    Eq.cast (EvarMapMonad.eq (Eq.pair (Eq.sym eq) Refl) Refl) (fun sigma ->
      let sigma, result, trace =
        Coercion.inh_conv_coerce_to ~program_mode ?flags ?use_coercions
          ~resolve_tc (Eq.cast Env.eq env)
          sigma (Eq.cast eq judgment) (Eq.cast ETerm.eq t) in
       (sigma, (result, trace)))

  let inh_conv_coerce_to_tycon (type env) ~program_mode (env : env Env.t)
      (judgment : env t) (tycon : env ETerm.t option) : env t EvarMapMonad.t =
    let open EvarMapMonad.Ops in
    match tycon with
    | Some p ->
        let* result, _trace =
          inh_conv_coerce_to ~program_mode ~resolve_tc:true env judgment p
            ~flags:(Evarconv.default_flags_of TransparentState.full) in
        return result
    | None -> return judgment
(*
  let unit (type env) (env : env Env.t) : env t Univ.in_universe_context_set EvarMapMonad.t =
    try
      Eq.(cast (sym (Env.eq ^-> eq ^* Refl))) Evarconv.coq_unit_judge env
    with _ ->
      make (ETerm.mkLambda Context.anonR (ETerm.mkProp ())
          (ETerm.mkLambda Context.anonR (ETerm.mkRel (Rel.zero ()))
            (ETerm.mkRel (Rel.zero ()))))
        (ETerm.mkProd Context.anonR (ETerm.mkProp ())
          (ETerm.mkProd Context.anonR (ETerm.mkRel (Rel.zero ()))
            (ETerm.mkRel (Rel.succ (Rel.zero ()))))), Univ.ContextSet.empty
*)

  let unit_m (type env) (env : env Env.t) : env t EvarMapMonad.t =
    fun sigma ->
    try
      Eq.(cast (sym (Env.eq ^-> Refl ^-> Refl ^* eq))) Evarconv.coq_unit_judge env
        sigma
    with _ ->
      sigma,
      make (ETerm.mkLambda Context.anonR (ETerm.mkProp ())
          (ETerm.mkLambda Context.anonR (ETerm.mkRel (Rel.zero ()))
            (ETerm.mkRel (Rel.zero ()))))
        (ETerm.mkProd Context.anonR (ETerm.mkProp ())
          (ETerm.mkProd Context.anonR (ETerm.mkRel (Rel.zero ()))
            (ETerm.mkRel (Rel.succ (Rel.zero ())))))

(*
  let new_evar env =
    let open EvarMapMonad.Ops in
    let* (ty, _) = EvarMapMonad.new_type_evar env Evd.univ_flexible_alg in
    let* v = EvarMapMonad.new_evar env ty in
    return (make v ty)
*)

  let of_term (type env) (env : env Env.t) sigma (term : env ETerm.t) : env t =
    make term (ETerm.retype_of env sigma term)

(*
  let of_term_via_typing (type env) (env : env Env.t) (term : env ETerm.t) : env t EvarMapMonad.t =
    let open EvarMapMonad.Ops in
    let* ty = ETerm.get_type_of env term in
    return (make term ty)
*)

  let print env sigma j =
    Pp.(ETerm.print env sigma (uj_val j) ++ spc () ++ str ":" ++ spc () ++
      ETerm.print env sigma (uj_type j))
  [@@ocaml.warning "-32"] (* can be unused *)

  let debug_print j =
    Pp.(ETerm.debug_print (uj_val j) ++ spc () ++ str ":" ++ spc () ++
      ETerm.debug_print (uj_type j))
  [@@ocaml.warning "-32"] (* can be unused *)
end

module AbstractDeclaration = struct
  module Self (X : AbstractTermS) = struct
    type ('env, 'nb_args, 'nb_args_tail) desc =
      | LocalAssum : ('env, 'nb Nat.succ, 'nb) desc
      | LocalDef : 'env X.t -> ('env, 'nb, 'nb) desc

    type ('env, 'nb_args, 'nb_args_tail) t = {
        name : Names.Name.t Context.binder_annot;
        ty : 'env X.t;
        desc : ('env, 'nb_args, 'nb_args_tail) desc;
      }

    type ('env, 'nb_args_tail) exists_tail =
        Exists :
          ('env, 'nb_args, 'nb_args_tail) t -> ('env, 'nb_args_tail) exists_tail
              [@@ocaml.unboxed]

    type 'env exists =
        Exists :
          ('env, 'nb_args, 'nb_args_tail) t -> 'env exists [@@ocaml.unboxed]
  end

  module Map (X0 : AbstractTermS) (X1 : AbstractTermS) = struct
    module D0 = Self (X0)
    module D1 = Self (X1)

    let map (type a b nb nb_tail) (f : a X0.t -> b X1.t)
        (d : (a, nb, nb_tail) D0.t) : (b, nb, nb_tail) D1.t =
      { name = d.name;
        ty = f d.ty;
        desc = match d.desc with
        | LocalAssum -> LocalAssum
        | LocalDef v -> LocalDef (f v)
      }
  end

  module Make (X : AbstractTermS) = struct
    include Self (X)

    include Map (X) (X)

    let of_concrete (d : X.Concrete.rel_declaration) :
        ('env, 'nb_args_tail) exists_tail =
      match d with
      | LocalAssum (name, ty) ->
          Exists { name; ty = Eq.(cast (sym X.eq)) ty; desc = LocalAssum }
      | LocalDef (name, v, ty) ->
          Exists { name; ty = Eq.(cast (sym X.eq)) ty;
            desc = LocalDef (Eq.(cast (sym X.eq)) v) }

    let to_concrete (type env nb_args nb_args_tail)
        (d : (env, nb_args, nb_args_tail) t) : X.Concrete.rel_declaration =
      match d.desc with
      | LocalAssum -> LocalAssum (d.name, Eq.cast X.eq d.ty)
      | LocalDef v -> LocalDef (d.name, Eq.cast X.eq v, Eq.cast X.eq d.ty)

    let morphism (type a b nb nb_tail) (eq : (a Env.t, b Env.t) Eq.t)
        (d : (a, nb, nb_tail) t) : (b, nb, nb_tail) t =
      map (Eq.cast (X.morphism eq)) d

    let assum (type env nb) name (ty : env X.t) : (env, nb Nat.succ, nb) t =
      { name; ty; desc = LocalAssum }

    module Judgment = AbstractJudgment.Make (X)

    let local_def (type env nb) (name : Names.Name.t Context.binder_annot)
        (judgment : env Judgment.t) : (env, nb, nb) t =
      { name; ty = Judgment.uj_type judgment;
        desc = LocalDef (Judgment.uj_val judgment) }

    let exliftn el decl =
      map (X.exliftn el) decl

    let liftn n m decl =
      map (X.liftn n m) decl

    let substnl subst n decl =
      map (X.substnl subst n) decl

    let set_name name decl =
      { decl with name = { decl.name with binder_name = name }}
  end
end

module Declaration = struct
  include AbstractDeclaration.Make (Term)

  let lookup (type env h) (env : (env * h) Env.t) (x : h Height.t) :
      env exists =
    let Exists d =
      of_concrete (Environ.lookup_rel (Eq.cast Height.eq x)
        (Eq.cast Env.eq env)) in
    Exists d
end

module EDeclaration = struct
  include AbstractDeclaration.Make (ETerm)

  let of_declaration d =
    let module Map = AbstractDeclaration.Map (Term) (ETerm) in
    Map.map ETerm.of_term d

(*
  let print (type env nb_args nb_args_tail) env sigma
      (d : (env, nb_args, nb_args_tail) t) : Pp.t =
    let name = Context.binder_name d.name in
    match d.desc with
    | LocalAssum ->
        Pp.(Names.Name.print name ++ str ":" ++ spc () ++
          ETerm.print env sigma d.ty)
    | LocalDef value ->
        Pp.(Names.Name.print name ++ str ":" ++ spc () ++
          ETerm.print env sigma d.ty
           ++ spc () ++ str ":=" ++ spc () ++ ETerm.print env sigma value)
*)
end

module AbstractRelContext (X : AbstractTermS) = struct
  module D = AbstractDeclaration.Make (X)

  type ('env, 'length, 'nb_args) t =
    | [] : ('env, Nat.zero, Nat.zero) t
    | (::) : ('env * 'length, 'nb_args, 'nb_args_tail) D.t *
        ('env, 'length, 'nb_args_tail) t ->
        ('env, 'length Nat.succ, 'nb_args) t

  let rec morphism : type a b length nb .
        (a Env.t, b Env.t) Eq.t -> (a, length, nb) t -> (b, length, nb) t =
  fun eq context ->
    match context with
    | [] -> []
    | hd :: tl ->
        D.morphism (Env.morphism eq Refl) hd ::
        morphism eq tl

  let rec length :
  type env length nb_args . (env, length, nb_args) t -> length Nat.t =
  fun v ->
    match v with
    | [] -> O
    | _hd :: tl -> S (length tl)

  let rec nb_args :
  type env length nb_args . (env, length, nb_args) t -> nb_args Nat.t =
  fun v ->
    match v with
    | [] -> O
    | { desc = LocalAssum; _ } :: tl -> S (nb_args tl)
    | { desc = LocalDef _; _ } :: tl -> nb_args tl

  let rec push_plus : type outer length_inner length_outer length
        nb_inner nb_outer nb .
      (outer * length_outer, length_inner, nb_inner) t ->
      (outer, length_outer, nb_outer) t ->
      (length_inner, length_outer, length) Nat.plus ->
      (nb_inner, nb_outer, nb) Nat.plus ->
      (outer, length, nb) t =
  fun inner_context outer_context plus plus_nb ->
    match inner_context, plus, plus_nb with
    | [], Zero_l, Zero_l -> outer_context
    | hd :: tl, Succ_plus plus, _ ->
        let hd =
          D.morphism (Eq.trans Env.assoc (Env.morphism Refl
            (Env.rev_plus plus))) hd in
        match hd.desc, plus_nb with
        | LocalAssum, Succ_plus plus_nb ->
            { hd with desc = LocalAssum } ::
            push_plus tl outer_context plus plus_nb
        | LocalDef ty, _ ->
            { hd with desc = LocalDef ty } ::
            push_plus tl outer_context plus plus_nb

  type ('outer, 'length_inner, 'length_outer, 'nb_inner, 'nb_outer) push =
      Exists : {
      context : ('outer, 'length, 'nb) t;
      decls : ('length_inner, 'length_outer, 'length) Nat.plus;
      args : ('nb_inner, 'nb_outer, 'nb) Nat.plus;
    } -> ('outer, 'length_inner, 'length_outer, 'nb_inner, 'nb_outer) push

  let push (type outer length_inner length_outer nb_inner nb_outer)
      (inner : (outer * length_outer, length_inner, nb_inner) t)
      (outer : (outer, length_outer, nb_outer) t):
      (outer, length_inner, length_outer, nb_inner, nb_outer) push =
    let Exists decls = Nat.to_plus (length inner) in
    let Exists args = Nat.to_plus (nb_args inner) in
    Exists { decls; args; context = push_plus inner outer decls args }

  type 'env exists = Exists : ('env, 'length, 'nb_args) t -> 'env exists

  type concrete = X.Concrete.rel_context

  type ('env, 'height, 'length, 'nb_args) with_height_desc = {
      context : ('env, 'length, 'nb_args) t;
      eq : ('length Env.t, 'height Env.t) Eq.t;
    }

  type ('env, 'height) with_height =
      Exists : ('env, 'height, 'length, 'nb_args) with_height_desc ->
        ('env, 'height) with_height [@@ocaml.unboxed]

  let with_height context =
    Exists { context; eq = Refl }

  let rec of_concrete : type env . concrete -> env exists =
  fun context ->
    match context with
    | [] -> Exists []
    | hd :: tl ->
        let Exists tl = of_concrete tl in
        let Exists hd = D.of_concrete hd in
        Exists (hd :: tl)

  let rec to_concrete :
  type env length nb_args . (env, length, nb_args) t -> concrete =
  fun context ->
    match context with
    | [] -> []
    | hd :: tl -> D.to_concrete hd :: to_concrete tl

  type ('a, 'b) map = {
      f : 'height 'length 'nb_args.
        'height Height.t -> ('a * 'height, 'length, 'nb_args) D.t ->
          ('b * 'height, 'length, 'nb_args) D.t;
    }

  let rec map_rec : type a b length nb_args .
    (a, b) map -> (a, length, nb_args) t ->
      (b, length, nb_args) t * length Height.t =
  fun f context ->
    match context with
    | [] -> [], Height.zero
    | hd :: tl ->
        let tl, height = map_rec f tl in
        let hd = f.f height hd in
        hd :: tl, Height.succ height

  let map map context =
    fst (map_rec map context)

  let exliftn (type a b) (el : (a, b) Lift.t) context =
    context |> map { f = fun (type height) (height : height Height.t) d ->
      D.exliftn (Lift.liftn height el) d }

  let liftn n m context =
    context |> map { f = fun height d ->
      D.morphism (Eq.sym Env.assoc)
        (D.liftn n (Height.add m height)
           (D.morphism Env.assoc d)) }

  let substnl subst n context =
    context |> map { f = fun height d ->
      D.morphism (Eq.sym Env.assoc)
        (D.substnl subst (Height.add n height)
           (D.morphism Env.assoc d)) }

  let substl subst context =
    context |>
    morphism (Eq.sym Env.zero_r) |>
    substnl subst Height.zero |>
    morphism Env.zero_r

  let lift (type env length nb_args n) (n : n Height.t)
      (context : (env, length, nb_args) t) :
      (env * n, length, nb_args) t =
    morphism Env.zero_r
      (liftn n Height.zero (morphism (Eq.sym Env.zero_r) context))

  let unsafe_exliftn el context =
    let add decl (new_context, el) =
      new_context |> Context.Rel.add
        (Context.Rel.Declaration.map_constr (X.Concrete.exliftn el) decl),
      Esubst.el_shft 1 el in
    let new_context, _m =
      Context.Rel.fold_outside add context ~init:(Context.Rel.empty, el) in
    new_context

  let it_mkLambda_or_LetIn (type env height)
      (Exists { context } : (env, height) with_height)
      (t : (env * height) X.t) : env X.t =
    Eq.(cast (sym (X.eq ^-> Refl ^-> X.eq)))
      X.Concrete.it_mkLambda_or_LetIn t (to_concrete context)

  let it_mkProd_or_LetIn (type env height)
      (Exists { context } : (env, height) with_height)
      (t : (env * height) X.t) : env X.t =
    Eq.(cast (sym (X.eq ^-> Refl ^-> X.eq)))
      X.Concrete.it_mkProd_or_LetIn t (to_concrete context)

  module Judgment = D.Judgment

  let it_mkLambda_or_LetIn_judgment (type env height)
      (context : (env, height) with_height)
      (t : (env * height) Judgment.t) : env Judgment.t =
    Judgment.map2 (it_mkLambda_or_LetIn context) (it_mkProd_or_LetIn context)
      t

  let rec of_vector_rec : type env length .
      (env X.t, length) Vector.t -> (env, length, length) t * length Height.t =
  fun vector ->
    match vector with
    | [] -> [], Height.zero
    | hd :: tl ->
        let tl, height = of_vector_rec tl in
        let hd = X.lift height hd in
        D.assum Context.anonR hd :: tl, Height.succ height

  let of_vector vector =
    fst (of_vector_rec vector)

(*
  let rec of_named_vector_rec : type env length .
      (Names.Name.t * env X.t, length) Vector.t ->
      (env, length, length) t * length Height.t =
  fun vector ->
    match vector with
    | [] -> [], Height.zero
    | (name, hd) :: tl ->
        let tl, height = of_named_vector_rec tl in
        let hd = X.lift height hd in
        D.assum (Context.annotR name) hd :: tl, Height.succ height

  let of_named_vector vector =
    fst (of_named_vector_rec vector)
*)

  let rec to_rel_vector_decls_lift : type env env' length nb_args .
      (env, length, nb_args) t -> (env * length, env') Lift.t ->
        (env' Judgment.t, length) Vector.t =
  fun context lift ->
    match context with
    | [] -> []
    | hd :: tl ->
        let lift' = Lift.(Height.one & Eq.(cast (morphism
          (Env.morphism Refl (sym Env.succ) ++ sym Env.assoc) Refl) lift)) in
        let tl = to_rel_vector_decls_lift tl lift' in
        let hd =
          Eq.(cast (Judgment.morphism (trans (trans (sym Env.succ) Env.assoc)
             (Env.morphism Refl Env.succ))))
            (Judgment.make (X.mkRel (Index.zero ()))
               (Eq.cast (X.morphism Env.succ)
                  (X.lift Height.one hd.ty))) in
        Judgment.exliftn lift hd :: tl

  let to_rel_vector_decls context =
    to_rel_vector_decls_lift context (Lift.id ())

  let rec to_rel_vector_lift : type env env' length nb_args .
      (env, length, nb_args) t -> (env * length, env') Lift.t ->
        (env' Judgment.t, nb_args) Vector.t =
  fun context lift ->
    match context with
    | [] -> []
    | hd :: tl ->
        let lift' = Lift.(Height.one & Eq.(cast (morphism
          (Env.morphism Refl (sym Env.succ) ++ sym Env.assoc) Refl) lift)) in
        let tl = to_rel_vector_lift tl lift' in
        match hd.desc with
        | LocalAssum ->
            let hd = Eq.(cast
              (Judgment.morphism (trans (trans (sym Env.succ) Env.assoc)
                (Env.morphism Refl Env.succ))))
                (Judgment.make (X.mkRel (Index.zero ()))
                  (Eq.cast (X.morphism Env.succ)
                     (X.lift Height.one hd.ty))) in
            Judgment.exliftn lift hd :: tl
        | LocalDef _ -> tl

  let to_rel_vector context =
    to_rel_vector_lift context (Lift.id ())

  let rec set_names : type env length nb_args .
    (Names.Name.t, length) Vector.t -> (env, length, nb_args) t ->
      (env, length, nb_args) t =
  fun names context ->
    match names, context with
    | [], [] -> []
    | name :: names, hd :: tl ->
        D.set_name name hd :: set_names names tl

  let rec set_names_from_env : type env length nb_args .
    (env * length) Env.t -> (env, length, nb_args) t ->
      (env, length, nb_args) t =
  fun env context ->
    match context with
    | [] -> []
    | hd :: tl ->
        let env = env |> Eq.(cast (Env.morphism Refl (sym Env.succ) ++
          (sym Env.assoc))) in
        let Exists decl = Declaration.lookup env Height.one in
        D.set_name (Context.binder_name decl.name) hd ::
        set_names_from_env (Height.env Height.one env) tl

  let subst_of_instance : type env length nb_args .
    (env, length, nb_args) t -> (env X.t, nb_args) Vector.t ->
      (env X.t, length) Vector.t =
  fun context args ->
    match
      Vector.of_list_of_length
        (Eq.(cast (sym (Refl ^-> array X.eq ^-> list X.eq)))
           X.Concrete.subst_of_rel_context_instance (to_concrete context)
             (Vector.to_array args)) (length context)
    with
    | Some vector -> vector
    | None -> assert false
end

module RelContextMap (X0 : AbstractTermS) (X1 : AbstractTermS) = struct
  module C0 = AbstractRelContext (X0)
  module C1 = AbstractRelContext (X1)

  type map = {
      f : 'height 'nb_args 'nb_args_tail .
        ('height, 'nb_args, 'nb_args_tail) C0.D.t ->
          ('height, 'nb_args, 'nb_args_tail) C1.D.t;
    }

  let rec map : type env length nb_args .
    map -> (env, length, nb_args) C0.t -> (env, length, nb_args) C1.t =
  fun f c ->
    match c with
    | [] -> []
    | hd :: tl -> f.f hd :: map f tl
end

module RelContext = AbstractRelContext (Term)

module ERelContext = struct
  include AbstractRelContext (ETerm)

  let of_rel_context c =
    let module Map = RelContextMap (Term) (ETerm) in
    Map.map { f = EDeclaration.of_declaration } c

(*
  type ('env, 'm, 'n) decompose_n = Exists : {
      context : ('env, 's, 's) t;
      term : ('env * 's) ETerm.t;
      plus : ('m, 'n, 's) Nat.plus;
    } -> ('env, 'm, 'n) decompose_n

  type decompose_1 = {
      f : 'env . Evd.evar_map -> 'env ETerm.t -> 'env ETerm.decompose_1;
    }

  let rec decompose_n_rec : type env m n .
    decompose_1 -> Evd.evar_map -> m Nat.t ->
    (env, m, m) t -> n Nat.t ->
      (env * m) ETerm.t -> (env, m, n) decompose_n =
  fun f sigma m context n t ->
    match n with
    | O ->
        Exists { context; term = t; plus = Nat.zero_r m }
    | S n ->
      let ETerm.{ name; ty; t } = f.f sigma t in
      let t = Eq.(cast (ETerm.morphism (trans (sym Env.succ) (trans Env.assoc
        (Env.morphism Refl Env.succ))))) t in
      let Exists { context; term; plus = Succ_plus plus } =
        decompose_n_rec f sigma (S m)
          ({ name; ty; desc = LocalAssum } :: context) n t in
      Exists { context; term; plus = Nat.plus_succ plus }

  let decompose_n (type env n) decompose_1 sigma (n : n Nat.t)
      (t : env ETerm.t) : (env, n, n) t * (env * n) ETerm.t =
    let Exists { context; term; plus = Zero_l } =
      decompose_n_rec decompose_1 sigma O [] n
        (Eq.(cast (ETerm.morphism (sym Env.zero_r))) t) in
    context, term

  let decompose_lam_n sigma n t =
    decompose_n { f = ETerm.decompose_lam_1 } sigma n t

  let decompose_prod_n sigma n t =
    decompose_n { f = ETerm.decompose_prod_1 } sigma n t
*)
end

module GlobalEnv = struct
  include Phantom (struct type t = GlobEnv.t end)

  let env (glob_env : 'env t) : 'env Env.t =
    Eq.cast (Eq.sym Env.eq) (GlobEnv.env (Eq.cast eq glob_env))

  let push_rel (type env nb_args nb_args_tail) ~hypnaming
      sigma (d : (env, nb_args, nb_args_tail) EDeclaration.t)
      (glob_env : env t) :
      (env, nb_args, nb_args_tail) EDeclaration.t *
      (env * Nat.one) t =
    let d', env =
      GlobEnv.push_rel ~hypnaming sigma (EDeclaration.to_concrete d)
         (Eq.cast eq glob_env) in
    let env = Eq.(cast (sym eq)) env in
    let Exists d' =
      (EDeclaration.of_concrete d' :
         (env, nb_args_tail) EDeclaration.exists_tail) in
    match d.desc, d'.desc with
    | LocalAssum, LocalAssum -> d', env
    | LocalDef _, LocalDef _ -> d', env
    | _ -> assert false

  let push_rel_context (type env height) ~hypnaming
      sigma (Exists { context; _ } : (env, height) ERelContext.with_height)
      (glob_env : env t) : (env * height) t =
    let _rel_context, env =
      GlobEnv.push_rel_context ~hypnaming sigma
        (ERelContext.to_concrete context)
        (Eq.cast eq glob_env) in
    Eq.cast (Eq.sym eq) env

  let morphism (type a b) (_ : (a Env.t, b Env.t) Eq.t) :
      (a t, b t) Eq.t =
    transtype

(*
  type 'a fold = {
      f : 'env 'nb_args 'nb_args_tail . 'env t ->
        ('env, 'nb_args, 'nb_args_tail) EDeclaration.t -> 'a -> 'a
    }

  let rec fold_context_aux : type env length nb_args . hypnaming:_ ->
    'a fold -> env t -> Evd.evar_map -> (env, length, nb_args) ERelContext.t ->
      'a -> 'a * (env * length) t =
  fun ~hypnaming f env sigma context state ->
    match context with
    | [] -> state, Eq.(cast (morphism (sym Env.zero_r))) env
    | hd :: tl ->
        let state, env = fold_context_aux ~hypnaming f env sigma tl state in
        let state = f.f env hd state in
        let _, env = push_rel ~hypnaming sigma hd env in
        state,
        Eq.(cast (morphism (trans Env.assoc (Env.morphism Refl Env.succ)))) env

  let fold_context ~hypnaming f env sigma context v =
    fst (fold_context_aux ~hypnaming f env sigma context v)

  let print_context ~hypnaming e sigma
      (Exists { context } : (_, _) ERelContext.with_height) =
    fold_context ~hypnaming
      { f = fun e d pp ->
          Pp.(pp ++ cut () ++ EDeclaration.print (env e) sigma d) } e sigma
      context (Pp.mt ())
*)
end

module InductiveSpecif = struct
  include Phantom2 (struct type t = Inductive.mind_specif end)

  let lookup (type env ind) (env : env Env.t) (ind : ind InductiveDef.t) :
      (env, ind) t =
    Eq.cast (Eq.sym (Eq.arrow Env.eq (Eq.arrow InductiveDef.eq eq)))
      Inductive.lookup_mind_specif env ind

  let params (type env ind) (specif : (env, ind) t) : int =
    Inductive.inductive_params (Eq.cast eq specif)

  let constructors (type env ind) (specif : (env, ind) t) :
      (env Term.t, ind) Tuple.t =
    Eq.cast (Eq.trans (Eq.array (Eq.sym (Term.eq))) (Eq.sym Tuple.eq))
      (snd (Eq.cast eq specif)).mind_user_lc
end

module type AnnotationS = sig
  type ('env, 'annot, 'annot_tail) t

  type 'env unit_annot
end

module AnnotatedVector = struct
  module Self (S : AnnotationS) = struct
    type ('env, 'length, 'annot, 'end_annot) section =
      | [] : ('env, Nat.zero, 'end_annot, 'end_annot) section
      | (::) :
          ('env, 'annot, 'annot_tail) S.t *
          ('env, 'length, 'annot_tail, 'end_annot) section ->
            ('env, 'length Nat.succ, 'annot, 'end_annot) section

    type ('env, 'length, 'annot) t =
        ('env, 'length, 'annot, 'env S.unit_annot) section

    let rec length : type env length annot end_annot .
          (env, length, annot, end_annot) section -> length Nat.t =
    fun v ->
      match v with
      | [] -> O
      | _ :: tl -> S (length tl)
  end

  module Map (S0 : AnnotationS) (S1 : AnnotationS) = struct
    module V0 = Self (S0)

    module V1 = Self (S1)

    type ('a, 'b) map =
        { f : 'annot 'annot_tail .
            ('a, 'annot, 'annot_tail) S0.t -> ('b, 'annot, 'annot_tail) S1.t }

    let rec map_append : type a b annot0 annot1 annot2 length0 length1 length2 .
          (a, b) map -> (a, length0, annot0, annot1) V0.section ->
            (b, length1, annot1, annot2) V1.section ->
            (length0, length1, length2) Nat.plus ->
            (b, length2, annot0, annot2) V1.section =
    fun f v b plus ->
      match v, plus with
      | [], Nat.Zero_l -> b
      | hd :: tl, Nat.Succ_plus plus ->
          f.f hd :: map_append f tl b plus

    let map f v = map_append f v [] (Nat.zero_r (V0.length v))
  end

  module Make (S : AnnotationS) = struct
    include Self (S)

    include Map (S) (S)

    let append v0 v1 = map_append { f = Fun.id } v0 v1

    type ('a, 'b) map = {
        f : 'annot 'annot_tail . ('a, 'annot, 'annot_tail) S.t -> 'b;
      }

    let rec to_vector : type a b length annot end_annot .
          (a, b) map -> (a, length, annot, end_annot) section ->
          (b, length) Vector.t =
    fun f v ->
      match v with
      | [] -> []
      | hd :: tl -> f.f hd :: to_vector f tl

    let rec find_opt : type a env length annot end_annot .
        (env, a option) map -> (env, length, annot, end_annot) section ->
        a option =
    fun f v ->
      match v with
      | [] -> None
      | hd :: tl ->
          match f.f hd with
          | None -> find_opt f tl
          | x -> x

    let for_all (type env length annot end_annot) (f : (env, bool) map)
        (v : (env, length, annot, end_annot) section) : bool =
      find_opt { f = fun x -> if f.f x then None else Some () } v = None
  end
end

module InductiveFamily = struct
  type ('env, 'ind, 'params, 'nrealargs, 'nrealdecls) t = {
      def : 'ind InductiveDef.t Univ.puniverses;
      params : ('env Term.t, 'params) Vector.t;
      nrealargs : 'nrealargs Nat.t;
      nrealdecls : 'nrealdecls Nat.t;
    }

  type ('env, 'ind) exists =
      Exists :
        ('env, 'ind, 'params, 'nrealargs, 'nrealdecls) t -> ('env, 'ind) exists
            [@@ocaml.unboxed]

  let ind_fun (type ind params0 params1 nrealargs0 nrealargs1 nrealdecls0
        nrealdecls1)
      (indf0 : (_, ind, params0, nrealargs0, nrealdecls0) t)
      (indf1 : (_, ind, params1, nrealargs1, nrealdecls1) t) :
      (params0 * nrealargs0 * nrealdecls0,
       params1 * nrealargs1 * nrealdecls1) Eq.t =
    match
      Nat.is_eq (Vector.length indf0.params) (Vector.length indf1.params),
      Nat.is_eq indf0.nrealargs indf1.nrealargs,
      Nat.is_eq indf0.nrealdecls indf1.nrealdecls
    with
    | Some Refl, Some Refl, Some Refl -> Refl
    | _ -> assert false

  let of_concrete (env : 'env Env.t) (indf : Inductiveops.inductive_family) :
      ('env, 'ind) exists =
    let (ind, univ), params = Inductiveops.dest_ind_family indf in
    let Exists params =
      Vector.of_list (Eq.(cast (list (sym Term.eq))) params) in
    let def = Eq.cast (Eq.sym InductiveDef.eq) ind in
    let oib =
      snd (Eq.cast InductiveSpecif.eq (InductiveSpecif.lookup env def)) in
    let Exists nrealargs = Nat.of_int (oib.mind_nrealargs) in
    let Exists nrealdecls = Nat.of_int (oib.mind_nrealdecls) in
    Exists {
      def = (def, univ); params;
      nrealargs;
      nrealdecls }

  let to_concrete (indf : ('env, 'ind, 'params, 'nrealargs, 'nrealdecls) t) :
      Inductiveops.inductive_family =
    let ind, univ = indf.def in
    let params = Eq.(cast (list Term.eq)) (Vector.to_list indf.params) in
    Inductiveops.make_ind_family ((Eq.cast InductiveDef.eq ind, univ), params)

  let get_arity (type env ind params nrealargs nrealdecls) (env : env Env.t)
      (indf : (env, ind, params, nrealargs, nrealdecls) t) :
      (env, nrealdecls, nrealargs) ERelContext.t =
    let Exists context =
      ERelContext.of_concrete (List.map EConstr.of_rel_decl (fst
        (Inductiveops.get_arity (Eq.cast Env.eq env) (to_concrete indf)))) in
    match Nat.is_eq (ERelContext.length context) indf.nrealdecls,
     Nat.is_eq (ERelContext.nb_args context) indf.nrealargs with
    | Some Refl, Some Refl -> context
    | _ -> assert false

  let build_dependent_inductive  (type env ind params nrealargs nrealdecls)
      (env : env Env.t) (indf : (env, ind, params, nrealargs, nrealdecls) t) :
      (env * nrealdecls) ETerm.t =
    Eq.cast (Eq.sym ETerm.eq)
      (EConstr.of_constr (Inductiveops.build_dependent_inductive
         (Eq.cast Env.eq env) (to_concrete indf)))

  let map (type ind params nrealargs nrealdecls a b) (f : a Term.t -> b Term.t)
      (indf : (a, ind, params, nrealargs, nrealdecls) t) :
      (b, ind, params, nrealargs, nrealdecls) t =
    { indf with params = Vector.map f indf.params }

(*
  let liftn m n indf = map (Term.liftn m n) indf
*)

  let lift n indf = map (Term.lift n) indf
end

module InductiveType = struct
  type ('env, 'ind, 'params, 'nrealargs, 'nrealdecls) t = {
      family : ('env, 'ind, 'params, 'nrealargs, 'nrealdecls) InductiveFamily.t;
      realargs : ('env ETerm.t, 'nrealargs) Vector.t;
    }

(*
  type 'env exists =
      Exists : ('env, 'ind, 'params, 'nrealargs, 'nrealdecls) t -> 'env exists
*)

  type ('env, 'ind) exists_ind =
      Exists :
        ('env, 'ind, 'params, 'nrealargs, 'nrealdecls) t ->
          ('env, 'ind) exists_ind [@@ocaml.unboxed]

  let of_concrete (type env ind) (env : env Env.t)
      (ind_type : Inductiveops.inductive_type) :
      (env, ind) exists_ind =
    let family, realargs = Inductiveops.dest_ind_type ind_type in
    let Exists realargs =
      Vector.of_list (Eq.cast (Eq.list (Eq.sym ETerm.eq)) realargs) in
    let Exists family = InductiveFamily.of_concrete env family in
    match Nat.is_eq (Vector.length realargs) family.nrealargs with
    | None -> assert false
    | Some Refl -> Exists { family; realargs }

  let to_inductive_type (type env ind params nrealargs nrealdecls)
      (indt : (env, ind, params, nrealargs, nrealdecls) t) :
      Inductiveops.inductive_type =
    let family = InductiveFamily.to_concrete indt.family in
    Eq.(cast (sym ((Refl ^* Eq.list ETerm.eq) ^-> Refl)))
      Inductiveops.make_ind_type (family, Vector.to_list indt.realargs)

  let of_term_opt (type env ind) (env : env Env.t) sigma
      (term : env ETerm.t) : (env, ind) exists_ind option =
    match
       Inductiveops.find_rectype (Eq.cast Env.eq env) sigma
        (Eq.cast ETerm.eq term)
    with
    | exception Not_found -> None
    | ind -> Some (of_concrete env ind)

  let of_term_opt_whd_all env sigma term =
    of_term_opt env sigma (ETerm.whd_all env sigma term)

  let map (type ind params realargs realdecls a b) (f : a Term.t -> b Term.t)
      (ef : a ETerm.t -> b ETerm.t)
      (ind_type : (a, ind, params, realargs, realdecls) t) :
      (b, ind, params, realargs, realdecls) t =
    { family = InductiveFamily.map f ind_type.family;
      realargs = Vector.map ef ind_type.realargs }

  let exliftn el ind_type =
    map (Term.exliftn el) (ETerm.exliftn el) ind_type

  let make_with_evars (type env ind) (env : env Env.t)
      (ind : ind InductiveDef.t) :
      (env ETerm.t * (env, ind) exists_ind) EvarMapMonad.t =
    let open EvarMapMonad.Ops in
    let nb_args =
      Inductiveops.inductive_nallargs (Eq.cast Env.eq env)
        (Eq.cast InductiveDef.eq ind) in
    let* args = EvarMapMonad.array_init nb_args (fun _ ->
      let* (e, _) = EvarMapMonad.new_type_evar env Evd.univ_flexible_alg in
      EvarMapMonad.new_evar env e) in
    let* (ind, instance) = EvarMapMonad.fresh_inductive_instance env ind in
    let term =
      ETerm.mkApp (ETerm.mkIndU ind (EConstr.EInstance.make instance)) args in
    let* sigma = EvarMapMonad.get in
    match of_term_opt env sigma term with
    | None -> assert false
    | Some (Exists ind) ->
        return (term, Exists ind)

  let make_case_or_project (type env ind params realargs realdecls)
    (env : env Env.t)
    sigma (indt : (env, ind, params, realargs, realdecls) t)
    (style : Constr.case_style) ~(return_pred : env ETerm.t)
    ~(tomatch : env ETerm.t) (branches : (env ETerm.t, ind) Tuple.t) :
      env ETerm.t =
    let mind = indt.family.def in
    let rci =
      Eq.cast (Eq.sym Eq.(Env.eq ^-> Refl ^-> (InductiveDef.eq ^* Refl) ^->
        ETerm.eq ^-> ETerm.eq ^-> Refl))
      Typing.check_allowed_sort env sigma mind tomatch return_pred in
    let ci =
      Eq.cast (Eq.sym Eq.(Env.eq ^-> InductiveDef.eq ^-> Refl))
      Inductiveops.make_case_info env (fst mind) rci style in
    let indt = to_inductive_type indt in
    Eq.cast (Eq.sym Eq.(
      Env.eq ^-> Refl ^-> Refl ^-> Refl ^-> ETerm.eq ^-> ETerm.eq ^->
        Eq.trans Tuple.eq (Eq.array ETerm.eq) ^->
        ETerm.eq))
    Inductiveops.make_case_or_project env sigma indt ci return_pred
      tomatch branches
end


module ConstructorSummary = struct
  type ('env, 'ind, 'nrealargs, 'arity, 'args) t = {
      desc : Inductiveops.constructor_summary;
      cstr : 'ind Constructor.t;
      args : ('env, 'arity, 'args) RelContext.t;
      arity : 'arity Nat.t;
      concl_realargs : (('env * 'arity) ETerm.t, 'nrealargs) Vector.t;
      nrealargs : 'nrealargs Nat.t;
    }

  type ('env, 'ind, 'nrealargs) exists =
      Exists : ('env, 'ind, 'nrealargs, 'arity, 'args) t ->
        ('env, 'ind, 'nrealargs) exists [@@ocaml.unboxed]

  let unsafe_make (type nrealargs) (desc : Inductiveops.constructor_summary)
      (nrealargs : nrealargs Nat.t)
      (cstr : 'ind Constructor.t) : ('env, 'ind, nrealargs) exists =
    let Exists args = RelContext.of_concrete desc.cs_args in
    let concl_realargs =
      Array.map (fun constr -> ETerm.of_term (Eq.(cast (sym Term.eq)) constr))
        desc.cs_concl_realargs in
    let concl_realargs =
      match
        Vector.of_list_of_length (Array.to_list concl_realargs) nrealargs
      with
      | None -> assert false
      | Some concl_realargs -> concl_realargs in
        Exists { desc; cstr; args; arity = RelContext.length args;
          concl_realargs; nrealargs }

  let get (env : 'env Env.t)
      (indf : ('env, 'ind, 'params, 'nrealargs, 'nrealdecls) InductiveFamily.t)
      (specif : ('env, 'ind) InductiveSpecif.t)
      (cstr : 'ind Constructor.t) : ('env, 'ind, 'nrealargs) exists =
    let indu, params =
      Inductiveops.dest_ind_family (InductiveFamily.to_concrete indf) in
    let mib, mip = Eq.cast InductiveSpecif.eq specif in
    let index = succ (Eq.cast Index.eq (Constructor.index cstr)) in
    let desc = Inductiveops.get_constructor (indu, mib, mip, params) index in
    unsafe_make desc indf.nrealargs cstr

  let get_tuple (env : 'env Env.t)
      (indf : ('env, 'ind, 'params, 'nrealargs, 'nrealdecls) InductiveFamily.t)
      (specif : ('env, 'ind) InductiveSpecif.t) :
      (('env, 'ind, 'nrealargs) exists, 'ind) Tuple.t =
    let ind, _ = indf.def in
    let nb = Tuple.length (InductiveSpecif.constructors specif) in
    Tuple.init nb (fun i -> get env indf specif (Constructor.make ind i))

  let build_dependent_constructor
      (cs : ('env, 'ind, 'nrealargs, 'arity, 'args) t) :
      ('env * 'arity) Term.t =
    Eq.(cast (sym (Refl ^-> Term.eq)))
      Inductiveops.build_dependent_constructor cs.desc

  include Liftable (struct
    module Phantom = struct
      type nonrec ('env, 'ind, 'nrealargs, 'arity, 'args) t =
          ('env, 'ind, 'nrealargs, 'arity, 'args) t
    end
    module Concrete = struct
      type t = Inductiveops.constructor_summary
    end
    let unsafe_map (type a b ind nrealargs arity args) f
        (summary : (a, ind, nrealargs, arity, args) t) :
        (b, ind, nrealargs, arity, args) t =
      let Exists result =
        unsafe_make (f summary.desc) summary.nrealargs summary.cstr in
      match
        Nat.is_eq (RelContext.length result.args)
          (RelContext.length summary.args),
        Nat.is_eq (RelContext.nb_args result.args)
          (RelContext.nb_args summary.args) with
      | Some Refl, Some Refl -> result
      | _ -> assert false
    let exliftn el (cs : Inductiveops.constructor_summary) :
        Inductiveops.constructor_summary = {
      cs_cstr = cs.cs_cstr;
      cs_params = List.map (Constr.exliftn el) cs.cs_params;
      cs_nargs = cs.cs_nargs;
      cs_args = RelContext.unsafe_exliftn el cs.cs_args;
      cs_concl_realargs =
        Array.map (Constr.exliftn el) cs.cs_concl_realargs
    }
  end)
end

exception NotAdjustable

let rec adjust_local_defs ?loc pats (args : _ Context.Rel.pt) :
    Glob_term.cases_pattern list =
  match pats, args with
  | (pat :: pats, LocalAssum _ :: decls) ->
      pat :: adjust_local_defs ?loc pats decls
  | (pats, LocalDef _ :: decls) ->
      (DAst.make ?loc @@ Glob_term.PatVar Anonymous) ::
      adjust_local_defs ?loc pats decls
  | [], [] -> []
  | _ -> raise NotAdjustable

let nb_params_of_constructor env cstr =
  let inductive = Constructor.inductive cstr in
  let mind_specif = InductiveSpecif.lookup env inductive in
  InductiveSpecif.params mind_specif

module Pattern = struct
  type ('size, 'size_tail) section = ('size, 'size_tail) content CAst.t
  and ('size, 'size_tail) content = {
      name : Names.Name.t;
      desc : ('size, 'size_tail) desc;
    }
  and ('size, 'size_tail) desc =
    | Var : ('size Nat.succ, 'size) desc
    | Cstr : {
      cstr : Constructor.exists;
      args : ('length, 'size, 'size_tail Nat.succ) args;
    } -> ('size, 'size_tail) desc
  and ('length, 'size, 'size_tail) args =
    | [] : (Nat.zero, 'size, 'size) args
    | (::) : ('size0, 'size1) section * ('length, 'size1, 'size2) args ->
        ('length Nat.succ, 'size0, 'size2) args
(*
  type 'size t = ('size, Nat.zero) section
*)
(*
  let eq_args (type a b size size_tail) (Refl : (a, b) Eq.t) :
      ((a, size, size_tail) args, (b, size, size_tail) args) Eq.t = Refl
*)

  type exists = Exists : ('size, 'size_tail) section -> exists [@@ocaml.unboxed]

  let var ?loc name =
    CAst.make { name; desc = Var }

  let cstr ?loc ?(name = Names.Name.Anonymous) cstr args =
    CAst.make { name; desc = Cstr { cstr; args }}

  let ex_var ?loc name = Exists (var ?loc name)

(*
  let ex_cstr ?loc ?name c args = Exists (cstr ?loc ?name c args)
*)

  type 'size_tail size_exists =
      Exists : ('size, 'size_tail) section -> 'size_tail size_exists
          [@@ocaml.unboxed]

  type 'size_tail args_exists =
      Exists : ('length, 'size, 'size_tail) args -> 'size_tail args_exists
          [@@ocaml.unboxed]

  type ('length, 'size_tail) args_exists_length =
      Exists : ('length, 'size, 'size_tail) args ->
        ('length, 'size_tail) args_exists_length
          [@@ocaml.unboxed]

  let rec length : type length size size_tail .
        (length, size, size_tail) args -> length Nat.t =
  fun args ->
    match args with
    | [] -> O
    | _ :: tl -> S (length tl)

  let rec append_plus : type l0 l1 l s0 s1 s2 .
        (l0, s0, s1) args -> (l1, s1, s2) args -> (l0, l1, l) Nat.plus ->
          (l, s0, s2) args =
  fun args0 args1 plus ->
    match args0, plus with
    | [], Zero_l -> args1
    | hd :: tl, Succ_plus plus -> hd :: append_plus tl args1 plus

(*
  type ('l0, 'l1, 's0, 's2) concat = Exists : {
      args : ('l, 's0, 's2) args;
      length : 'l Nat.t;
      plus : ('l0, 'l1, 'l) Nat.plus;
    } -> ('l0, 'l1, 's0, 's2) concat

  let append (type l0 l1 s0 s1 s2) (args0 : (l0, s0, s1) args)
      (args1 : (l1, s1, s2) args) : (l0, l1, s0, s2) concat  =
    let Exists (length, plus) = Nat.add (length args0) (length args1) in
    Exists { args = append_plus args0 args1 plus; length; plus }
*)

  type ('n, 'size_tail) make_vars = Exists : {
      args : ('n, 'size, 'size_tail) args;
      plus : ('n, 'size_tail, 'size) Nat.plus;
    } -> ('n, 'size_tail) make_vars

  let rec make_vars :
  type n size_tail . ?loc:Loc.t -> n Nat.t -> (n, size_tail) make_vars =
  fun ?loc n ->
    match n with
    | O -> Exists { args = []; plus = Nat.Zero_l }
    | S n ->
        let Exists tl = make_vars ?loc n in
        let args = CAst.make { name = Anonymous; desc = Var } :: tl.args in
        let plus = Nat.Succ_plus tl.plus in
        Exists { args; plus }

  let rec size : type size size_tail .
        (size, size_tail) section -> size_tail Nat.t -> size Nat.t =
  fun pat size_tail ->
    match pat.v.desc with
    | Var -> S size_tail
    | Cstr { args; _ } -> size_of_args args (S size_tail)
  and size_of_args : type length size size_tail .
        (length, size, size_tail) args -> size_tail Nat.t -> size Nat.t =
  fun args tail ->
    match args with
    | [] -> tail
    | hd :: tl -> size hd (size_of_args tl tail)

  let rec diff : type s0 s1 s2 .
        (s0, s1) section -> (s1, s2) Nat.Diff.t -> (s0, s2) Nat.Diff.t =
  fun pat diff_tail ->
    match pat.v.desc with
    | Var -> Nat.Diff.succ diff_tail
    | Cstr { args; _ } -> diff_of_args args (Nat.Diff.succ diff_tail)
  and diff_of_args : type length s0 s1 s2 .
        (length, s0, s1) args -> (s1, s2) Nat.Diff.t -> (s0, s2) Nat.Diff.t =
  fun args tail ->
    match args with
    | [] -> tail
    | hd :: tl -> diff hd (diff_of_args tl tail)

  let rec size_of_concrete :
  type size_tail . Glob_term.cases_pattern -> size_tail size_exists = fun p ->
    let loc = p.loc in
    match DAst.get p with
    | PatVar name -> Exists (CAst.make ?loc { name; desc = Var })
    | PatCstr (cstr, args, name) ->
        let cstr = Constructor.of_concrete cstr in
        let Exists args = args_of_concrete args in
        Exists (CAst.make ?loc { name; desc = Cstr { cstr; args }})
  and args_of_concrete :
  type size_tail . Glob_term.cases_pattern list -> size_tail args_exists =
  fun l ->
    match l with
    | [] -> Exists []
    | hd :: tl ->
        let Exists tl = args_of_concrete tl in
        let Exists hd = size_of_concrete hd in
        Exists (hd :: tl)

(*
  let of_concrete pat : exists =
    let Exists pat = size_of_concrete pat in
    Exists pat
*)

  let rec to_concrete :
  type size size_tail . (size, size_tail) section -> Glob_term.cases_pattern =
  fun { v = { name; desc }; loc } ->
    match desc with
    | Var ->  DAst.make ?loc (Glob_term.PatVar name)
    | Cstr { cstr = Exists cstr; args } ->
        let cstr = Constructor.to_concrete cstr in
        let args = Vector.to_list (args_to_concrete args) in
        DAst.make ?loc (Glob_term.PatCstr (cstr, args, name))
  and args_to_concrete : type length size size_tail .
    (length, size, size_tail) args ->
      (Glob_term.cases_pattern, length) Vector.t =
  fun args ->
    match args with
    | [] -> []
    | hd :: tl -> to_concrete hd :: args_to_concrete tl

  let rec to_vector : type length size size_tail .
    (length, size, size_tail) args -> (exists, length) Vector.t =
  fun args ->
    match args with
    | [] -> []
    | hd :: tl -> Exists hd :: to_vector tl

  let adjust_args (type env ind nrealargs arity args size_tail) ?loc
      (env : env Env.t) (args : Glob_term.cases_pattern list)
      (summary : (env, ind, nrealargs, arity, args) ConstructorSummary.t) :
      (arity, size_tail) args_exists_length =
    let Exists args' = args_of_concrete args in
    let nargs = length args' in
    match Nat.is_eq nargs summary.arity with
    | Some Refl -> Exists args'
    | None ->
        let args =
          try
            adjust_local_defs ?loc args (List.rev summary.desc.cs_args)
          with NotAdjustable ->
            let nlet =
              CList.count
                (function Context.Rel.Declaration.LocalDef _ -> true
                  | _ -> false)
              summary.desc.cs_args in
            let expected_nassums = Nat.to_int summary.arity in
            Constructor.error_wrong_numarg ?loc env ~cstr:summary.cstr
              ~expanded:false ~nargs:(Nat.to_int nargs)
              ~expected_nassums ~expected_ndecls:(expected_nassums + nlet) in
        let Exists args' = args_of_concrete args in
        let Refl = Option.get (Nat.is_eq (length args') summary.arity) in
        Exists args'

  let rec get_aux : type i l l' size size_tail .
    (i, l' Nat.succ, l) Nat.plus -> (l, size, size_tail) args -> exists =
  fun plus args ->
    match plus, args with
    | Zero_l, hd :: _ -> Exists hd
    | Succ_plus plus, _ :: tl ->
        get_aux plus tl
    | _ -> .

  module Ops = struct
    let (.%()) (type l) args (Exists plus : l Fin.t) : exists =
      get_aux plus args
  end

  type ('size_a, 'a, 'b) replace = Exists : {
      section : ('size_b, 'b) section;
      diff_a : ('diff, 'a, 'size_a) Nat.plus;
      diff_b : ('diff, 'b, 'size_b) Nat.plus;
    } -> ('size_a, 'a, 'b) replace

  type ('length, 'size_a, 'a, 'b) replace_args = Exists : {
      args : ('length, 'size_b, 'b) args;
      diff_a : ('diff, 'a, 'size_a) Nat.plus;
      diff_b : ('diff, 'b, 'size_b) Nat.plus;
    } -> ('length, 'size_a, 'a, 'b) replace_args

  let rec replace : type size a b . (size, a) section ->
    (size, a, b) replace =
  fun { loc; v = { name; desc }} ->
    match desc with
    | Var ->
        let section = CAst.make ?loc { name; desc = Var } in
        let diff_a = Nat.Succ_plus Nat.Zero_l in
        let diff_b = Nat.Succ_plus Nat.Zero_l in
        Exists { section; diff_a; diff_b }
    | Cstr { cstr; args } ->
        let Exists { args; diff_a; diff_b } = replace_args args in
        let section = CAst.make ?loc { name; desc = Cstr { cstr; args }} in
        Exists {
          section; diff_a = Nat.move_succ_left diff_a;
          diff_b = Nat.move_succ_left diff_b }
  and replace_args :
  type length size a b . (length, size, a) args ->
    (length, size, a, b) replace_args =
  fun args ->
    match args with
    | [] -> Exists { args = []; diff_a = Nat.Zero_l; diff_b = Nat.Zero_l }
    | hd :: tl ->
        let Exists tl = replace_args tl in
        let Exists hd = replace hd in
        let Exists plus = Nat.plus_shift hd.diff_a in
        let diff_a = Nat.plus_assoc_rec tl.diff_a hd.diff_a plus in
        let diff_b = Nat.plus_assoc_rec tl.diff_b hd.diff_b plus in
        Exists { args = hd.section :: tl.args; diff_a; diff_b }

  let rec to_rel_vector_lift : type env env' size size_tail .
        size_tail Nat.t -> (size, size_tail) section ->
          (env * size, env') Lift.t ->
          (env' Rel.t, size, size_tail) Vector.section *
          env' Rel.t =
  fun n { loc; v = { name; desc }} lift ->
    let m : size_tail Nat.succ Nat.t = S n in
    match desc with
    | Var ->
        let self = Rel.of_height (Height.of_nat m) in
        let self = Rel.exliftn lift self in
        [self], self
    | Cstr { args; _ } ->
        let Exists args_diff = diff_of_args args Nat.Diff.zero in
        let Succ_plus _ = Nat.move_succ_left args_diff in
        let self = Rel.zero () |>
          Eq.(cast (Rel.morphism (Env.plus_succ ()))) in
        let self = Rel.exliftn lift self in
        Vector.append_section (args_to_rel_vector_lift m args lift) [self], self
  and args_to_rel_vector_lift : type env length size env' size_tail .
        size_tail Nat.t -> (length, size, size_tail) args ->
          (env * size, env') Lift.t ->
          (env' Rel.t, size, size_tail) Vector.section =
  fun n args lift ->
    match args with
    | [] -> []
    | hd :: tl ->
        let m = size_of_args tl n in
        let Exists hd_diff = diff hd Nat.Diff.zero in
        let lift' = lift |>
          Eq.(cast (Lift.morphism
             (Env.morphism Refl (sym (Env.rev_plus hd_diff)) ++
               sym Env.assoc) Refl)) in
        let lift' = Lift.(Height.of_plus hd_diff & lift') in
        let tl = args_to_rel_vector_lift n tl lift' in
        let hd, _ = to_rel_vector_lift m hd lift in
        Vector.append_section hd tl

  let to_rel_vector : type env size size_tail .
        size_tail Nat.t -> (size, size_tail) section ->
          ((env * size) Rel.t, size, size_tail) Vector.section *
          (env * size) Rel.t =
  fun n v ->
    to_rel_vector_lift n v (Lift.id ())
(*
  let args_to_rel_vector : type env length size size_tail .
        size_tail Nat.t -> (length, size, size_tail) args ->
          ((env * size) Rel.t, size, size_tail) Vector.section =
  fun n args ->
    args_to_rel_vector_lift n args (Lift.id ())
*)
  let rec args_all_vars : type length size size_tail .
        (length, size, size_tail) args -> bool =
  fun args ->
    match args with
    | [] -> true
    | { v = { desc = Var; _ }} :: tl -> args_all_vars tl
    | _ -> false

  type ('env, 'size_tail) of_term = Exists : {
      pattern : ('size, 'size_tail) section;
      terms :  ('env ETerm.t, 'size) Vector.t;
    } -> ('env, 'size_tail) of_term

  type ('length, 'env, 'size, 'size_tail) of_terms_exists = {
      args : ('length, 'size, 'size_tail) args;
      terms : ('env ETerm.t, 'size) Vector.t;
    }

  type ('length, 'env, 'size_tail) of_terms = Exists :
      ('length, 'env, 'size, 'size_tail) of_terms_exists ->
        ('length, 'env, 'size_tail) of_terms [@@ocaml.unboxed]

  let rec of_term : type env size_tail . env Env.t ->
    Evd.evar_map -> env ETerm.t -> (env ETerm.t, size_tail) Vector.t ->
      (env, size_tail) of_term =
  fun env sigma term terms ->
    let term = ETerm.whd_all env sigma term in
    let construct, args = ETerm.decompose_app sigma term in
    match ETerm.destConstruct sigma construct with
    | Some (Exists ctr, _) ->
        let args = Util.List.skipn (nb_params_of_constructor env ctr) args in
        let Exists args =
          Vector.of_list (List.map (fun arg -> true, arg) args) in
        let Exists { args; terms } =
          of_terms_rec env sigma args (term :: terms) in
        let pattern = cstr (Exists ctr) args in
        Exists { pattern; terms }
    | None ->
        let pattern =
          CAst.make { name = Anonymous; desc = Var } in
        Exists { pattern; terms = term :: terms }
  and of_terms_rec :
  type env size_tail length . env Env.t -> Evd.evar_map ->
    (bool * env ETerm.t, length) Vector.t ->
      (env ETerm.t, size_tail) Vector.t ->
      (length, env, size_tail) of_terms =
  fun env sigma args terms ->
    match args with
    | [] -> Exists { args = []; terms }
    | (deep, hd) :: tl ->
        let Exists { args; terms } =
          of_terms_rec env sigma tl terms in
        let Exists { pattern; terms } =
          if deep then
            of_term env sigma hd terms
          else
            let pattern = CAst.make { name = Anonymous; desc = Var } in
            Exists { pattern; terms = hd :: terms } in
        Exists { args = pattern :: args; terms }

  let of_terms (type env length)
      (env : env Env.t) (sigma : Evd.evar_map)
      (terms : (bool * env ETerm.t, length) Vector.t) :
      (length, env, Nat.zero) of_terms =
    let Exists { args; terms } =
      of_terms_rec env sigma terms [] in
    Exists { args; terms = Vector.rev terms }
end

module TomatchType = struct
  (* Constructors None and Some are never used:
     they are here for injectivity. *)

  type none = [`None]

  type 'ind some = [`Some of 'ind]

  type ('env, 'ind, 'params, 'nrealargs, 'nrealdecls) desc = {
        inductive_type :
          ('env, 'ind, 'params, 'nrealargs, 'nrealdecls) InductiveType.t;
        pattern_structure :
          ('nrealargs Nat.succ, 'env, Nat.zero) Pattern.of_terms;
        predicate_pattern : Glob_term.predicate_pattern;
    }

  type ('env, 'ind, 'height) t =
    | Not_inductive : { as_name : Names.Name.t } -> ('env, none, Nat.one) t
    | Inductive : ('env, 'ind, 'params, 'nrealargs, 'nrealdecls) desc ->
          ('env, 'ind some, 'nrealdecls Nat.succ) t

  let exliftn (type a b ind height) (el : (a, b) Lift.t)
      (t : (a, ind, height) t) : (b, ind, height) t =
    match t with
    | Not_inductive { as_name } -> Not_inductive { as_name }
    | Inductive { inductive_type; pattern_structure = Exists { args; terms };
          predicate_pattern } ->
        Inductive { inductive_type = InductiveType.exliftn el inductive_type;
          pattern_structure =
            Exists { args; terms = Vector.map (ETerm.exliftn el) terms };
          predicate_pattern }
end

module TypedPattern = struct
  type ('env, 'ind, 'size) desc =
    | Var : ('env, 'ind, Nat.one) desc
    | Cstr : {
      cstr : ('env, 'ind, 'nrealargs, 'arity, 'args) ConstructorSummary.t;
      args : ('arity, 'size, Nat.zero Nat.succ) Pattern.args;
    } -> ('env, 'ind TomatchType.some, 'size) desc

  type ('env, 'ind, 'size) content = {
      name : Names.Name.t;
      desc : ('env, 'ind, 'size) desc;
    }

  type ('env, 'ind, 'size) t = ('env, 'ind, 'size) content CAst.t

  type ('env, 'ind) exists =
      Exists : ('env, 'ind, 'size) t -> ('env, 'ind) exists [@@ocaml.unboxed]

  let get_var (type env ind size) (pat : (env, ind, size) t) :
      (Names.Name.t * (size, Nat.one) Eq.t) option =
    match pat.v.desc with
    | Var -> Some (pat.v.name, Refl)
    | _ -> None

  let get_name (pat : ('env, 'ind, 'size) t) : Names.Name.t =
    pat.v.name

  let of_var ({ v; loc } : Names.Name.t CAst.t) : ('env, 'ind) exists =
    Exists (CAst.make ?loc { name = v; desc = Var })

  let size (type env ind size) (pat : (env, ind, size) t) : size Nat.t =
    match pat.v.desc with
    | Var -> Nat.one
    | Cstr { args; _ } -> Pattern.size_of_args args Nat.one

  let height pat = Height.of_nat (size pat)

  let unsafe_of_cstr ?loc
      (env : 'env Env.t)
      (cstrs :
         (('env, 'ind, 'nrealargs) ConstructorSummary.exists, 'ind) Tuple.t)
      cstr args name  : ('env, 'ind TomatchType.some) exists =
    let index = Constructor.index cstr in
    let Exists summary = Tuple.Ops.(cstrs.%(index)) in
    let Exists args = Pattern.adjust_args env args summary in
    Exists
      (CAst.make ?loc { name; desc = Cstr { cstr = summary; args }})

(*
  let untype (type env ind size)
      ({ v = { name; desc }; loc } : (env, ind, size) t) :
      size Pattern.t =
    match desc with
    | Var -> CAst.make ?loc Pattern.{ name; desc = Var }
    | Cstr { cstr; args } ->
        let desc = Pattern.Cstr { cstr = Exists cstr.cstr; args } in
        CAst.make ?loc Pattern.{ name; desc }
*)

  let coerce_to ?loc (env : 'env Env.t) cstrs (pat : Glob_term.cases_pattern)
      (pat_ind : _ InductiveDef.t)
      (tgt_ind : 'ind InductiveDef.t) :
      ('env, 'ind TomatchType.some) exists =
    let pat =
      Coercion.inh_pattern_coerce_to ?loc (Eq.cast Env.eq env) pat
        (Eq.cast InductiveDef.eq pat_ind)
        (Eq.cast InductiveDef.eq tgt_ind) in
    match DAst.get pat with
    | PatVar _ -> assert false
    | PatCstr (cstr, args, alias) ->
        let Exists cstr = Constructor.of_concrete cstr in
        let eq = Option.get
          (InductiveDef.equal (Constructor.inductive cstr) tgt_ind) in
        let cstr = Eq.cast (Constructor.morphism eq) cstr in
        unsafe_of_cstr env cstrs cstr args alias

  type ('a, 'b) map = {
      f : 'ind 'arity 'nrealargs 'args .
        ('a, 'ind, 'arity, 'nrealargs, 'args) ConstructorSummary.t ->
          ('b, 'ind, 'arity, 'nrealargs, 'args) ConstructorSummary.t
    }

  let map (type a b ind size) f (p : (a, ind, size) t) : (b, ind, size) t =
    match p with
    | { v = { name; desc }; loc } ->
        let desc : (b, ind, size) desc =
          match desc with
          | Var -> Var
          | Cstr { cstr; args } -> Cstr { cstr = f.f cstr; args } in
        CAst.make ?loc { name; desc }

  let exliftn el p =
    map { f = fun cstr -> ConstructorSummary.exliftn el cstr } p

  let lift n p = map { f = fun cstr -> ConstructorSummary.lift n cstr } p

  let check
      (type env ind params nrealargs nrealdecls size size_tail)
      (env : env Env.t)
      (cstrs : ((env, ind, nrealargs) ConstructorSummary.exists, ind) Tuple.t)
      (ind_type : (env, ind, params, nrealargs, nrealdecls) InductiveType.t)
      (({ v; loc } as pat) : (size, size_tail) Pattern.section) :
      (env, ind TomatchType.some) exists =
    match v.desc with
    | Var ->
        of_var (CAst.make ?loc v.name)
    | Cstr { cstr = Exists cstr; args } ->
        let ind, _ = ind_type.family.def in
        let ind' = Constructor.inductive cstr in
        match InductiveDef.equal ind' ind with
        | Some eq ->
            let cstr = Eq.cast (Constructor.morphism eq) cstr in
            let args = Vector.to_list (Pattern.args_to_concrete args) in
            unsafe_of_cstr env cstrs cstr args v.name
        | None ->
            try
              coerce_to ?loc env cstrs (Pattern.to_concrete pat) ind' ind
            with Not_found ->
              Constructor.error_bad ?loc env cstr ind
end

module type IndSizedTypeS = sig
  include Type3S

  val height : ('env, 'ind, 'size) t -> 'size Height.t
end

module IndSizeAnnotation (S : Type3S) = struct
  type ('env, 'annot, 'annot_tail) t =
      I : ('env, 'ind, 'size) S.t ->
        ('env, < ind: 'ind * 'ind_tail; size: 'size * 'size_tail>,
         <ind: 'ind_tail; size: 'size_tail>) t

  type 'env unit_annot = <ind: unit; size: Nat.zero>
end

module IndSizeVector (S : IndSizedTypeS) = struct
  module A = IndSizeAnnotation(S)

  include AnnotatedVector.Make (A)


  let tl (type env length ind ind_tail size size_tail end_annot)
      (v : (env, length Nat.succ, <ind: ind * ind_tail; size: size * size_tail>,
         end_annot) section) :
      (env, length, <ind: ind_tail; size: size_tail>, end_annot) section =
    match v with
    | I _ :: tl -> tl

  let rec height : type env length ind size .
        (env, length, <ind: ind; size: size>) t -> size Height.t = fun v ->
    match v with
    | [] -> Height.zero
    | I hd :: tl -> Height.add (S.height hd) (height tl)

  let rec partial_height : type env length annot height end_annot end_height .
        (env, length, <ind: annot; size: height>,
          <ind:end_annot; size: end_height>) section->
            (height, end_height) Height.diff = fun v ->
    match v with
    | [] -> Height.diff_zero
    | I hd :: tl -> Height.diff_add (S.height hd) (partial_height tl)

  type ('env, 'a) concat_map_f = {
    f : 'annot 'height .
        ('env, 'annot, 'height) S.t -> ('a, 'height) Vector.t
  }

  let rec concat_rev_map_rec : type length annot height accu .
    ('env, 'a) concat_map_f -> ('env, length, <ind: annot; size: height>) t ->
      ('a, accu) Height.Vector.t ->
      ('a, height * accu) Height.Vector.t =
  fun f v accu ->
    match v with
    | [] ->
        let Exists { vector; eq } = accu in
        Exists { vector; eq = Eq.(Env.zero_l ++ eq) }
    | I hd :: tl ->
       let hd' = f.f hd in
       let Exists { vector = tl; eq } =
         concat_rev_map_rec f tl accu in
       let Exists { vector; plus; _ } = Vector.rev_append hd' tl in
       Exists { vector;
         eq = Eq.(Env.assoc ++ Env.morphism Refl eq ++ Env.plus plus) }

  let concat_rev_map (type length annot height)
    (f : ('env, 'a) concat_map_f)
      (v : ('env, length, <ind: annot; size: height>) t) :
      ('a, height) Height.Vector.t =
    let Exists { vector; eq } =
      concat_rev_map_rec f v (Height.Vector.of_vector []) in
    Exists { vector; eq = Eq.(sym Env.zero_r ++ eq) }

(*
  type ('env, 'length, 'annot, 'end_annot, 'size0, 'end_size0, 'end_size1)
        resize =
      Exists : {
      section :
        ('env, 'length, <ind: 'annot; size: 'size1>,
          <ind: 'end_annot; size: 'end_size1>) section;
      diff0 : ('diff * 'end_size0, 'size0) Height.eq;
      diff1 : ('diff * 'end_size1, 'size1) Height.eq;
    } ->
      ('env, 'length, 'annot, 'end_annot, 'size0, 'end_size0, 'end_size1) resize

  let rec resize : type length annot end_annot size0 end_size0 end_size1 .
        ('env, length, <ind: annot; size: size0>,
          <ind: end_annot; size: end_size0>) section ->
            ('env, length, annot, end_annot, size0, end_size0, end_size1)
              resize =
  fun section ->
    match section with
    | [] -> Exists { section = []; diff0 = Env.zero_l; diff1 = Env.zero_l }
    | I hd :: tl ->
        let Exists { section; diff0; diff1 } = resize tl in
        Exists {
          section = I hd :: section;
          diff0 = Eq.(Env.assoc ++ Env.morphism Refl diff0);
          diff1 = Eq.(Env.assoc ++ Env.morphism Refl diff1);
      }
*)
end

module IndSizeNatAnnotation (S : Type3S) = struct
  type ('env, 'annot, 'annot_tail) t =
      I : ('env, 'ind, 'size) S.t * ('size, 'size_tail, 'sum) Nat.plus ->
        ('env, <ind: 'ind * 'ind_tail; size: 'sum>,
         <ind: 'ind_tail; size: 'size_tail>) t

  type 'env unit_annot = <ind: unit; size: Nat.zero>
end

module IndSizeNatVector (S : IndSizedTypeS) = struct
  module A = IndSizeNatAnnotation(S)

  include AnnotatedVector.Make (A)

  let rec size : type env length ind size .
        (env, length, <ind: ind; size: size>) t -> size Nat.t = fun v ->
    match v with
    | [] -> Nat.O
    | I (hd, plus) :: tl -> Nat.plus_nat plus (size tl)

(*
  type ('env, 'a) concat_map_f = {
    f : 'annot 'size . ('env, 'annot, 'size) S.t -> ('a, 'size) Vector.t
  }

  let rec concat_map : type length annot size .
    ('env, 'a) concat_map_f -> ('env, length, <ind: annot; size: size>) t ->
      ('a, size) Vector.t =
  fun f v ->
    match v with
    | [] -> []
    | I (hd, plus) :: tl ->
       let hd = f.f hd in
       let tl = concat_map f tl in
       Vector.append_plus hd tl plus
*)

  type ('env, 'length, 'annot, 'end_annot, 'size0, 'end_size0, 'end_size1)
        resize =
      Exists : {
      section :
        ('env, 'length, <ind: 'annot; size: 'size1>,
          <ind: 'end_annot; size: 'end_size1>) section;
      diff0 : ('diff, 'end_size0, 'size0) Nat.plus;
      diff1 : ('diff, 'end_size1, 'size1) Nat.plus;
    } ->
      ('env, 'length, 'annot, 'end_annot, 'size0, 'end_size0, 'end_size1) resize

  let rec resize : type length annot end_annot size0 end_size0 end_size1 .
        ('env, length, <ind: annot; size: size0>,
          <ind: end_annot; size: end_size0>) section ->
            ('env, length, annot, end_annot, size0, end_size0, end_size1)
              resize =
  fun section ->
    match section with
    | [] -> Exists { section = []; diff0 = Zero_l; diff1 = Zero_l }
    | I (hd, plus) :: tl ->
        let Exists tl = resize tl in
        let Exists plus_diff = Nat.plus_shift plus in
        let Exists plus_hd = Nat.plus_shift plus in
        let diff0 = Nat.plus_assoc_rec tl.diff0 plus plus_diff in
        let diff1 = Nat.plus_assoc_rec tl.diff1 plus_hd plus_diff in
        Exists { section = I (hd, plus_hd) :: tl.section; diff0; diff1 }
end

module Patterns = struct
  include IndSizeNatVector (TypedPattern)

  type ('env, 'length, 'ind, 'end_ind, 'end_size) exists_section =
      Exists :
        ('env, 'length, <ind: 'ind; size: 'size>,
          <ind: 'end_ind; size: 'end_size>) section ->
            ('env, 'length, 'ind, 'end_ind, 'end_size) exists_section
              [@@ocaml.unboxed]

  let lift n v =
    map { f = fun (type a t) (I (p, sum) : (_, a, t) A.t) : (_, a, t) A.t ->
      I (TypedPattern.lift n p, sum) } v

  let exliftn el v =
    map { f = fun (type a t) (I (p, sum) : (_, a, t) A.t) : (_, a, t) A.t ->
      I (TypedPattern.exliftn el p, sum) } v
end

module Tomatch = struct
  type ('env, 'ind, 'height) t = {
      judgment : 'env EJudgment.t;
      inductive_type : ('env, 'ind, 'height) TomatchType.t;
      return_pred_context : ('env, 'height) ERelContext.with_height;
      return_pred_height : 'height Height.t;
    }

  let height t = t.return_pred_height

  let exliftn (type a b ind height) (el : (a, b) Lift.t)
      (tomatch : (a, ind, height) t) :
      (b, ind, height) t =
    let Exists return_context = tomatch.return_pred_context in
    let context = ERelContext.exliftn el return_context.context in
    { judgment = EJudgment.exliftn el tomatch.judgment;
      inductive_type = TomatchType.exliftn el tomatch.inductive_type;
      return_pred_context = Exists { return_context with context };
      return_pred_height = tomatch.return_pred_height; }

  let make_not_inductive (type env) (judgment : env EJudgment.t) as_name =
    { judgment;
      inductive_type = Not_inductive { as_name };
      return_pred_height = Height.one;
      return_pred_context =
        ERelContext.with_height [
          EDeclaration.assum
            (Context.make_annot as_name Relevant)
            (Eq.cast (ETerm.morphism (Eq.sym Env.zero_r))
              (EJudgment.uj_type judgment))];
    }

  let make_inductive (type env ind params nrealargs nrealdecls)
      ~(small_inversion : bool)
      (env : env Env.t) sigma (judgment : env EJudgment.t)
      (inductive_type :
         (env, ind, params, nrealargs, nrealdecls) InductiveType.t)
      (predicate_pattern : Glob_term.predicate_pattern) =
    let arity = InductiveFamily.get_arity env inductive_type.family in
    let as_name, in_names = predicate_pattern in
    let ty =
      InductiveFamily.build_dependent_inductive env
        inductive_type.family in
    let arity_length = ERelContext.length arity in
    let arity =
      match in_names with
      | None -> arity
      | Some { loc; v = (_ind, names) } ->
          let names =
            Option.get (Vector.of_list_of_length names arity_length) in
          ERelContext.set_names (Vector.rev names) arity in
    let return_pred_context : (_, _, _) ERelContext.t =
      EDeclaration.assum
        (Context.make_annot as_name Relevant) ty :: arity in
    let return_pred_height = Height.of_nat (S arity_length) in
    let pattern_structure =
      let terms : _ Vector.t =
        Vector.map_append_plus (fun term -> small_inversion, term)
          inductive_type.realargs
          [false, EJudgment.uj_val judgment]
          (Nat.plus_one inductive_type.family.nrealargs) in
      Pattern.of_terms env sigma terms in
    { judgment;
      inductive_type =
        Inductive { inductive_type; pattern_structure; predicate_pattern };
      return_pred_context = ERelContext.with_height return_pred_context;
      return_pred_height
    }

  let change (type env ind height) ~small_inversion (env : env Env.t) sigma
      (judgment : env EJudgment.t) (tomatch : (_, ind, height) t) :
      (env, ind, height) t =
    match tomatch.inductive_type with
    | Not_inductive { as_name } -> make_not_inductive judgment as_name
    | Inductive { inductive_type; predicate_pattern; _ } ->
        match
          InductiveType.of_term_opt_whd_all env sigma
            (EJudgment.uj_type judgment)
        with
        | None -> assert false
        | Some (Exists indt) ->
            let Refl =
              InductiveFamily.ind_fun inductive_type.family indt.family in
            make_inductive ~small_inversion env sigma judgment indt
              predicate_pattern
end

module TomatchVector = struct
  include IndSizeVector (Tomatch)

  let exliftn el tomatches =
    map { f = fun (type a t) (I t : (_, a, t) A.t) : (_, a, t) A.t ->
      I (Tomatch.exliftn el t) } tomatches

  let lift n tomatches =
    exliftn Lift.(+ n) tomatches

  type ('env, 'return_pred_height) make_return_pred_context =
      Exists : {
        context : ('env, 'return_pred_height, 'length, 'nb_args)
          ERelContext.with_height_desc;
        length : 'length Nat.t;
        nb_args : 'nb_args Nat.t; } ->
          ('env, 'return_pred_height) make_return_pred_context

(*
  let context (type env return_pred_height)
      (Exists { context; _ } :
         (env, return_pred_height) make_return_pred_context) :
      (env, return_pred_height) ERelContext.with_height =
    Exists context
*)

  let rec make_return_pred_context :
  type env length annot return_pred_height .
        (env, length, <ind: annot; size: return_pred_height>) t ->
          (env, return_pred_height) make_return_pred_context =
  fun tomatchl ->
    match tomatchl with
    | [] ->
        Exists {
          context = { context = []; eq = Refl };
          length = Nat.O;
          nb_args = Nat.O;
      }
    | I { return_pred_context = Exists return_pred_context;
        return_pred_height; _ } :: tl ->
        let hd_length = ERelContext.length return_pred_context.context in
        let nb_args = ERelContext.nb_args return_pred_context.context in
        let Exists tl = make_return_pred_context tl in
        let Exists { sum = length; plus } = Nat.add tl.length hd_length in
        let Exists { sum = nb_args; plus = plus_nb } =
          Nat.add tl.nb_args nb_args in
        let context =
          ERelContext.push_plus
            (ERelContext.lift (Height.of_nat hd_length)
              tl.context.context) return_pred_context.context
            plus plus_nb in
        let eq =
          Eq.(sym (Env.rev_plus plus) ++
            (Env.morphism return_pred_context.eq tl.context.eq)) in
        Exists { context = { context; eq }; length; nb_args }
    | _ -> .

  let rec make_self_vector :
  type env length annot return_pred_height .
        (env, length, <ind: annot; size: return_pred_height>) t ->
          return_pred_height Height.t *
            ((env * return_pred_height) ETerm.t, length) Vector.t =
  fun tomatchl ->
    match tomatchl with
    | [] -> Height.zero, []
    | I { judgment; inductive_type; return_pred_height; _ } :: tl ->
          let tl_height, tl = make_self_vector tl in
          let tl =
            Vector.map (ETerm.liftn return_pred_height tl_height) tl |>
            Eq.(cast (Vector.eq (ETerm.morphism Env.assoc))) in
          let height = Height.Ops.(return_pred_height + tl_height) in
          let hd =
            match inductive_type with
            | Not_inductive _as_name ->
                ETerm.lift height (EJudgment.uj_val judgment)
            | Inductive _ ->
                ETerm.mkReln (Rel.zero ()) tl_height |>
                Eq.(cast (ETerm.morphism (
                  Env.morphism (Env.plus_succ ()) Refl ++
                  Env.assoc))) in
          height, hd :: tl

  let rec change :
  type env length annot return_pred_height .
  small_inversion:bool -> env Env.t -> Evd.evar_map ->
    (env EJudgment.t, length) Vector.t ->
      (env, length, <ind: annot; size: return_pred_height>) t ->
        (env, length, <ind: annot; size: return_pred_height>) t =
  fun ~small_inversion env sigma new_tomatches tomatches ->
    match new_tomatches, tomatches with
    | [], [] -> []
    | hd :: tl, I hd' :: tl' ->
        let hd = Tomatch.change ~small_inversion env sigma hd hd' in
        I hd :: change ~small_inversion env sigma tl tl'
end

module Rhs = struct
  type ('env, 'matches, 'nrealdecls, 'nrealargs) args = {
      globenv : ('env * 'nrealdecls) GlobalEnv.t;
      context : ('env, 'nrealdecls, 'nrealargs) ERelContext.t;
      return_pred : ('env * 'nrealdecls) ETerm.t;
      matches : (('env * 'nrealdecls) ETerm.t, 'matches) Vector.t;
    }

  type ('env, 'matches, 'nrealdecls, 'nrealargs) f =
      ('env, 'matches, 'nrealdecls, 'nrealargs) args ->
          ('env * 'nrealdecls) EJudgment.t EvarMapMonad.t

  type ('env, 'matches) poly = {
      f : 'nrealdecls 'nrealargs .
        ('env, 'matches, 'nrealdecls, 'nrealargs) f;
    } [@@ocaml.unboxed]

  type ('env, 'length, 'matched, 'matches) cont = {
      length : 'length Nat.t;
      sum : ('matched, 'length, 'matches) Nat.plus;
      f : ('env, 'matches) poly;
    }

  type ('env, 'length, 'matched, 'matches) desc = {
      matches : ('env ETerm.t, 'matched) Vector.t;
      cont : ('env, 'length, 'matched, 'matches) cont;
    }

  type ('env, 'length) t = Exists :
        ('env, 'length, 'matched, 'matches) desc -> ('env, 'length) t
            [@@ocaml.unboxed]

  type ('env, 'nrealdecls) untyped_args = {
      globenv : ('env * 'nrealdecls) GlobalEnv.t;
      return_pred : ('env * 'nrealdecls) ETerm.t;
    }

  type ('env, 'nrealdecls) untyped_f =
      ('env, 'nrealdecls) untyped_args ->
          ('env * 'nrealdecls) EJudgment.t EvarMapMonad.t

  type 'env untyped_poly = {
      f : 'nrealdecls .
        ('env, 'nrealdecls) untyped_f;
    } [@@ocaml.unboxed]

  let make (type env length) (length : length Nat.t)
      (f : (env, length) poly) : (env, length) t =
    Exists { matches = []; cont = { length; sum = Nat.Zero_l; f }}

  let length (type env length) (Exists rhs : (env, length) t) : length Nat.t =
    rhs.cont.length

  let morphism (type a b length) (eq : (a, b) Height.eq) (rhs : (a, length) t) :
      (b, length) t =
    let Exists { matches; cont = { length; sum; f }} = rhs in
    let matches = Eq.cast (Vector.eq (ETerm.morphism eq)) matches in
    let f { globenv; context; return_pred; matches } =
      let open EvarMapMonad.Ops in
      let eq' = Env.morphism (Eq.sym eq) Refl in
      let args = {
        globenv = Eq.cast (GlobalEnv.morphism eq') globenv;
        context = ERelContext.morphism (Eq.sym eq) context;
        return_pred = Eq.cast (ETerm.morphism eq') return_pred;
        matches = Eq.cast (Vector.eq (ETerm.morphism eq')) matches;
      } in
      let* result = f.f args in
      return (Eq.cast (EJudgment.morphism (Env.morphism eq Refl)) result) in
    Exists { matches; cont = { length; sum; f = { f }}}

  let consume (type env length) (matched : env Nat.succ ETerm.t)
      (rhs : (env, length Nat.succ) t)
      (j : env EJudgment.t) : (env Nat.succ, length) t =
    let Exists { matches; cont = { length; sum; f }} = rhs in
    let matches : _ Vector.t =
      matched ::
      Eq.(cast (Vector.eq (ETerm.morphism Env.succ)))
      (Vector.map (ETerm.lift Height.one) matches) in
    let f (type nrealdecls nrealargs) :
        (env Nat.succ, _, nrealdecls, nrealargs) f =
    fun { globenv; context; return_pred; matches } ->
      let open EvarMapMonad.Ops in
      let context = ERelContext.morphism (Eq.sym Env.succ) context in
      let j = Eq.(cast (EJudgment.morphism (sym Env.zero_r))) j in
      let Exists push =
        ERelContext.push context [EDeclaration.local_def Context.anonR j] in
      let Succ_plus Zero_l = Nat.plus_commut Nat.one push.decls in
      let eq' = Eq.(Env.morphism (sym Env.succ) Refl ++ Env.assoc ++
        Env.morphism Refl Env.rev_succ) in
      let args = {
        globenv = Eq.cast (GlobalEnv.morphism eq') globenv;
        context = push.context;
        return_pred = Eq.cast (ETerm.morphism eq') return_pred;
        matches = Eq.cast (Vector.eq (ETerm.morphism eq')) matches;
      } in
      let* result = f.f args in
      return (Eq.(cast (EJudgment.morphism (sym eq'))) result) in
    let sum = Nat.move_succ_left sum in
    Exists { matches; cont = { length = Nat.pred length; sum; f = { f }}};;

  let produce (type base m n env length length')
      (npb : (n, base, length) Nat.plus)
      (mpl : (m, length, length') Nat.plus)
      (rhs : (env, length) t) :
      (env, length') t =
    let Exists { matches; cont = { length; sum; f }} = rhs in
    let length' = Nat.plus_nat mpl length in
    let Exists sum' = Nat.plus_shift sum in
    let m = Nat.plus_l mpl in
    let Exists npm = Nat.plus_shift npb in
    let Exists mpb = Nat.to_plus m in
    let Exists npl = Nat.plus_shift npb in
    let npmpb = Nat.plus_assoc_rec mpb npl npm in
    let mpn = Nat.plus_commut m npm in
    let mpnpb = Nat.plus_assoc_rec npb mpl mpn in
    let eq = Nat.plus_fun mpnpb npmpb in
    let f (type nrealdecls nrealargs) :
        (env, _, nrealdecls, nrealargs) f =
    fun args ->
      let others, matched =
        Vector.cut (Nat.plus_commut length' sum') args.matches in
      let vn, tl = Vector.cut npl (Eq.cast (Vector.eq_length eq) others) in
      let _, tl  = Vector.cut mpb tl in
      let matches = Vector.append_plus vn tl npb in
      let matches =
        Vector.append_plus matches matched (Nat.plus_commut length sum) in
      f.f { args with matches } in
    Exists { matches; cont = { length = length'; sum = sum'; f = { f }}}

  let push_cont (type env length matched matches nrealdecls nrealargs)
      (context' : (env, nrealdecls, nrealargs) ERelContext.t)
      (rhs : (env, length, matched, matches) cont) :
      (env * nrealdecls, length, matched, matches) cont =
    let open EvarMapMonad.Ops in
    let { length; sum; f } = rhs in
    let f (type nrealdecls' nrealargs') :
        (env * nrealdecls, _, nrealdecls', nrealargs') f =
    fun { globenv; context; return_pred; matches } ->
      let Exists push = ERelContext.push context context' in
      let eq' = Eq.(
        Env.assoc ++ Env.morphism Refl (Env.rev_plus push.decls)) in
      let args = {
        globenv = Eq.cast (GlobalEnv.morphism eq') globenv;
        context = push.context;
        return_pred = Eq.cast (ETerm.morphism eq') return_pred;
        matches = Eq.cast (Vector.eq (ETerm.morphism eq')) matches;
      } in
      let* result = f.f args in
      return (Eq.(cast (EJudgment.morphism (sym eq'))) result) in
    { length; sum; f = { f }}

(*
  let push (type env length nrealdecls nrealargs)
      (context' : (env, nrealdecls, nrealargs) ERelContext.t)
      (rhs : (env, length) t) : (env * nrealdecls, length) t =
    let Exists { matches; cont } = rhs in
    let matches =
      Vector.map (ETerm.lift (Height.of_nat (ERelContext.length context')))
        matches in
    let cont = push_cont context' cont in
    Exists { matches; cont }
*)
end

module Clause = struct
  type ('env, 'pats, 'rhs) desc = {
      env : 'env GlobalEnv.t;
      ids : Names.Id.Set.t;
      pats : 'pats;
      rhs : 'rhs;
    }

  type ('env, 'pats, 'height) content =
      ('env, 'pats, 'height) desc CAst.t

  type ('env, 'length) untyped =
    | Exists :
        ('env, ('length, 'height, Nat.zero) Pattern.args,
          'env Rhs.untyped_poly) content ->
             ('env, 'length) untyped

  type ('env, 'length, 'ind) t =
      Exists :
        ('env, ('env, 'length, <ind: 'ind; size: 'height>) Patterns.t,
          ('env, 'height) Rhs.t) content ->
            ('env, 'length, 'ind) t [@@ocaml.unboxed]

  let check (type height_pat height_rhs) ?loc
      (clause :
        ('env, ('env, 'length, <ind: 'ind; size: height_pat>) Patterns.t,
          ('env, height_rhs) Rhs.t) desc) =
    let size_pat = Patterns.size clause.pats in
    let Refl = Option.get (Nat.is_eq size_pat (Rhs.length clause.rhs)) in
    Exists (CAst.make ?loc clause)

  let extract_pat_var (type env length head tail)
      (Exists clause : (env, length, head * tail) t) :
      Names.Name.t option =
    match clause.v.pats with
    | I (head, _sum) :: _ -> Option.map fst (TypedPattern.get_var head)

  let is_catch_all (type env length ind)
      (Exists eqn : (env, length, ind) t) =
    eqn.v.pats |> Patterns.for_all { f = fun (type annot annot_tail)
        (I (pat, _) : (_, annot, annot_tail) Patterns.A.t) ->
      match pat.v.desc with
      | Var -> true
      | Cstr _ -> false }

  let rec remove_trailing_eqns : type env length ind .
      (env, length, ind) t list -> (env, length, ind) t list =
  fun eqns ->
    match eqns with
    | [] -> []
    | eqn :: eqns ->
        if is_catch_all eqn then [eqn]
        else eqn :: remove_trailing_eqns eqns
end

let substn_binders (type env n level length diff)
    (env : (env * n) Env.t) sigma
    (n : n Height.t)
    (diff : diff Height.t)
    (plus : (level, diff, length) Nat.plus)
(*
    (subst : ((env * level) ETerm.t, length) Vector.t)
*)
    (subst_vector : (env ETerm.t, length) Vector.t)
    (term : (env * n) ETerm.t) : ((env * length) * n) ETerm.t * bool =
  let length = Height.of_nat (Vector.length subst_vector) in
  let term' = ETerm.liftn length n term in
  let modified = ref false in
  let subst (type h) (h : h Height.t) (t : (((env * length) * n) * h) ETerm.t) :
      (((env * length) * n) * h) ETerm.t option =
    let open Monad.Option.Ops in
    let* j =
      subst_vector |> Vector.findi (fun j (subst_t : env ETerm.t) ->
        let subst_t = subst_t |>
          ETerm.exliftn Lift.(length & n & + h) in
        if ETerm.equal sigma t subst_t then
          begin
            modified := true;
            Some j
          end
        else
          None) in
    return (ETerm.exliftn Lift.(n & + h) (ETerm.mkRel (Rel.of_fin j))) in
  let term' = ETerm.subst sigma { f = subst } term' in
  if !modified then
    term', true
  else
    ETerm.liftn length n term, false

let subst_binders (type env level length diff) (env : env Env.t) sigma
    (diff : diff Height.t)
    (plus : (level, diff, length) Nat.plus)
    (subst : (env ETerm.t, length) Vector.t)
    (term : env ETerm.t) : (env * length) ETerm.t * bool =
  let env =
    Eq.(cast (sym Env.zero_r)) env in
  let term, modified =
    substn_binders env sigma Height.zero diff plus subst
      Eq.(cast (ETerm.morphism (sym Env.zero_r)) term) in
  Eq.(cast (ETerm.morphism Env.zero_r) term), modified

module ReturnPred = struct
  type ('env, 'return_pred_height, 'previous) desc = {
      return_pred : (('env * 'previous) * 'return_pred_height) ETerm.t;
      height : 'return_pred_height Height.t;
      generalize : bool;
      previous : ('env ETerm.t, 'previous) Vector.t;
    }

  type ('env, 'return_pred_height) t = Exists :
        ('env, 'return_pred_height, 'previous) desc ->
          ('env, 'return_pred_height) t [@@ocaml.unboxed]

  let make ?(generalize = false) return_pred height =
    let return_pred = return_pred |>
      Eq.(cast (ETerm.morphism (Env.morphism (sym Env.zero_r) Refl))) in
    Exists { return_pred; height; generalize; previous = [] }

  let get (Exists { return_pred; height; previous; _ }) =
    ETerm.substnl (Height.Vector.of_vector previous) height return_pred

(*
  let check_generalize (Exists { generalize; _ }) =
    generalize
*)

  let morphism (type a b c d) (eq_env : (a, b) Height.eq)
      (eq_height : (c, d) Height.eq) (t : (a, c) t) : (b, d) t =
    let Exists ({ return_pred; height; previous; _ } as desc) = t in
    let return_pred = return_pred |> Eq.(cast (ETerm.morphism (
      Env.morphism (Env.morphism eq_env Refl) eq_height))) in
    let height = Eq.(cast (Height.morphism eq_height)) height in
    let previous = Eq.(cast (Vector.eq (ETerm.morphism eq_env))) previous in
    Exists { desc with return_pred; height; previous }

  let map (type a b return_pred_height) (f : (a, b) ETerm.map)
      (return_pred : (a, return_pred_height) t) :
      (b, return_pred_height) t =
    let Exists ({ return_pred; height; previous; _ } as desc) = return_pred in
    let return_pred = return_pred |>
      Eq.(cast (ETerm.morphism Env.assoc)) |>
      f.f (Height.Ops.(
        Height.of_nat (Vector.length previous) + height)) |>
      Eq.(cast (ETerm.morphism (sym Env.assoc))) in
    let previous = previous |> Vector.map (
      Eq.(cast (ETerm.morphism Env.zero_r ^-> ETerm.morphism Env.zero_r))
        (f.f Height.zero)) in
    Exists { desc with return_pred; previous }

  let substnl (type env n l return_pred_height)
      (v : (env ETerm.t, l) Height.Vector.t) (n : n Height.t)
      (return_pred : ((env * l) * n, return_pred_height) t) :
      (env * n, return_pred_height) t =
    return_pred |> map { f =
    fun (type h) (h : h Height.t) (term : (((env * l) * n) * h) ETerm.t) :
      ((env * n) * h) ETerm.t ->
      Eq.(cast (sym (ETerm.morphism Env.assoc ^-> ETerm.morphism Env.assoc)))
        (ETerm.substnl v Height.Ops.(n + h)) term }

(*
  let substl (type env l return_pred_height)
      (v : (env ETerm.t, l) Height.Vector.t)
      (return_pred : ((env * l), return_pred_height) t) :
      (env, return_pred_height) t =
    return_pred |> map { f =
    fun (type h) (h : h Height.t) (term : ((env * l) * h) ETerm.t) :
      (env * h) ETerm.t ->
      ETerm.substnl v h term }
*)

  let exliftn el return_pred =
    map
      { f = fun height term -> ETerm.exliftn Lift.(liftn height el) term }
      return_pred

  let lift n return_pred = exliftn Lift.(+ n) return_pred

  let lift_return n t =
    let Exists ({ return_pred; height; _ } as desc) = t in
    let return_pred = return_pred |>
      ETerm.liftn n height |> Eq.(cast (ETerm.morphism Env.assoc)) in
    Exists { desc with return_pred; height = Height.Ops.(n + height) }

  let generalize (type env return_pred_height level diff length previous)
      ~hypnaming
      (globenv : env GlobalEnv.t) sigma
      (Exists context : (env, return_pred_height) ERelContext.with_height)
      (diff : diff Height.t)
      (plus : (level, diff, length) Nat.plus)
      (subst : (env ETerm.t, length) Vector.t)
      (new_previous : ((env * length) ETerm.t, previous) Vector.t)
      (desc : (env, return_pred_height, previous) desc) :
      (env * length, return_pred_height) t =
    let { return_pred; height; previous; generalize } = desc in
    let length = Height.of_nat (Vector.length subst) in
    if generalize then
      let previous_types =
        Vector.map (ETerm.retype_of (GlobalEnv.env globenv) sigma) previous in
      let previous_context = ERelContext.of_vector previous_types in
      let previous_height = Height.of_nat (Vector.length previous) in
      let context' = ERelContext.lift previous_height context.context in
      let Exists context'' = ERelContext.push context' previous_context in
      let globenv =
        GlobalEnv.push_rel_context ~hypnaming sigma
          (ERelContext.with_height context''.context) globenv in
      let n = Height.of_nat (ERelContext.length context''.context) in
      let return_pred =
        Eq.(cast (ETerm.morphism (Env.assoc ++
          Env.morphism Refl (Env.morphism Refl (sym context.eq) ++
            Env.rev_plus context''.decls)))) return_pred in
      let return_pred, _ =
        substn_binders (GlobalEnv.env globenv) sigma n diff plus subst
          return_pred in
      let return_pred = return_pred |> Eq.(cast (ETerm.morphism (
        Env.morphism Refl (sym (Env.rev_plus context''.decls)) ++
        sym Env.assoc ++ Env.morphism Refl context.eq))) in
      Exists { desc with return_pred; previous = new_previous }
    else
      let previous_height = Height.of_nat (Vector.length previous) in
      let return_pred = return_pred |>
        Eq.(cast (sym (ETerm.morphism Env.assoc ^-> ETerm.morphism Env.assoc)))
          (ETerm.liftn length (Height.Ops.(previous_height + height))) in
      Exists { desc with return_pred; previous = new_previous }

  let print (type env return_pred_height) ~hypnaming
      (globenv : env GlobalEnv.t) sigma
      (Exists context : (env, return_pred_height) ERelContext.with_height)
      (Exists { return_pred; height; previous; _ } :
         (env, return_pred_height) t) =
    let previous_types =
      Vector.map (ETerm.retype_of (GlobalEnv.env globenv) sigma) previous in
    let previous_context = ERelContext.of_vector previous_types in
    let previous_height = Height.of_nat (Vector.length previous) in
    let context' = ERelContext.lift previous_height context.context in
    let Exists context'' = ERelContext.push context' previous_context in
    let globenv' =
      GlobalEnv.push_rel_context ~hypnaming sigma
        (ERelContext.with_height context''.context) globenv |>
      Eq.(cast (GlobalEnv.morphism (Env.morphism Refl
        (sym (Env.rev_plus context''.decls) ++
          Env.morphism Refl context.eq) ++ sym Env.assoc))) in
    Pp.(
      str "previous:" ++ spc () ++
      pr_enum (ETerm.print (GlobalEnv.env globenv) sigma)
        (Vector.to_list previous) ++
      Pp.cut () ++
      str "return pred:" ++ ETerm.print (GlobalEnv.env globenv') sigma
        return_pred)
  [@@ocaml.warning "-32"] (* can be unused *)

  let debug_print (Exists { return_pred; previous; _ }) =
    Pp.(
      str "previous:" ++ spc () ++
      pr_enum ETerm.debug_print (Vector.to_list previous) ++
      Pp.cut () ++
      str "return pred:" ++ ETerm.debug_print return_pred)
  [@@ocaml.warning "-32"] (* can be unused *)

  let apply (type env args tail_height)
      (args : (env ETerm.t, args) Vector.t)
      (tail_height : tail_height Height.t)
      (return_pred : (env, args * tail_height) t) : (env, tail_height) t =
    let Exists ({ return_pred; height; previous; _ } as t) = return_pred in
    let Exists { vector = previous; plus } = Vector.rev_append args previous in
    let return_pred = return_pred |>
      Eq.(cast (ETerm.morphism (
        sym Env.assoc ++ Env.morphism (Env.assoc ++
          Env.morphism Refl (Env.rev_plus plus)) Refl))) in
    Exists { t with return_pred; height = tail_height; previous }
end

module PatternMatchingProblem = struct
  type ('env, 'tomatch_length, 'tomatch_ind, 'eqn_length,
      'return_pred_height, 'previously_bounds) t = {
      env : 'env GlobalEnv.t;
      tomatches :
        ('env, 'tomatch_length, <ind: 'tomatch_ind; size: 'return_pred_height>)
        TomatchVector.t;
      eqns :
        (('env, 'tomatch_length, 'tomatch_ind) Clause.t, 'eqn_length) Vector.t;
      return_pred : ('env, 'return_pred_height) ReturnPred.t;
      previously_bounds : ('env Rel.t, 'previously_bounds) Vector.t;
      expand_self : bool;
    }
end

module PrepareTomatch (EqnLength : Type) = struct
  module TomatchWithContext = struct
    type ('env, 'ind, 'return_height) t = {
        tomatch : ('env, 'ind, 'return_height) Tomatch.t;
        pats : (('env, 'ind) TypedPattern.exists, EqnLength.t) Vector.t;
      }

    type 'env exists =
        Exists : ('env, 'ind, 'height) t -> 'env exists [@@ocaml.unboxed]

    let height t = Tomatch.height t.tomatch

    type ('env, 'item) inferred =
      | Unknown : ('env, TomatchType.none) inferred
      | Known :
          ('env, 'ind, 'params, 'nrealargs, 'nrealdecls) InductiveType.t ->
            ('env, 'ind TomatchType.some) inferred

    type 'env infer_type =
        Inferred :
          ('env, 'ind) inferred *
          (('env, 'ind) TypedPattern.exists, EqnLength.t) Vector.t ->
            'env infer_type

    let rec check :
      type env ind params nrealargs nrealdecls pat_length accu_length .
          env Env.t ->
          (pat_length, accu_length, EqnLength.t) Nat.plus ->
          (env, ind, params, nrealargs, nrealdecls) InductiveType.t ->
          ((env, ind, nrealargs) ConstructorSummary.exists, ind) Tuple.t ->
          (Pattern.exists, pat_length) Vector.t ->
          ((env, ind TomatchType.some) TypedPattern.exists, accu_length)
              Vector.t ->
          env infer_type = fun env plus ind_type cstrs pats accu ->
      match pats, plus with
      | [], Zero_l ->
          Inferred (
            Known ind_type, Vector.map_rev_append Fun.id accu []
              (Nat.plus_commut (Vector.length accu) plus))
      | Exists hd :: tl, Succ_plus plus ->
          let pat = TypedPattern.check env cstrs ind_type hd in
          check env (Nat.plus_succ plus) ind_type cstrs tl (pat :: accu)

    let rec infer : type pat_length var_length .
          'env Env.t -> 'env EJudgment.t ->
          (pat_length, var_length, EqnLength.t) Nat.plus ->
          (Pattern.exists, pat_length) Vector.t ->
          (Names.Name.t CAst.t, var_length) Vector.t ->
          ('env EJudgment.t * 'env infer_type) EvarMapMonad.t =
    fun env judgment plus pats vars ->
      let open EvarMapMonad.Ops in
      match pats, plus with
      | [], Zero_l ->
          return (judgment, Inferred (
            Unknown,
            Vector.map_rev_append TypedPattern.of_var vars []
              (Nat.plus_commut (Vector.length vars) plus)))
      | Exists hd :: tl, Succ_plus plus  ->
          match hd.v.desc with
          | Var ->
              infer env judgment (Nat.plus_succ plus) tl
                (CAst.make ?loc:hd.loc hd.v.name :: vars)
          | Cstr { cstr = Exists cstr; args } ->
              let ind = Constructor.inductive cstr in
              let vars_pat =
                Vector.map_rev_append TypedPattern.of_var vars []
                  (Nat.zero_r (Vector.length vars)) in
              let* ind_term, Exists ind_type =
                InductiveType.make_with_evars env ind in
              let* () =
                  fun sigma ->
                  try (
                    Evarconv.unify_leq_delay (Eq.cast Env.eq env) sigma
                      (Eq.cast ETerm.eq ind_term)
                      (Eq.cast ETerm.eq (EJudgment.uj_type judgment)), ())
                  with Evarconv.UnableToUnify _ ->
                    (sigma, ()) in
              let specif = InductiveSpecif.lookup env ind in
              let cstrs =
                ConstructorSummary.get_tuple env ind_type.family specif in
              let args =
                Vector.to_list (Pattern.args_to_concrete args) in
              let pat =
                TypedPattern.unsafe_of_cstr ?loc:hd.loc env cstrs cstr args
                  hd.v.name in
              return (judgment, check env (Nat.plus_succ plus) ind_type cstrs tl
                (pat :: vars_pat))

    let infer_type  (type env) (env : env Env.t)
        (judgment : env EJudgment.t)
        (pats : (Pattern.exists, EqnLength.t) Vector.t) :
        (env EJudgment.t * env infer_type) EvarMapMonad.t =
      let open EvarMapMonad.Ops in
      let* sigma = EvarMapMonad.get in
      match
        InductiveType.of_term_opt_whd_all env sigma (EJudgment.uj_type judgment)
      with
      | None ->
          infer env judgment (Nat.zero_r (Vector.length pats)) pats []
      | Some (Exists ind_type) ->
          let ind, _ = ind_type.family.def in
          let specif = InductiveSpecif.lookup env ind in
          let cstrs =
            ConstructorSummary.get_tuple env ind_type.family specif in
          return (judgment,
            check env (Nat.zero_r (Vector.length pats)) ind_type cstrs pats [])

    let make (type env) ~small_inversion (env : env Env.t)
        (judgment : env EJudgment.t)
        (predicate_pattern : Glob_term.predicate_pattern)
        (pats : (Pattern.exists, EqnLength.t) Vector.t) :
        env exists EvarMapMonad.t =
      let open EvarMapMonad.Ops in
      let* judgment, Inferred (inferred, pats) =
        infer_type env judgment pats in
      match inferred with
      | Unknown ->
          let as_name =
            match predicate_pattern with
            | as_name, None -> as_name
            | _, Some { loc; _ } ->
                CErrors.user_err ?loc (Pp.str
              "Unexpected type annotation for a term of non inductive type.") in
          return (Exists {
            tomatch = Tomatch.make_not_inductive judgment as_name;
            pats;
          })
      | Known inductive_type ->
          begin
            match predicate_pattern with
            | _, None -> ()
            | _, Some { loc; v = (ind, _) } ->
                if InductiveDef.equal (fst inductive_type.family.def)
                  (Eq.(cast (sym (InductiveDef.eq))) ind) = None then
                  CErrors.user_err ?loc (Pp.str "Wrong inductive type.");
          end;
          let* sigma = EvarMapMonad.get in
          let tomatch =
            Tomatch.make_inductive ~small_inversion env sigma judgment
              inductive_type predicate_pattern in
          return (Exists { tomatch; pats })
  end

  module TomatchWithContextVector = struct
    include IndSizeVector (TomatchWithContext)

    let to_tomatch_vector v =
      let module Map = AnnotatedVector.Map (A) (TomatchVector.A) in
      v |> Map.map { f = fun (type a t) (I t : (_, a, t) A.t) :
        (_, a, t) TomatchVector.A.t -> I (t.tomatch) }

    let rec proj_pats : type env length ind height end_ind end_height end_size .
        EqnLength.t Fin.t ->
          (env, length, <ind: ind; size: height>,
            <ind: end_ind; size: end_height>) section ->
              (env, length, ind, end_ind, end_size) Patterns.exists_section =
    fun index v ->
      match v with
      | [] -> Exists []
      | I hd :: tl ->
          let Exists tl = proj_pats index tl in
          let Exists hd = Vector.Ops.(hd.pats.%(index)) in
          let Exists plus = Nat.to_plus (TypedPattern.size hd) in
          Exists (I (hd, plus) :: tl)

    let to_clause (type env length) (env : env GlobalEnv.t)
        (v : (env, 'length, <ind: 'ind; size: 'height>) t)
        (index : EqnLength.t Fin.t)
        (Exists { v = { ids; rhs; _ }; loc } :
          (env, length) Clause.untyped) :
        (env, 'length, 'ind) Clause.t =
      let Exists pats = proj_pats index v in
      let length = Patterns.size pats in
      let rhs : (env, _) Rhs.t =
        Exists { matches = []; cont = { length; sum = Zero_l;
          f = { f = fun { globenv; return_pred; _ } ->
            rhs.f { globenv; return_pred }}}} in
      Exists (CAst.make ?loc ({ env; ids; pats; rhs } : _ Clause.desc))

    let to_clauses (type env length) (env : env GlobalEnv.t)
        (clauses : ((env, length) Clause.untyped,
          EqnLength.t) Vector.t)
        (v : (env, length, <ind: 'ind; size: 'height>) t) :
        ((env, length, 'ind) Clause.t, EqnLength.t)
          Vector.t =
      Vector.mapi (fun index clause -> to_clause env v index clause) clauses

    type ('env, 'length, 'end_annot) exists =
        Exists :
          ('env, 'length, <ind: 'ind; size: 'height>, 'end_annot) section ->
          ('env, 'length, 'end_annot) exists [@@ocaml.unboxed]

    let rec of_vector : type env tomatch_length end_ind end_height .
          (env TomatchWithContext.exists, tomatch_length) Vector.t ->
            (env, tomatch_length, <ind: end_ind; size: end_height>) exists =
    fun l ->
      match l with
      | [] -> Exists []
      | Exists hd :: tl ->
          let Exists tl = of_vector tl in
          Exists (I hd :: tl)
  end
end

module Suspended = struct
  type 'env term = {
      f : 'env' . ('env, 'env') Lift.t -> 'env' ETerm.t;
    }

  let of_term term =
    { f = fun lift -> ETerm.exliftn lift term }

  let lift l term =
    { f = fun lift -> term.f (Lift.comp lift l)}

  type ('env, 'length, 'length_end) section =
    | [] : ('env, 'length, 'length) section
    | ( :: ) :
        'env term *
        ('env, 'length, 'length_end) section ->
        ('env, 'length Nat.succ, 'length_end) section
    | Vector of ('env term, 'length, 'length_end) Vector.section
    | Lift : {
        lift : ('env, 'env') Lift.t;
        v : ('env, 'length, 'length_end) section;
      } -> ('env', 'length, 'length_end) section
    | Append_section : {
        v : ('env, 'l0, 'l1) section;
        v' : ('env, 'l1, 'l2) section;
      } -> ('env, 'l0, 'l2) section
(*
    | Append : {
        v : ('env, 'arity) vector;
        v' : ('env, 'arity') vector;
        plus : ('arity, 'arity', 'arity'') Nat.plus;
      } -> ('env, 'arity'', Nat.zero) section *)
  and ('env, 'length) vector = ('env, 'length, Nat.zero) section

  let of_vector vector =
    Vector (Vector.map of_term vector)

  let rec to_vector : type a b length length_end .
        (a, length, length_end) section -> (a, b) Lift.t ->
          (b ETerm.t, length, length_end) Vector.section =
  fun v l ->
    match v with
    | [] -> []
    | hd :: tl -> hd.f l :: to_vector tl l
    | Vector v -> Vector.map (fun term -> term.f l) v
    | Lift { lift; v } ->
        to_vector v (Lift.comp l lift)
    | Append_section { v; v' } ->
        Vector.append_section (to_vector v l) (to_vector v' l)
(*
    | Append { v; v'; plus } ->
        Vector.append_plus (to_vector v l) (to_vector v' l) plus
*)
end

type ('env, 'size, 'size_tail, 'patterns, 'length, 'apply)
      abstract_refine_pattern_exist = {
    tomatches : ('env EJudgment.t, 'length) Vector.t;
    length : 'length Height.t;
    patterns : ('length, 'patterns, Nat.zero) Pattern.args;
    patterns_height : 'patterns Height.t;
    apply : 'apply;
  }

type ('env, 'size, 'size_tail, 'patterns, 'length) refine_pattern_exist =
    ('env, 'size, 'size_tail, 'patterns, 'length,
     (('env * 'patterns) ETerm.t, 'size, 'size_tail) Vector.section)
      abstract_refine_pattern_exist

type ('env, 'size, 'size_tail, 'patterns, 'length) refine_pattern_exist_rec =
    ('env, 'size, 'size_tail, 'patterns, 'length,
     ('env * 'patterns, 'size, 'size_tail) Suspended.section)
      abstract_refine_pattern_exist

type ('env, 'size, 'size_tail) refine_pattern = Exists : {
    result :
      ('env, 'size, 'size_tail, 'patterns, 'length) refine_pattern_exist_rec;
    term : ('env * 'patterns) Suspended.term;
    local : ('env * 'length) Suspended.term;
  } -> ('env, 'size, 'size_tail) refine_pattern

type ('env, 'size, 'size_tail, 'arity) refine_patterns_rec = Exists : {
    result :
      ('env, 'size, 'size_tail, 'patterns, 'length) refine_pattern_exist_rec;
    terms : ('env * 'patterns, 'arity) Suspended.vector;
    locals : ('env * 'length, 'arity) Suspended.vector;
  } -> ('env, 'size, 'size_tail, 'arity) refine_patterns_rec

type ('env, 'size, 'size_tail, 'arity) refine_patterns = Exists : {
    result : ('env, 'size, 'size_tail, 'patterns, 'length) refine_pattern_exist;
    terms : (('env * 'patterns) ETerm.t, 'arity) Vector.t;
    locals : (('env * 'length) ETerm.t, 'arity) Vector.t;
  } -> ('env, 'size, 'size_tail, 'arity) refine_patterns

let rec refine_pattern : type env size size_tail .
    env Env.t -> Evd.evar_map ->
    (size, size_tail) Pattern.section ->
    env ETerm.t ->
    (env, size, size_tail) refine_pattern option =
fun env sigma pattern term ->
  let open Monad.Option.Ops in
  match pattern.v.desc with
  | Var ->
      let local = Eq.(cast (ETerm.morphism (sym Env.zero_r))) term in
      let term = Eq.(cast (ETerm.morphism (sym Env.zero_r))) term in
      let result = { tomatches = []; length = Height.zero; patterns = [];
        patterns_height = Height.zero; apply = Suspended.of_vector [term] } in
      Some (Exists { result; term = Suspended.of_term term;
        local = Suspended.of_term local })
  | Cstr { cstr = Exists cstr; args } ->
      let term' = ETerm.whd_all env sigma term in
      let construct, terms = ETerm.decompose_app sigma term' in
      match ETerm.destConstruct sigma construct with
      | None ->
          let Exists pattern = Pattern.replace pattern in
          let apply, self = Pattern.to_rel_vector O pattern.section in
          let Exists apply = Vector.replace apply in
          let Refl = Nat.zero_r_eq pattern.diff_b in
          let Refl = Nat.zero_r_eq apply.diff_a in
          let Refl = Nat.plus_fun pattern.diff_a apply.diff_b in
          let result = {
            tomatches = [EJudgment.of_term env sigma term];
            length = Height.one;
            patterns = [pattern.section];
            patterns_height =
              Height.of_nat (Pattern.size pattern.section Nat.O);
            apply =
              Suspended.of_vector (Vector.map ETerm.mkRel apply.section) } in
          let term = Suspended.of_term (ETerm.mkRel self) in
          let local =
            Suspended.of_term (ETerm.mkRel
              (Eq.(cast (Rel.morphism (Env.plus_succ ()))) (Rel.zero ()))) in
          Some (Exists { result; term; local })
      | Some (Exists cstr', instance) ->
          if Constructor.equal cstr cstr' then
            let params, terms =
              Util.List.chop (nb_params_of_constructor env cstr) terms in
            let terms =
              Option.get (Vector.of_list_of_length terms
                (Pattern.length args)) in
            let* Exists { result; terms; locals } =
              refine_patterns_rec env sigma args terms in
            let params = Array.of_list params in
            let self =
              { Suspended.f = fun l ->
                let terms = Suspended.to_vector terms l in
                ETerm.mkApp (ETerm.mkConstructU cstr' instance)
                  (Array.append
                    (Array.map (ETerm.exliftn
                      Lift.(comp l (+ result.patterns_height))) params)
                    (Vector.to_array terms))} in
            let local =
              { Suspended.f = fun l ->
                let locals = Suspended.to_vector locals l in
                ETerm.mkApp (ETerm.mkConstructU cstr' instance)
                  (Array.append
                    (Array.map (ETerm.exliftn
                      Lift.(comp l (+ result.length))) params)
                    (Vector.to_array locals))} in
            let apply =
              Suspended.Append_section
                { v = result.apply; v' = [self]} in
            Some (Exists { result = { result with apply }; term = self;
              local }
              : _ refine_pattern)
          else
            None
and refine_patterns_rec : type env arity size size_tail .
    env Env.t -> Evd.evar_map ->
    (arity, size, size_tail) Pattern.args ->
    (env ETerm.t, arity) Vector.t ->
    (env, size, size_tail, arity) refine_patterns_rec option =
fun env sigma args terms ->
  let open Monad.Option.Ops in
  match args, terms with
   | [], [] ->
       let result = {
         tomatches = []; length = Height.zero; patterns = [];
         patterns_height = Height.zero; apply = Suspended.[] } in
       Some (Exists { result; terms = []; locals = [] })
   | arg :: args, term :: terms ->
       let* Exists { result = tail; terms = tail_terms; locals } =
         refine_patterns_rec env sigma args terms in
       let* Exists { result = head; term = head_term; local } =
         refine_pattern env sigma arg term in
       let Exists { vector = tomatches; plus } =
         Vector.Ops.(head.tomatches @ tail.tomatches) in
       let head_size = Pattern.size_of_args head.patterns O in
       let Exists height_plus = Nat.to_plus head_size in
       let head_apply =
         Suspended.Lift {
           lift = Lift.(+ tail.patterns_height); v = head.apply; } in
       let tail_apply =
         Suspended.Lift {
           lift = Lift.(liftn tail.patterns_height (+ head.patterns_height));
           v = tail.apply; } in
       let apply =
         Suspended.Lift {
           lift = Lift.of_eq Eq.(Env.assoc ++ Env.morphism Refl
             (Env.plus height_plus));
           v = Suspended.Append_section { v = head_apply; v' = tail_apply }} in
       let Exists head_patterns = Pattern.replace_args head.patterns in
       let Refl = Nat.zero_r_eq head_patterns.diff_a in
       let Refl = Nat.plus_fun head_patterns.diff_b height_plus in
       let patterns =
         Pattern.append_plus head_patterns.args tail.patterns plus in
       let length = Height.Ops.(head.length + tail.length) |>
         Eq.cast (Height.morphism (Env.plus plus)) in
       let patterns_height =
         Height.Ops.(head.patterns_height + tail.patterns_height) |>
         Eq.cast (Height.morphism (Env.plus height_plus)) in
       let result = { tomatches; length; patterns; patterns_height; apply } in
       let head_term = Suspended.lift Lift.(+ tail.patterns_height) head_term in
       let tail_terms =
         Suspended.Lift {
           lift = Lift.(liftn tail.patterns_height (+ head.patterns_height));
           v = tail_terms;
       } in
       let terms = Suspended.Lift {
         lift = Lift.of_eq
           Eq.(Env.assoc ++ Env.morphism Refl (Env.plus height_plus));
         v = head_term :: tail_terms; } in
       let length_hd = Height.of_nat (Vector.length head.tomatches) in
       let length_tail = Height.of_nat (Vector.length tail.tomatches) in
       let local =
         Suspended.lift Lift.(+ length_tail) local in
       let locals =
         Suspended.Lift {
           lift = Lift.(liftn length_tail (+ length_hd));
           v = locals; } in
       let locals = Suspended.Lift {
         lift = Lift.of_eq Eq.(Env.assoc ++ Env.morphism Refl (Env.plus plus));
         v = local :: locals } in
       Some ((Exists { result; terms; locals } : _ refine_patterns_rec))

let refine_patterns env sigma args terms =
  let open Monad.Option.Ops in
  let* Exists { result; terms; locals } =
    refine_patterns_rec env sigma args terms in
  let result = { result with
    apply = Vector.rev (Suspended.to_vector result.apply (Lift.id ()));
  } in
  let terms = Suspended.to_vector terms (Lift.id ()) in
  let locals = Suspended.to_vector locals (Lift.id ()) in
  return (Exists { result; terms; locals })

type ('env, 'binders, 'level, 'sum_binders) generalize_context_desc = {
    level : 'level Nat.t;
    binders_height : 'binders Height.t;
    level_height : 'level Height.t;
    height : 'sum_binders Height.t;
    sum_binders : ('level, 'binders, 'sum_binders) Nat.plus;
    binders : ('env ETerm.t, 'sum_binders) Vector.t;
    context : 'env Env.t -> ('env * 'binders, 'level, 'level) ERelContext.t;
    apply : ('env ETerm.t, 'level) Vector.t;
  }

type ('env, 'binders, 'level) generalize_context = Exists :
  ('env, 'binders, 'level, 'sum_binders) generalize_context_desc ->
    ('env, 'binders, 'level) generalize_context [@@ocaml.unboxed]

let generalize_context_of_binders env sigma binders =
  let height = Height.of_nat (Vector.length binders) in
  Exists {
    sum_binders = Nat.Zero_l; level = Nat.O; level_height = Height.zero;
    binders_height = height; height;
    binders; context = (fun _ -> []); apply = []; }

type ('env, 'binders, 'level, 'sum_binders, 'new_level, 'new_binders, 'diff)
      generalize_context_accu = {
    level : ('diff, 'level, 'new_level) Nat.plus;
    binders : ('diff, 'sum_binders, 'new_binders) Nat.plus;
    context : ('env, 'binders, 'new_level, 'new_binders)
      generalize_context_desc;
  }

let accu_zero context =
  { level = Nat.Zero_l; binders = Nat.Zero_l; context }

type ('env, 'binders, 'level, 'sum_binders) generalize_judgment = {
    accu : ('env, 'binders, 'level, 'sum_binders, 'level Nat.succ,
      'sum_binders Nat.succ, Nat.one) generalize_context_accu;
    result : ('env * 'sum_binders Nat.succ) EJudgment.t;
  }

let generalize_judgment (type env binders level sum_binders) env sigma namer
    (judgment : env EJudgment.t)
    (context : (env, binders, level, sum_binders) generalize_context_desc) =
  let { sum_binders; level; level_height; binders_height; height; binders;
    context; apply } = context in
  let ty, modified =
    subst_binders env sigma binders_height sum_binders binders
      (EJudgment.uj_type judgment) in
  if modified then
    let height = Height.succ height in
    let level_height = Height.succ level_height in
    let value = EJudgment.uj_val judgment in
    let ty' = ty |> Eq.(cast (ETerm.morphism (
      Env.morphism Refl (sym (Env.rev_plus sum_binders)) ++
      sym Env.assoc))) in
    let context = {
      sum_binders = Nat.Succ_plus sum_binders; level = S level; height;
      binders_height; level_height;
      binders = value :: binders; apply = value :: apply;
      context = fun env ->
        EDeclaration.assum (namer env) ty' :: context env } in
    let ty = ETerm.lift Height.one ty |> Eq.(cast (ETerm.morphism
      (Env.assoc ++ Env.morphism Refl Env.succ))) in
    let rel = Eq.(cast (Rel.morphism (Env.plus_succ ())) (Rel.zero ())) in
    let accu = { context;
      level = Nat.Succ_plus Nat.Zero_l;
      binders = Nat.Succ_plus Nat.Zero_l } in
    Some ({ accu; result = EJudgment.make (ETerm.mkRel rel) ty })
  else
    None

type ('env, 'binders, 'level, 'sum_binders, 'new_level, 'new_sum_binders,
        'diff) generalize_term_desc = {
    accu :
      ('env, 'binders, 'level, 'sum_binders, 'new_level, 'new_sum_binders,
        'diff) generalize_context_accu;
    result : ('env * 'new_sum_binders) ETerm.t;
  }

type ('env, 'binders, 'level, 'sum_binders) generalize_term = Exists :
      ('env, 'binders, 'level, 'sum_binders, 'new_level, 'new_sum_binders,
        'diff) generalize_term_desc ->
          ('env, 'binders, 'level, 'sum_binders) generalize_term
            [@@ocaml.unboxed]

type ('env, 'binders, 'level, 'sum_binders, 'length) generalize_terms =
    Exists : {
    accu :
      ('env, 'binders, 'level, 'sum_binders, 'new_level, 'new_sum_binders,
        'diff) generalize_context_accu;
    result : (('env * 'new_sum_binders) ETerm.t, 'length) Vector.t;
  } -> ('env, 'binders, 'level, 'sum_binders, 'length) generalize_terms

type ('env, 'binders, 'level0, 'sum_binders0, 'level2, 'sum_binders2)
      union_accu = Exists :
      ('env, 'binders, 'level0, 'sum_binders0, 'level2, 'sum_binders2,
        'diff) generalize_term_desc ->
          ('env, 'binders, 'level0, 'sum_binders0, 'level2, 'sum_binders2)
            union_accu [@@ocaml.unboxed]

let union_accu
    (desc : ('env, 'binders, 'level0, 'sum_binders0, 'level1, 'sum_binders1,
      'diff0) generalize_term_desc)
    (accu : ('env, 'binders, 'level1, 'sum_binders1, 'level2, 'sum_binders2,
      'diff1) generalize_context_accu) :
    ('env, 'binders, 'level0, 'sum_binders0, 'level2, 'sum_binders2)
    union_accu =
  let Exists diff = Nat.plus_shift accu.level in
  Exists { accu =
    { level = Nat.plus_assoc_rec desc.accu.level accu.level diff;
      binders = Nat.plus_assoc_rec desc.accu.binders accu.binders diff;
      context = accu.context };
    result = desc.result |>
    Eq.(cast (ETerm.morphism (
      Env.morphism Refl (sym (Env.rev_plus desc.accu.context.sum_binders)) ++
      sym Env.assoc))) |>
    ETerm.lift (Height.of_nat (Nat.plus_l accu.level)) |>
    Eq.(cast (ETerm.morphism (
      Env.assoc ++
      Env.morphism Refl (Env.rev_plus accu.level) ++
      Env.assoc ++
      Env.morphism Refl (Env.rev_plus accu.context.sum_binders)))) }

let rec generalize_term : type env binders level sum_binders .
    allow_new_binders:bool ->
    env Env.t ->
    Evd.evar_map -> env ETerm.t ->
    (env, binders, level, sum_binders) generalize_context_desc ->
    (env, binders, level, sum_binders) generalize_term =
fun ~allow_new_binders env sigma term context ->
  let term' = ETerm.whd_all env sigma term in
  let f, args = ETerm.decompose_app sigma term' in
  match ETerm.destConstruct sigma f with
  | Some (Exists cstr, instance) ->
      let Exists args = Vector.of_list args in
      let Exists { accu; result = args } =
        generalize_terms ~allow_new_binders env sigma args context in
      let result = ETerm.mkConstructU cstr instance in
      Exists { accu; result = ETerm.mkApp result (Vector.to_array args) }
  | None ->
      match
        context.binders |> Vector.findi (fun i (t' : env ETerm.t) ->
          if ETerm.equal sigma term' t' then
            Some i
          else
            None)
      with
      | Some i ->
          let result = ETerm.mkRel (Rel.of_fin i) in
          Exists { accu = accu_zero context; result }
      | None ->
          let j = EJudgment.of_term env sigma term' in
          match
            if allow_new_binders then
              generalize_judgment env sigma (fun _ -> Context.anonR) j context
            else
              None
          with
          | None ->
              Exists {
                accu = accu_zero context;
                result = ETerm.lift context.height term }
          | Some { accu; result } ->
              Exists { accu; result = EJudgment.uj_val result }
and generalize_terms : type env binders level sum_binders length .
    allow_new_binders:bool ->
    env Env.t ->
    Evd.evar_map -> (env ETerm.t, length) Vector.t ->
    (env, binders, level, sum_binders) generalize_context_desc ->
    (env, binders, level, sum_binders, length) generalize_terms =
fun ~allow_new_binders env sigma terms context ->
    match terms with
    | [] -> Exists { accu = accu_zero context; result = [] }
    | hd :: tl ->
        let Exists desc =
          generalize_term ~allow_new_binders env sigma hd context in
        let Exists { accu; result = tl } =
          generalize_terms ~allow_new_binders env sigma tl desc.accu.context in
        let Exists { accu; result = hd } = union_accu desc accu in
        Exists { accu; result = hd :: tl }

type ('env, 'binders) generalize_previously_bounds =
    Exists : {
    context : ('env, 'binders, 'level, 'sum_binders) generalize_context_desc;
    old_previously_bounds : ('env Rel.t, 'old_previously_bounds) Vector.t;
    new_previously_bounds : ('level Fin.t, 'new_previously_bounds) Vector.t;
  }->
    ('env, 'binders) generalize_previously_bounds

let rec generalize_previously_bounds :
type env previously_bounds binders level .
    env Env.t -> Evd.evar_map -> (env Rel.t, previously_bounds) Vector.t ->
    (env, binders, level) generalize_context ->
    (env, binders) generalize_previously_bounds =
fun env sigma previously_bounds context ->
  match previously_bounds with
  | [] ->
      let Exists context = context in
      Exists { context; old_previously_bounds = previously_bounds;
        new_previously_bounds = [] }
  | hd :: tl ->
      let Exists { context; old_previously_bounds; new_previously_bounds } =
        generalize_previously_bounds env sigma tl context in
      let Exists h = Rel.to_height hd in
      let get_decl env =
        Declaration.lookup (Eq.(cast (sym h.eq)) env) h.height in
      let Exists decl = get_decl env in
      let ty =
        Eq.cast (ETerm.morphism h.eq)
          (ETerm.lift h.height (ETerm.of_term decl.ty)) in
      let namer env =
        let Exists decl = get_decl env in
        decl.name in
      match
        generalize_judgment env sigma namer (EJudgment.make (ETerm.mkRel hd) ty)
          context
      with
      | None ->
          Exists { context; old_previously_bounds = hd :: old_previously_bounds;
            new_previously_bounds }
      | Some { accu; _ } ->
          let new_previously_bounds =
            Vector.map Fin.succ new_previously_bounds in
          Exists { context = accu.context; old_previously_bounds;
            new_previously_bounds = Fin.zero :: new_previously_bounds }

type ('env, 'binders, 'length, 'level, 'sum_binders) generalize_judgments =
    Exists : {
    accu :
      ('env, 'binders, 'level, 'sum_binders, 'new_level, 'new_sum_binders,
        'diff) generalize_context_accu;
    result :
      (('env * 'new_sum_binders) EJudgment.t, 'length) Vector.t;
  }->
    ('env, 'binders, 'length, 'level, 'sum_binders) generalize_judgments

let rec generalize_judgments_rec :
type env length binders level sum_binders .
      env Env.t -> Evd.evar_map ->
        (env EJudgment.t, length) Vector.t ->
          (env, binders, level, sum_binders) generalize_context_desc ->
            (env, binders, length, level, sum_binders) generalize_judgments =
fun env sigma judgments context ->
  match judgments with
  | [] ->
      Exists { accu = accu_zero context; result = [] }
  | hd :: tl ->
      let Exists desc =
        generalize_term ~allow_new_binders:true env sigma (EJudgment.uj_val hd)
          context in
      let Exists { accu; result = tl } =
        generalize_judgments_rec env sigma tl desc.accu.context in
      let Exists { accu; result = v } = union_accu desc accu in
      let ty, _ =
        subst_binders env sigma accu.context.binders_height
          accu.context.sum_binders accu.context.binders
          (EJudgment.uj_type hd) in
      Exists { accu; result = EJudgment.make v ty :: tl }

let generalize_judgments env sigma judgments context =
  let Exists { accu; result } =
    generalize_judgments_rec env sigma (Vector.rev judgments) context in
  Exists { accu; result = Vector.rev result }

let naming_of_program_mode (program_mode : bool) : Evarutil.naming_mode =
  let vars = Evarutil.VarSet.variables (Global.env ()) in
  if program_mode then ProgramNaming vars
  else RenameExistingBut vars

module TomatchTuple = struct
  type 'env t = {
      judgment : 'env EJudgment.t;
      predicate_pattern : Glob_term.predicate_pattern;
    }

  let of_judgment (judgment : 'env EJudgment.t) : 'env t =
    { judgment; predicate_pattern = (Anonymous, None) }

  let make_pair (pattern : Pattern.exists) (judgment : 'env EJudgment.t) =
    (of_judgment judgment, Vector.[pattern; Pattern.ex_var Anonymous])
end

type 'env return_pred = {
    f : 'length 'nb_args . ('env, 'length, 'nb_args) ERelContext.t ->
      ('env * 'length) ETerm.t EvarMapMonad.t;
  }

module type CompilerS = sig
  val compile_cases : generalize_return_pred:bool ->
      'env GlobalEnv.t -> 'env return_pred ->
      ('env TomatchTuple.t, 'tomatch_count) Vector.t ->
      (('env, 'tomatch_count) Clause.untyped,
        'eqns_length) Vector.t ->
      'env EJudgment.t EvarMapMonad.t

  val compile_loop :
      ('env, 'tomatch_length, 'tomatch_ind, 'eqns_length, 'return_pred_height,
        'previously_bounds)
        PatternMatchingProblem.t -> 'env EJudgment.t EvarMapMonad.t
end

module type CompileCaseS = sig
  val expand_self : bool

  type env

  type ind

  type nrealargs

  type nrealdecls

  val env : env GlobalEnv.t

  val tomatch : (env, ind TomatchType.some, nrealdecls Nat.succ) Tomatch.t
end

(*
let rec pp_pattern (pattern : Glob_term.cases_pattern) =
  match DAst.get pattern with
  | PatVar name -> Names.Name.print name
  | PatCstr (cstr, args, _) ->
      Pp.(
        int (snd cstr) ++ str "(" ++
        prlist_with_sep pr_comma pp_pattern args ++ str ")")
*)

let rec destruct_n_prod sigma n term =
  if n = 0 then
    term
  else
    let (_binder, _type, term') = EConstr.destProd sigma term in
    destruct_n_prod sigma (pred n) term'

let rec check_if_argument_is_used_in_type sigma n used (term : EConstr.t) =
  match EConstr.destLambda sigma term with
  | (_binder, _ty, term) ->
      check_if_argument_is_used_in_type sigma n used term
  | exception Constr.DestKO ->
      match EConstr.destCase sigma term with
      | (case_info, univ, params, (names, p), iv, tomatch, branches) ->
          Array.iter (fun (_names, branch) ->
              check_if_argument_is_used_in_type sigma n used branch
            ) branches
      | exception Constr.DestKO ->
          match EConstr.destApp sigma term with
          | (term, _args) ->
              check_if_argument_is_used_in_type sigma n used term
          | exception Constr.DestKO ->
              match destruct_n_prod sigma n term with
              | exception Constr.DestKO -> ()
              | term ->
                  for i = 0 to n - 1 do
                    if not (EConstr.Vars.noccurn sigma (n - i) term) then
                      used.(i) <- true
                  done

let rec destruct_n_lambda sigma n term =
  if n = 0 then
    term
  else
    let (_binder, _type, term') = EConstr.destLambda sigma term in
    destruct_n_lambda sigma (pred n) term'

let rec check_if_argument_is_used sigma n m used (term : EConstr.t) =
  match EConstr.destLambda sigma term with
  | (_binder, _type, term) ->
      if m > 0 then
        check_if_argument_is_used sigma n (m - 1) used term
      else
        begin
          let term = destruct_n_lambda sigma (n - 1) term in
          for i = 0 to n - 1 do
            if not (EConstr.Vars.noccurn sigma (n - i) term) then
              used.(i) <- true
          done
        end
  | exception Constr.DestKO ->
      match EConstr.destCase sigma term with
      | (case_info, _univ, _params, (_names, p), _iv, _tomatch, branches) ->
          check_if_argument_is_used_in_type sigma n used p;
          Array.iter (fun (_, branch) ->
              check_if_argument_is_used sigma n m used branch
            ) branches
      | exception Constr.DestKO ->
          match EConstr.destApp sigma term with
          | (term, args) ->
              check_if_argument_is_used sigma n (m + Array.length args) used
                term
          | exception Constr.DestKO -> ()

let rec destruct_n_prod_binders_rec accu sigma n term =
  if n = 0 then
    List.rev accu
  else
    let (_binder, ty, term') = EConstr.destProd sigma term in
    destruct_n_prod_binders_rec (ty :: accu) sigma (pred n) term'

let destruct_n_prod_binders sigma n term =
  destruct_n_prod_binders_rec [] sigma n term

let rec check_if_argument_is_deps_in_return_pred env sigma n (deps : bool list) used (term : EConstr.t) =
  match EConstr.destLambda sigma term with
  | (_binder, _ty, term) ->
      check_if_argument_is_deps_in_return_pred env sigma n (true :: deps) used term
  | exception Constr.DestKO ->
      match EConstr.destCase sigma term with
      | (case_info, univ, params, (names, p), iv, tomatch, branches) ->
          let _, specif = Inductive.lookup_mind_specif env case_info.ci_ind in
          let is_tomatch_in_deps =
            CList.exists_i (fun i dep ->
              if dep then
                not (EConstr.Vars.noccurn sigma (i + 1) term)
              else
                false) 0 deps in
          Array.iter2 (fun (_names, branch) nrealdecls ->
              let new_deps =
                List.init nrealdecls (fun _ -> is_tomatch_in_deps) in
              let deps = new_deps @ deps in
              check_if_argument_is_deps_in_return_pred env sigma n deps used branch
            ) branches specif.mind_consnrealdecls
      | exception Constr.DestKO ->
          match EConstr.destApp sigma term with
          | (term, _args) ->
              check_if_argument_is_deps_in_return_pred env sigma n deps used term
          | exception Constr.DestKO ->
              match destruct_n_prod_binders sigma n term with
              | exception Constr.DestKO -> ()
              | types ->
                  ignore (List.fold_left (fun (deps, i) ty ->
                    if not (CList.exists_i (fun i dep ->
                      if dep then
                        not (EConstr.Vars.noccurn sigma (i + 1) ty)
                      else
                        false) 0 deps) then
                      begin
                        used.(i) <- false;
                        (false :: deps, succ i)
                      end
                    else
                      (true :: deps, succ i)) (deps, 0) types)

let check_if_argument_is_deps env sigma n used (term : EConstr.t) =
  match EConstr.destCase sigma term with
  | (case_info, _univ, _params, (names, p), _iv, _tomatch, branches) ->
      check_if_argument_is_deps_in_return_pred env sigma n
        (List.init (Array.length names) (fun _ -> true)) used p
  | exception Constr.DestKO -> ()

let rec filter_prods sigma used apply lvl term =
  match used, apply with
  | [], [] -> term
  | hd :: tl, hd' :: tl' ->
      let (binder, ty, term) = EConstr.destProd sigma term in
      if hd then
        EConstr.mkProd (binder, ty, filter_prods sigma tl tl' (succ lvl) term)
      else
        let hd' = EConstr.Vars.lift lvl hd' in
        filter_prods sigma tl tl' lvl (EConstr.Vars.subst1 hd' term)
  | _ -> assert false

let rec strip_unused_prods env sigma n used apply lvl (term : EConstr.t) =
  match EConstr.destLambda sigma term with
  | (binder, ty, term') ->
      EConstr.mkLambda (binder, ty, strip_unused_prods env sigma n used apply (succ lvl) term')
  | exception Constr.DestKO ->
      match EConstr.destCase sigma term with
      | (case_info, univ, params, p, iv, tomatch, branches) ->
          let _, specif = Inductive.lookup_mind_specif env case_info.ci_ind in
          let branches =
            Array.map2 (fun (names, branch) nrealdecls ->
                let lvl = lvl + nrealdecls in
                (names, strip_unused_prods env sigma n used apply lvl branch)
              ) branches specif.mind_consnrealdecls in
          EConstr.mkCase (case_info, univ, params, p, iv, tomatch, branches)
      | exception Constr.DestKO ->
          match EConstr.destApp sigma term with
          | (term, args) ->
              EConstr.mkApp (strip_unused_prods env sigma n used apply lvl term, args)
          | exception Constr.DestKO ->
              try filter_prods sigma used apply lvl term
              with Constr.DestKO -> term

let rec filter_lambdas sigma used apply lvl term =
  match used, apply with
  | [], [] -> term
  | hd :: tl, hd' :: tl' ->
      let (binder, ty, term) = EConstr.destLambda sigma term in
      if hd then
        EConstr.mkLambda (binder, ty, filter_lambdas sigma tl tl' (succ lvl) term)
      else
        let hd' = EConstr.Vars.lift lvl hd' in
        filter_lambdas sigma tl tl' lvl (EConstr.Vars.subst1 hd' term)
  | _ -> assert false

let rec strip_unused_lambdas env sigma n m used apply lvl (term : EConstr.t) =
  match EConstr.destLambda sigma term with
  | (binder, ty, term') ->
      if m > 0 then
        EConstr.mkLambda (binder, ty,
          strip_unused_lambdas env sigma n (m - 1) used apply (succ lvl) term')
      else
        filter_lambdas sigma used apply lvl term
  | exception Constr.DestKO ->
      match EConstr.destCase sigma term with
      | (case_info, univ, params, (names, p), iv, tomatch, branches) ->
          let _, specif = Inductive.lookup_mind_specif env case_info.ci_ind in
          let p = strip_unused_prods env sigma n used apply (lvl + Array.length names) p in
          let branches =
            Array.map2 (fun (names, branch) nrealdecls ->
                (names, strip_unused_lambdas env sigma n m used apply (lvl + nrealdecls) branch)
              ) branches specif.mind_consnrealdecls in
          EConstr.mkCase
            (case_info, univ, params, (names, p), iv, tomatch, branches)
      | exception Constr.DestKO ->
          match EConstr.destApp sigma term with
          | (term, args) ->
              let term =
                strip_unused_lambdas env sigma n (m + (Array.length args)) used
                  apply lvl term in
              EConstr.mkApp (term, args)
          | exception Constr.DestKO -> term

let degeneralize_list (type env) (env : env Env.t) sigma (term : env ETerm.t)
      (apply : env ETerm.t list) : env ETerm.t * env ETerm.t list =
  let n = List.length apply in
  if n = 0 then
    (term, apply)
  else
    begin
      let used_array = Array.make n false in
      check_if_argument_is_used sigma n 0 used_array (Eq.cast ETerm.eq term);
      check_if_argument_is_deps (Eq.cast Env.eq env) sigma n used_array (Eq.cast ETerm.eq term);
      if Array.for_all Fun.id used_array then
        (term, apply)
      else
        begin
          let used_list = Array.to_list used_array in
          let term =
            Eq.cast (Eq.sym ETerm.eq)
              (strip_unused_lambdas (Eq.cast Env.eq env) sigma n 0 used_list
                (Eq.cast (Eq.list ETerm.eq) apply) 0 (Eq.cast ETerm.eq term)) in
          let apply =
            List.filter_map
              (fun (term, used) -> if used then Some term else None)
              (List.combine apply used_list) in
          (term, apply)
        end
    end

module type MatchContextS = sig
  val style : Constr.case_style

  val program_mode : bool

  val small_inversion : bool

  val compile_loop :
      ('env, 'tomatch_length, 'tomatch_ind, 'eqns_length, 'return_pred_height,
        'previously_bounds)
        PatternMatchingProblem.t -> 'env EJudgment.t EvarMapMonad.t
end

module Make (MatchContext : MatchContextS) : CompilerS = struct
  let push_rel sigma decl env =
    let hypnaming = naming_of_program_mode MatchContext.program_mode in
    GlobalEnv.push_rel ~hypnaming sigma decl env

  let push_local_def sigma name judgment env =
    push_rel sigma (EDeclaration.local_def (Context.annotR name) judgment) env

  let push_local_name sigma name judgment env =
    let rec is_already_named :
    type env . env ETerm.t -> env Env.t -> env Rel.t option =
    fun term env ->
      match ETerm.destRel sigma term with
      | None -> None
      | Some r ->
          let Exists { height; eq } = Rel.to_height r in
          let env = Eq.(cast (sym eq)) env in
          let Exists d = Declaration.lookup env height in
          if Context.binder_name d.name = name then
            Some r
          else
            match d.desc with
            | LocalAssum -> None
            | LocalDef term ->
                let env = Height.env height env in
                match is_already_named (ETerm.of_term term) env with
                | None -> None
                | Some r ->
                    Some (Eq.(cast (Rel.morphism eq)) (Rel.lift height r)) in
    let r, name' =
      match
        is_already_named (EJudgment.uj_val judgment) (GlobalEnv.env env)
      with
      | None -> None, name
      | Some r -> Some (Rel.lift Height.one r), Anonymous in
    r, push_local_def sigma name' judgment env

(*
  let push_rel_m decl env =
    let open EvarMapMonad.Ops in
    let* sigma = EvarMapMonad.get in
    return (push_rel sigma decl env)
*)

  let push_rel_context sigma context env =
    let hypnaming = naming_of_program_mode MatchContext.program_mode in
    GlobalEnv.push_rel_context ~hypnaming sigma context env

  let push_rel_context_m context env =
    let open EvarMapMonad.Ops in
    let* sigma = EvarMapMonad.get in
    return (push_rel_context sigma context env)

  module TypeTomatch (EqnLength : TypeS) = struct
    module PrepareTomatch = PrepareTomatch (EqnLength)

    let type_tomatch (glob_env : 'env GlobalEnv.t)
        (tomatch_with_pats :
           'env TomatchTuple.t *
           (Pattern.exists, EqnLength.t) Vector.t):
        'env PrepareTomatch.TomatchWithContext.exists EvarMapMonad.t =
      let tuple, pats = tomatch_with_pats in
      let env = GlobalEnv.env glob_env in
      PrepareTomatch.TomatchWithContext.make
        ~small_inversion:MatchContext.small_inversion
        env tuple.judgment tuple.predicate_pattern pats

    let type_tomatches
        (type tomatch_length end_ind end_height)
        (env : 'env GlobalEnv.t)
        (tomatches_with_pats :
           ('env TomatchTuple.t *
               (Pattern.exists, EqnLength.t) Vector.t,
             tomatch_length) Vector.t) :
        ('env, tomatch_length, <ind: end_ind; size: end_height>)
        PrepareTomatch.TomatchWithContextVector.exists EvarMapMonad.t =
      let open EvarMapMonad.Ops in
      let module VectorUtils = Vector.UseMonad (Monad.State) in
      let* vector =
        VectorUtils.map (type_tomatch env) tomatches_with_pats in
      return (PrepareTomatch.TomatchWithContextVector.of_vector vector)
  end

  let compile_base (type env)
      (problem :
        (env, Nat.zero, unit, _ Nat.succ, Nat.zero, _)
          PatternMatchingProblem.t) :
      env EJudgment.t EvarMapMonad.t =
    let open EvarMapMonad.Ops in
    let Exists { v = { env; pats = []; rhs = Exists rhs; _ }} :: _ =
      problem.eqns in
    let return_pred = ReturnPred.get problem.return_pred in
    let globenv = Eq.(cast (GlobalEnv.morphism (sym Env.zero_r)) env) in
    let* sigma = EvarMapMonad.get in
    let matches =
      Eq.(cast (Vector.eq (ETerm.morphism (sym Env.zero_r)))) rhs.matches in
    let Refl = Nat.zero_r_eq rhs.cont.sum in
    Format.eprintf "compile_base in env: %a@.return pred: %a@."
      Pp.pp_with (Env.print (GlobalEnv.env globenv))
      Pp.pp_with (ETerm.print (GlobalEnv.env globenv) sigma return_pred);
    let* result = rhs.cont.f.f
        { globenv; context = []; return_pred; matches } in
    let* sigma = EvarMapMonad.get in
    Format.eprintf "Base: @[%a@] (return pred: @[%a@] in env @[%a@])@."
      Pp.pp_with (EJudgment.print (GlobalEnv.env globenv) sigma result)
      Pp.pp_with (ETerm.print (GlobalEnv.env globenv) sigma
        return_pred)
      Pp.pp_with (Env.print (GlobalEnv.env globenv));
    let* (result, _trace) =
      EJudgment.inh_conv_coerce_to ~program_mode:MatchContext.program_mode
        ~resolve_tc:true (GlobalEnv.env globenv)
        result return_pred in
    let result = Eq.(cast (EJudgment.morphism Env.zero_r)) result in
    return result

  let get_tomatch_args : type env ind height .
      env Env.t -> (env, ind, height) Tomatch.t ->
        (env ETerm.t, height) Vector.t =
  fun env tomatch ->
    match tomatch.inductive_type with
    | Not_inductive _ -> [EJudgment.uj_val tomatch.judgment]
    | Inductive { inductive_type; _ } ->
        let args =
          ERelContext.subst_of_instance
            (InductiveFamily.get_arity env inductive_type.family)
            (Vector.rev inductive_type.realargs) in
        EJudgment.uj_val tomatch.judgment :: Vector.rev args

  let compile_case_trivial
      (type env ind tail_length ind_tail eqns_length return_pred_height
        tail_height previously_bounds)
      (tomatch : (env, ind, return_pred_height) Tomatch.t)
      (vars : (Names.Name.t, eqns_length) Vector.t)
      (problem :
         (env, tail_length Nat.succ, ind * ind_tail, eqns_length,
           return_pred_height * tail_height, previously_bounds)
         PatternMatchingProblem.t) :
      env EJudgment.t EvarMapMonad.t =
    let open EvarMapMonad.Ops in
    let Exists { nat; eq } = Height.to_nat tomatch.return_pred_height in
    let tail_tomatches = TomatchVector.tl problem.tomatches in
    let tail_height = TomatchVector.height tail_tomatches in
    let substl = get_tomatch_args (GlobalEnv.env problem.env) tomatch in
(*
    Format.eprintf "compile case trivial: %a@."
      Pp.pp_with (Pp.pr_enum ETerm.debug_print (Vector.to_list substl));
*)
    let return_pred =
      ReturnPred.apply (Vector.rev substl) tail_height problem.return_pred in
    let* sigma = EvarMapMonad.get in
    let self_name = Vector.find_name Fun.id vars in
    let rel0, (_declaration, env) =
      push_local_name sigma self_name tomatch.judgment problem.env in
    let tomatches = TomatchVector.lift Height.one tail_tomatches in
    let make_eqn (Exists { v; loc } :
        (env, tail_length Nat.succ, ind * ind_tail) Clause.t) :
        _ Rel.t option * (env * Nat.one, tail_length, ind_tail) Clause.t =
      let I (pat, plus) :: pats = v.pats in
      let var, Refl = Option.get (TypedPattern.get_var pat) in
      let rel1, (_, env) = push_local_name sigma var tomatch.judgment v.env in
      let pats = Patterns.lift Height.one pats in
      let Succ_plus Zero_l = plus in
      let rhs =
        Rhs.consume (ETerm.lift Height.one
          (EJudgment.uj_val tomatch.judgment) |>
          Eq.cast (ETerm.morphism Env.succ)) v.rhs tomatch.judgment |>
        Rhs.morphism (Eq.sym Env.succ) in
      rel1, Exists (CAst.make ?loc Clause.{ env; ids = v.ids; pats; rhs }) in
    let rel_eqns = Vector.map make_eqn problem.eqns in
    let rels, eqns = Vector.split rel_eqns in
    let rel =
      match Vector.find_opt Fun.id rels with
      | Some rel -> rel
      | None -> Eq.(cast (Rel.morphism (sym Env.succ))) (Rel.zero ()) in
    let return_pred = ReturnPred.lift Height.one return_pred in
    let previously_bounds : _ Vector.t =
      rel :: Vector.map (Rel.lift Height.one) problem.previously_bounds in
    let* judgment =
      MatchContext.compile_loop
        { env; tomatches; eqns; return_pred; previously_bounds;
          expand_self = problem.expand_self } in
(*
    let* sigma = EvarMapMonad.get in
    Format.eprintf "subst trivial: %a@." Pp.pp_with
      (EJudgment.print (GlobalEnv.env problem.env) sigma tomatch.judgment);
*)
    return (EJudgment.substl
      (Height.Vector.of_vector [EJudgment.uj_val tomatch.judgment])
      judgment)

  let invert_return_pred
      (type env ind params nrealargs nrealdecls ind_tail tail_length
        tail_height binders generalized_length sum_binders)
      (env : env GlobalEnv.t)
      (ind : (env, ind, params, nrealargs, nrealdecls) InductiveType.t)
      (arity : (env, nrealdecls, nrealargs) ERelContext.t)
      (tail_tomatches :
         (env, tail_length, <ind: ind_tail; size: tail_height>) TomatchVector.t)
      (patterns : (nrealargs Nat.succ, binders, Nat.zero) Pattern.args)
      (binders_height : binders Height.t)
      (generalized_context :
         (env * binders, generalized_length, generalized_length) ERelContext.t)
      (sum_binders : (generalized_length, binders, sum_binders) Nat.plus)
      (return_pred :
         ((env * sum_binders) * (nrealdecls Nat.succ * tail_height))
         ETerm.t)
      (return_pred_height : nrealdecls Nat.succ Height.t) :
      ((env * nrealdecls Nat.succ) * tail_height) ETerm.t EvarMapMonad.t =
    let open EvarMapMonad.Ops in
    let* sigma = EvarMapMonad.get in
    let ty =
      InductiveFamily.build_dependent_inductive (GlobalEnv.env env)
        ind.family in
    let subcontext =
      ERelContext.(EDeclaration.assum Context.anonR ty :: arity) in
    let subenv =
      push_rel_context sigma (ERelContext.with_height subcontext) env in
    let tail_tomatches =
      TomatchVector.lift return_pred_height tail_tomatches in
    let Exists tail_context =
      TomatchVector.make_return_pred_context tail_tomatches in
    let subenv = push_rel_context sigma (Exists tail_context.context) subenv in
    let module EqnLength = struct type t = Nat.one Nat.succ end in
    let module T = TypeTomatch (EqnLength) in
    let tail_height = TomatchVector.height tail_tomatches in
    let tomatches_vector = subcontext |>
      ERelContext.to_rel_vector |>
      Vector.map (EJudgment.lift tail_height) |>
      Vector.rev in
    let tomatches =
      Vector.mapi (
      fun i judgment ->
        TomatchTuple.of_judgment judgment,
        Vector.[
          Pattern.Ops.(patterns.%(i));
          Pattern.ex_var Anonymous])
        tomatches_vector in
    let* Exists tomatches = T.type_tomatches subenv tomatches in
    let module V = T.PrepareTomatch.TomatchWithContextVector in
    let nrealdecls = ind.family.nrealdecls in
    let binders_length = Pattern.size_of_args patterns O in
    let tomatch_length = Vector.length tomatches_vector in
    let generalized_length = ERelContext.length generalized_context in
    let sum_binders_height =
      Height.Ops.(Height.of_nat generalized_length + binders_height) |>
      Eq.(cast (Height.morphism (Env.plus sum_binders))) in
    let Exists pats_ok = V.proj_pats Fin.zero tomatches in
    let Exists pats_reject = V.proj_pats Fin.one tomatches in
    let env = subenv in
    let ids = Names.Id.Set.empty in
    let tomatches = V.to_tomatch_vector tomatches in
    let Exists return_pred_context =
      TomatchVector.make_return_pred_context tomatches in
    let* return_pred_env =
      push_rel_context_m (Exists return_pred_context.context) env in
    let* s = Evd.new_sort_variable Evd.univ_flexible in
    let make_return_pred ({ globenv; context; matches; _ } : _ Rhs.args) =
      let env = GlobalEnv.env globenv in
      let subcontext_length = ERelContext.length context in
      let* sigma = EvarMapMonad.get in
(*
      Format.eprintf "matches: %a@."
        Pp.pp_with (Pp.pr_enum (ETerm.print env sigma) (Vector.to_list matches));
      Format.eprintf "make_return_pred: %a in %a@."
        Pp.pp_with (ETerm.debug_print return_pred)
        Pp.pp_with (Env.print env);
*)
      let sum_tail = Height.Ops.(return_pred_height + tail_height) in
      let Exists sum_nat = Height.to_nat sum_tail in
      let sum = Height.of_nat sum_nat.nat in
      let vector = Vector.init sum_nat.nat (fun fin ->
        ETerm.mkReln (Rel.of_fin fin) sum_binders_height) in
      let return_pred = return_pred |>
        Eq.cast (ETerm.morphism Env.assoc) |>
        ETerm.liftn sum (Height.Ops.(sum_binders_height + sum_tail)) |>
        Eq.(cast (ETerm.morphism (sym Env.assoc ++
          Env.morphism Refl (sym sum_nat.eq)))) |>
        ETerm.substl (Height.Vector.of_vector vector) |>
        Eq.(cast (ETerm.morphism (
          Env.morphism (Env.morphism Refl sum_nat.eq ++ sym Env.assoc)
            (sym (Env.rev_plus sum_binders)) ++ sym Env.assoc))) |>
        ERelContext.it_mkProd_or_LetIn
          (ERelContext.with_height
            (ERelContext.exliftn Lift.(liftn binders_height
              (Height.succ (Height.of_nat nrealdecls) & + tail_height))
              generalized_context)) |>
        ETerm.liftn (Height.of_nat subcontext_length)
          (Height.of_nat binders_length) |>
        ETerm.substl (Height.Vector.of_vector matches) in
      let* sigma = EvarMapMonad.get in
      (*
      Format.eprintf "get_sort_of: %a@." Pp.pp_with
        (ETerm.print env sigma return_pred);
       *)
      let s' =
        ETerm.get_sort_of env sigma return_pred in
      let* () = (*
        match s' with
        | SProp | Prop | Set -> EvarMapMonad.set_eq_sort env s' s
        | Type _ -> *) EvarMapMonad.set_leq_sort env s' s in
      let* sigma = EvarMapMonad.get in
      return (EJudgment.of_term env sigma return_pred) in
    let make_unit_rhs ({ globenv; _ } : _ Rhs.args) =
      let env = GlobalEnv.env globenv in
      let* unit_judgment = EJudgment.unit_m env in
      let* sigma = EvarMapMonad.get in
      return (EJudgment.of_term env sigma (EJudgment.uj_type unit_judgment)) in
    let problem = {
      PatternMatchingProblem.env;
      tomatches;
      return_pred =
        ReturnPred.make (ETerm.mkSort s) (TomatchVector.height tomatches);
      eqns = [
        Clause.check { env; ids; pats = pats_ok;
          rhs = Rhs.make binders_length { f = make_return_pred }; };
        Clause.check { env; ids; pats = pats_reject;
          rhs = Rhs.make tomatch_length { f = make_unit_rhs }; }];
      previously_bounds = [];
      expand_self = true;
    } in
    let* judgment = MatchContext.compile_loop problem in
    return (EJudgment.uj_val judgment)

  type ('env, 'arity, 'size, 'tail_length, 'ind_tail, 'size_tail)
        prepare_pattern = {
      as_name : Names.Name.t;
      args : ('arity, 'size, 'size_tail) Pattern.args;
      tail : ('env, 'tail_length, <ind: 'ind_tail; size: 'size_tail>)
        Patterns.t;
    }

  type ('env, 'arity, 'tail_length, 'ind_tail)
        prepare_clause =
      Exists :
        ('env, ('env, 'arity, 'size, 'tail_length, 'ind_tail,
           'size_tail) prepare_pattern,
         ('env, 'size Nat.succ) Rhs.t) Clause.content ->
           ('env, 'arity, 'tail_length, 'ind_tail)
             prepare_clause [@@ocaml.unboxed]

  type ('env, 'arity, 'eqn_length, 'end_annot, 'end_height, 'match_height)
        prepare_sub_tomatches =
      Exists : {
      section :
        (('env * 'arity) * 'match_height, 'arity, <ind: 'annot; size: 'height>,
          <ind: 'end_annot; size: 'end_height>) TomatchVector.section;
      pats :
        ((('env * 'arity) * 'match_height, 'arity, 'annot, 'end_annot, Nat.zero)
          Patterns.exists_section, 'eqn_length) Vector.t;
    } -> ('env, 'arity, 'eqn_length, 'end_annot, 'end_height, 'match_height)
        prepare_sub_tomatches

  let prepare_sub_tomatches
      (type env tail_length ind_tail eqn_length arity end_annot end_height
         match_height)
      (env : ((env * arity) * match_height) GlobalEnv.t)
      (tomatches : (((env * arity) * match_height) EJudgment.t, arity) Vector.t)
      (clauses : ((env, arity, tail_length, ind_tail)
        prepare_clause, eqn_length) Vector.t) :
      (env, arity, eqn_length, end_annot, end_height, match_height)
        prepare_sub_tomatches EvarMapMonad.t =
    let open EvarMapMonad.Ops in
    let module EqnLength = struct type t = eqn_length end in
    let module T = TypeTomatch (EqnLength) in
    let tomatches =
      tomatches |> Vector.mapi (
      fun (i : arity Fin.t)
        (judgment : ((env * arity) * match_height) EJudgment.t) ->
        TomatchTuple.of_judgment judgment,
        clauses |> Vector.map (fun (Exists clause :
            (env, arity, tail_length, ind_tail)
              prepare_clause) ->
          Pattern.Ops.(clause.v.pats.args.%(i)))) in
    let* Exists tomatches = T.type_tomatches env tomatches in
    let module V = T.PrepareTomatch.TomatchWithContextVector in
    let section = V.to_tomatch_vector tomatches in
    let pats =
      clauses |> Vector.mapi (fun index _ -> V.proj_pats index tomatches) in
    return (Exists { section; pats })

  type ('env, 'ind, 'nrealargs, 'tail_length, 'ind_tail)
        branch_clauses = Exists : {
      summary : ('env, 'ind, 'nrealargs, 'arity, 'args) ConstructorSummary.t;
      clauses : ('env, 'arity, 'tail_length, 'ind_tail)
        prepare_clause list;
    } -> ('env, 'ind, 'nrealargs, 'tail_length, 'ind_tail)
        branch_clauses

  module CompileCase (Case : CompileCaseS) = struct
    open Case

    let compile_branch_body
        (type height args refine_patterns eqns_length tail_length ind_tail
          patterns_height generalized_height tail_height nrealdecls'
          nrealargs' old_previously_bounds new_previously_bounds
          generalize_count refine_tomatches)
        (args_env : (env * height) GlobalEnv.t)
        (summary : (env, ind, nrealargs, height, args) ConstructorSummary.t)
        (generalized_return_pred :
          (env * generalized_height, nrealdecls Nat.succ * tail_height)
          ReturnPred.t)
        (height : height Height.t)
        (args : (env, height, args) ERelContext.t)
        (clauses :
           ((env, height, tail_length, ind_tail)
             prepare_clause, eqns_length)
           Vector.t)
        (generalize_context :
          (env, patterns_height, generalize_count, generalized_height)
            generalize_context_desc)
        (arity_terms : (env ETerm.t, patterns_height) Vector.t)
        (refine_apply :
          (((env * height) * refine_tomatches) ETerm.t, patterns_height)
          Vector.t)
        (refine_terms :
          (((env * height) * refine_tomatches) ETerm.t, nrealdecls Nat.succ)
          Vector.t)
        (old_previously_bounds :
          ((env * height) Rel.t, old_previously_bounds) Vector.t)
        (new_previously_bounds :
          (generalize_count Fin.t, new_previously_bounds) Vector.t)
        (new_tomatches :
          ((env * generalized_height) EJudgment.t, tail_length) Vector.t)
        (tomatches_plus :
          (height, refine_tomatches, refine_patterns) Nat.plus)
        (tail_tomatches :
          (env * height, tail_length, <ind: ind_tail; size: tail_height>)
            TomatchVector.t) :
        (env * height, refine_patterns, nrealdecls', nrealargs') Rhs.f =
    fun { globenv; context; return_pred; matches } ->
      let open EvarMapMonad.Ops in
      let subcontext =
        ERelContext.set_names_from_env (GlobalEnv.env globenv) context in
      let generalizable, refineds =
        Vector.cut tomatches_plus (Vector.rev matches) in
      let refineds = Vector.rev refineds in
      let* sigma = EvarMapMonad.get in
      let generalizable =
        Vector.map (EJudgment.of_term (GlobalEnv.env globenv) sigma)
          generalizable in
      let* Exists prepare =
        prepare_sub_tomatches globenv generalizable clauses in
      let patterns_height = Height.of_nat (Vector.length arity_terms) in
      let refine_patterns = Height.of_nat (Vector.length matches) in
      let refine_tomatches = Height.of_nat (Vector.length refineds) in
      let nrealdecls' = Height.of_nat (ERelContext.length subcontext) in
      let refined_apply = refine_apply |> Vector.map (fun term -> term |>
        ETerm.liftn nrealdecls' refine_tomatches |>
        ETerm.substl (Height.Vector.of_vector refineds)) in
      let make_generalized_context env =
        generalize_context.context env |>
        ERelContext.exliftn
          Lift.(liftn patterns_height (height & + nrealdecls')) |>
        ERelContext.substl (Height.Vector.of_vector refined_apply) in
      let generalized_context =
        make_generalized_context (GlobalEnv.env env) in
      let* genenv =
        push_rel_context_m (ERelContext.with_height generalized_context)
          globenv in
      let generalize_count =
        Height.of_nat (ERelContext.length generalized_context) in
      let generalized_height =
        Height.Ops.(generalize_count + patterns_height) |>
        Eq.(cast (Height.morphism (Env.plus generalize_context.sum_binders))) in
      let Exists plus =
        Nat.to_plus (TomatchVector.length prepare.section) in
      let* sigma = EvarMapMonad.get in
      let lift = Lift.(height & + nrealdecls') in
      let lift' = Lift.(liftn generalized_height lift) in
      let generalize_match (j : (env * generalized_height) ETerm.t) = j |>
        ETerm.exliftn lift' |>
        Eq.(cast (ETerm.morphism (Env.morphism Refl
          (sym (Env.rev_plus generalize_context.sum_binders)) ++
          (sym Env.assoc)))) |>
        ETerm.substnl (Height.Vector.of_vector refined_apply)
          generalize_count in
      let generalize_tomatch (j : (env * generalized_height) EJudgment.t) = j |>
        EJudgment.exliftn lift' |>
        Eq.(cast (EJudgment.morphism (Env.morphism Refl
          (sym (Env.rev_plus generalize_context.sum_binders)) ++
          (sym Env.assoc)))) |>
        EJudgment.substnl (Height.Vector.of_vector refined_apply)
          generalize_count in
      let eqns =
        Vector.map2 (fun
          (Exists { loc; v = clause } : _ prepare_clause)
          (Exists new_pats : _ Patterns.exists_section) :
            _ Clause.t ->
          let names =
            new_pats |> Patterns.to_vector { f = fun (type a b)
              (I (pat, _) : (_, a, b) Patterns.A.t) ->
                TypedPattern.get_name pat } in
          let context = ERelContext.set_names (Vector.rev names) args in
          let generalized_context =
            make_generalized_context (GlobalEnv.env clause.env) in
          let env = clause.env |>
            push_rel_context sigma (ERelContext.with_height context) |>
            push_rel_context sigma (ERelContext.with_height subcontext) |>
            push_rel_context sigma
              (ERelContext.with_height generalized_context) in
          let Exists new_pats = Patterns.resize new_pats in
          let as_pat =
            CAst.make { TypedPattern.name = clause.pats.as_name; desc = Var } in
          let old_pats =
            Patterns.exliftn Lift.(height & + nrealdecls') clause.pats.tail in
          let pats =
            Patterns.append new_pats.section
              (I (as_pat, Succ_plus Zero_l) :: old_pats) plus in
          let pats = Patterns.lift generalize_count pats in
          let Exists { matches; cont } = clause.rhs in
(*
          Format.eprintf "generalize matches: %a@."
            Pp.pp_with (Pp.pr_enum (ETerm.print (GlobalEnv.env Case.env) sigma)
              (Vector.to_list matches));
*)
          let Exists { accu = { binders; _ }; result = matches } =
            generalize_terms ~allow_new_binders:false (GlobalEnv.env Case.env)
              sigma matches generalize_context in
          let Refl =
            match binders with
            | Zero_l -> Nat.zero_l_eq binders
            | Succ_plus _ -> assert false in
          let cont = cont |>
            Rhs.push_cont context |>
            Rhs.push_cont subcontext |>
            Rhs.push_cont generalized_context in
          let matches = Vector.map generalize_match matches in
          let rhs : _ Rhs.t = Exists { matches; cont } in
          Clause.check ?loc { env; ids = clause.ids; pats; rhs })
            clauses prepare.pats in
      let section = prepare.section |>
        TomatchVector.lift generalize_count in
      let new_tomatches =
        Vector.map generalize_tomatch new_tomatches in
      let new_tail_tomatches = tail_tomatches |>
        TomatchVector.exliftn Lift.(nrealdecls' & + generalize_count) |>
        TomatchVector.change (GlobalEnv.env genenv) sigma new_tomatches
          ~small_inversion:MatchContext.small_inversion in
(*
      let self_judgment =
        if expand_self then
          let self = summary |>
            ConstructorSummary.exliftn lift |>
            ConstructorSummary.build_dependent_constructor |>
            ETerm.of_term |>
            ETerm.substl (Height.Vector.of_vector
              (Vector.rev_map EJudgment.uj_val generalizable)) in
          EJudgment.of_term (GlobalEnv.env globenv) sigma self
        else
          EJudgment.exliftn lift tomatch.judgment in
      Format.eprintf "expand_self: %b@.self judgment: %a@." expand_self Pp.pp_with
        (EJudgment.print (GlobalEnv.env globenv) sigma self_judgment);
*)
        let self = summary |>
          ConstructorSummary.exliftn lift |>
          ConstructorSummary.build_dependent_constructor |>
          ETerm.of_term |>
          ETerm.substl (Height.Vector.of_vector
            (Vector.rev_map EJudgment.uj_val generalizable)) in
      let* self_type, _ =
        EvarMapMonad.new_type_evar (GlobalEnv.env globenv)
          Evd.univ_flexible_alg in
      let* self_evar =
        EvarMapMonad.new_evar (GlobalEnv.env globenv)
          ~candidates:[ETerm.exliftn lift (EJudgment.uj_val tomatch.judgment);
            self] self_type in
      let self_judgment = EJudgment.make self_evar self_type in
      let self_tomatch =
        Tomatch.make_not_inductive
          (EJudgment.lift generalize_count self_judgment)
          Anonymous in
      let new_tomatches =
        TomatchVector.append section (I self_tomatch :: new_tail_tomatches)
          plus in
      let Exists return_pred_height =
        TomatchVector.partial_height prepare.section in
      let Exists new_height =
        TomatchVector.partial_height prepare.section in
      let vector =
        Height.Vector.rev (TomatchVector.concat_rev_map
          { f = fun tomatch ->
            get_tomatch_args (GlobalEnv.env genenv) tomatch }
              new_tomatches) in
      let old_previously_bounds = old_previously_bounds |> Vector.map
        (fun r ->
        Rel.exliftn Lift.(nrealdecls' & + generalize_count) r) in
      let new_previously_bounds =
        Vector.map Rel.of_fin new_previously_bounds in
      let Exists { vector = previously_bounds; _ } =
        Vector.Ops.(new_previously_bounds @ old_previously_bounds) in
(*
      let Exists { vector = previously_bounds; _ } =
        Vector.Ops.(Vector.init summary.arity (fun i ->
          let rel =
            match ETerm.destRel sigma (EJudgment.uj_val generalizable.%(i)) with
            | Some rel -> rel
            | None -> Rel.lift nrealdecls' (Rel.of_fin i) in
          Rel.lift generalize_count rel) @ previously_bounds) in
      Format.eprintf "env: %a@.previously_bounds: %a@."
        Pp.pp_with (Env.print (GlobalEnv.env genenv))
        Pp.pp_with (Pp.pr_enum (fun i -> Pp.int (Rel.to_int i))
          (Vector.to_list previously_bounds));
*)
      let tail_height = TomatchVector.height tail_tomatches in
(*
      Format.eprintf "refine: %a@."
        Pp.pp_with (Pp.pr_enum ETerm.debug_print
          (Vector.to_list refine_terms));
*)
      let generalized_return_pred = generalized_return_pred |>
        ReturnPred.exliftn
          Lift.(liftn generalized_height (height & + refine_tomatches))  |>
        ReturnPred.apply
          (Vector.rev_map (ETerm.lift generalized_height) refine_terms)
          tail_height in
      let generalized_return_pred = generalized_return_pred |>
        ReturnPred.morphism Eq.(
          Env.morphism Refl (
            sym (Env.rev_plus generalize_context.sum_binders)) ++
          sym Env.assoc) Refl in
      let generalized_return_pred = generalized_return_pred |>
        ReturnPred.substnl (Height.Vector.of_vector refine_apply)
          generalize_count in
      let generalized_return_pred = generalized_return_pred |>
        ReturnPred.morphism
          Eq.(Env.morphism Env.assoc Refl ++ Env.assoc ++
            Env.morphism Refl (Env.morphism (Env.plus tomatches_plus) Refl))
          Refl in
(*
      Format.eprintf "sub env: %a@.generalized_return_pred: %a@."
        Pp.pp_with (Env.print (GlobalEnv.env genenv))
        Pp.pp_with (ReturnPred.debug_print generalized_return_pred);
      Format.eprintf "matches: %a@."
        Pp.pp_with (Pp.pr_enum ETerm.debug_print (Vector.to_list matches));
*)
      let generalized_return_pred = generalized_return_pred |>
        ReturnPred.exliftn
          Lift.(liftn Height.Ops.(refine_patterns + generalize_count)
            (height & + nrealdecls')) |>
        ReturnPred.morphism Eq.(sym Env.assoc) Refl |>
        ReturnPred.substnl (Height.Vector.of_vector matches)
          generalize_count in
(*
      Format.eprintf "subst generalized_return_pred: %a@."
        Pp.pp_with (ReturnPred.debug_print generalized_return_pred);
*)
      let generalized_return_pred = generalized_return_pred |>
        ReturnPred.lift_return Height.one |>
        ReturnPred.lift_return new_height.diff in
      let generalized_return_pred = generalized_return_pred |>
        ReturnPred.morphism Refl new_height.plus in
      let Exists return_pred_context =
        TomatchVector.make_return_pred_context new_tomatches in
(*
      Format.eprintf "sub env: %a@.return pred: %a@."
        Pp.pp_with (Env.print (GlobalEnv.env genenv))
        Pp.pp_with (ETerm.debug_print (ReturnPred.get generalized_return_pred));
*)
      let sub_problem = {
        PatternMatchingProblem.env = genenv;
        tomatches = new_tomatches; eqns;
        return_pred = generalized_return_pred;
        previously_bounds;
        expand_self;
      } in
      let* judgment = MatchContext.compile_loop sub_problem in
      let sub_return_pred =
        ETerm.substl vector (ReturnPred.get generalized_return_pred) in
      let* sigma = EvarMapMonad.get in
(*
      Format.eprintf "inh_conv_coerce_to @[%a@] to @[%a@] in env @[%a@]@."
        Pp.pp_with (EJudgment.print (GlobalEnv.env sub_problem.env) sigma judgment)
        Pp.pp_with (ETerm.print (GlobalEnv.env sub_problem.env) sigma sub_return_pred)
        Pp.pp_with (Env.print (GlobalEnv.env sub_problem.env));
      Format.eprintf "source type: @[%a@]@."
        Pp.pp_with (ETerm.print (GlobalEnv.env sub_problem.env) sigma (ETerm.whd_all (GlobalEnv.env sub_problem.env) sigma (EJudgment.uj_type judgment)));
      Format.eprintf "target type: @[%a@]@."
        Pp.pp_with (ETerm.print (GlobalEnv.env sub_problem.env) sigma (ETerm.whd_all (GlobalEnv.env sub_problem.env) sigma sub_return_pred));
*)
      let* judgment, _ =
        EJudgment.inh_conv_coerce_to ~program_mode:MatchContext.program_mode
          ~resolve_tc:true (GlobalEnv.env sub_problem.env) judgment
          sub_return_pred in
      return (ERelContext.it_mkLambda_or_LetIn_judgment
        (ERelContext.with_height generalized_context) judgment)

    let compile_branch
        (type params tail_length ind_tail
          tail_height generalized_height patterns_height
          old_previously_bounds new_previously_bounds
          generalized_count)
        (ind : (env, ind, params, nrealargs, nrealdecls) InductiveType.t)
        (inverted_return_pred :
           ((env * nrealdecls Nat.succ) * tail_height) ETerm.t)
        (generalized_return_pred :
          (env * generalized_height, nrealdecls Nat.succ * tail_height)
          ReturnPred.t)
        (arity_patterns :
          (nrealargs Nat.succ, env, patterns_height, Nat.zero)
            Pattern.of_terms_exists)
        (old_previously_bounds : (env Rel.t, old_previously_bounds) Vector.t)
        (new_previously_bounds :
          (generalized_count Fin.t, new_previously_bounds) Vector.t)
        (new_tomatches :
          ((env * generalized_height) EJudgment.t, tail_length)
             Vector.t)
        (generalize_context :
          (env, patterns_height, generalized_count, generalized_height)
            generalize_context_desc)
        (tail_tomatches :
          (env, tail_length, <ind: ind_tail; size: tail_height>)
            TomatchVector.t)
        (Exists { summary; clauses } :
           (env, ind, nrealargs, tail_length, ind_tail)
           branch_clauses) :
        env ETerm.t EvarMapMonad.t =
      let open EvarMapMonad.Ops in
      let Exists clauses = Vector.of_list (List.rev clauses) in
      let args = ERelContext.of_rel_context summary.args in
      let all_vars =
        List.fold_left
          (fun all_vars (Exists { v = clause } : _ prepare_clause) ->
            Names.Id.Set.union all_vars clause.ids)
          (GlobEnv.vars_of_env (Eq.cast GlobalEnv.eq env))
          (Vector.to_list clauses) in
      let concrete_args =
        Array.of_list (List.rev (ERelContext.to_concrete args)) in
      let* sigma = EvarMapMonad.get in
      let names =
        Vector.init summary.arity (fun i ->
          let name =
            Vector.find_name
              (fun (Exists { v = clause } : _ prepare_clause) ->
                let names =
                  clause.pats.args |> Pattern.to_vector |>
                  Vector.map (fun (Exists pat : Pattern.exists) ->
                    pat.v.name) in
                Vector.Ops.(names.%(i)))
              clauses in
          if name = Anonymous then
            begin
              let decl = concrete_args.(Fin.to_int i) in
              let name =
                Namegen.named_hd (Eq.cast Env.eq (GlobalEnv.env env))
                  sigma (Context.Rel.Declaration.get_type decl)
                  (Context.Rel.Declaration.get_name decl) in
              Names.Name (Namegen.next_name_away name all_vars)
            end
          else
            name) in
      let args = ERelContext.set_names (Vector.rev names) args in
      let* args_env = push_rel_context_m (ERelContext.with_height args) env in
      let* sigma = EvarMapMonad.get in
      let self =
        ETerm.of_term
          (ConstructorSummary.build_dependent_constructor summary) in
      let* branch =
        match
          refine_patterns (GlobalEnv.env args_env) sigma arity_patterns.args
            (Vector.append_plus summary.concl_realargs [self]
              (Nat.plus_one summary.nrealargs))
        with
        | None ->
            let* j = EJudgment.unit_m (GlobalEnv.env args_env) in
            return (EJudgment.uj_val j)
        | Some (Exists refine) ->
            let height = Height.of_nat summary.arity in
            let module EqnLength = struct type t = Nat.one Nat.succ end in
            let module T = TypeTomatch (EqnLength) in
            let refine_tomatches =
              refine.result.tomatches |> Vector.mapi (fun i judgment ->
                TomatchTuple.make_pair
                  Pattern.Ops.(refine.result.patterns.%(i)) judgment) in
            let generalizable =
              ERelContext.to_rel_vector_decls args |> Vector.rev_map
                (TomatchTuple.make_pair (Pattern.ex_var Anonymous)) in
            let Exists { vector = tomatches; plus = tomatches_plus } =
              Vector.Ops.(generalizable @ refine_tomatches) in
            let tomatch_length = Vector.length tomatches in
            let* Exists tomatches = T.type_tomatches args_env tomatches in
            let module V = T.PrepareTomatch.TomatchWithContextVector in
            let Exists pats_ok = V.proj_pats Fin.zero tomatches in
            let Exists pats_reject = V.proj_pats Fin.one tomatches in
            let ids = Names.Id.Set.empty in
            let tail_tomatches = TomatchVector.lift height tail_tomatches in
            let arity =
              InductiveFamily.get_arity (GlobalEnv.env args_env)
                (InductiveFamily.lift height ind.family) in
            let return_pred_height = V.height tomatches in
            let return_pred_args_height =
              Height.of_nat (S ind.family.nrealdecls) in
            let tomatches = V.to_tomatch_vector tomatches in
            let refine_length =
              Pattern.size_of_args refine.result.patterns O in
            let refine_height = Height.of_nat refine_length in
            let Exists match_length =
              Nat.Ops.(Vector.length generalizable + refine_length) in
            let tomatch_height =
              Height.of_nat (Vector.length refine.result.tomatches) in
            let locals : _ Vector.t =
              let hd :: tl = Vector.rev refine.locals in
              let arity = ERelContext.lift tomatch_height arity in
              hd :: Vector.rev (ERelContext.subst_of_instance arity tl) in
            let terms : _ Vector.t =
              let hd :: tl = Vector.rev refine.terms in
              let arity = ERelContext.lift refine_height arity in
              hd :: Vector.rev (ERelContext.subst_of_instance arity tl) in
            let old_previously_bounds =
              Vector.map (Rel.lift height) old_previously_bounds in
            let Exists { vector = old_previously_bounds; _ } =
              Vector.Ops.(
                Vector.init summary.arity (fun i -> Rel.of_fin i) @
                old_previously_bounds) in
            let make_body rhs_args =
              compile_branch_body args_env summary
                generalized_return_pred height args clauses
                generalize_context
                arity_patterns.terms refine.result.apply terms
                old_previously_bounds
                new_previously_bounds new_tomatches match_length.plus
                tail_tomatches rhs_args in
            let make_idprop ({ globenv; _ } : _ Rhs.args) =
              EJudgment.unit_m (GlobalEnv.env globenv) in
            let* sigma = EvarMapMonad.get in
  (*
            Format.eprintf "refine env: %a@." Pp.pp_with
              (Env.print (GlobalEnv.env args_env));
  *)
            let vector =
              Height.Vector.rev (TomatchVector.concat_rev_map
                { f = fun tomatch ->
                  get_tomatch_args (GlobalEnv.env args_env) tomatch }
                    tail_tomatches) in
            let tail_height = TomatchVector.height tail_tomatches in
            let _, self_vector =
              TomatchVector.make_self_vector tomatches in
(*
            Format.eprintf "inverted return pred: %a@."
              Pp.pp_with (ETerm.debug_print inverted_return_pred);
            Format.eprintf "locals: %a@." Pp.pp_with
              (Pp.pr_enum ETerm.debug_print (Vector.to_list locals));
            Format.eprintf "self_vector: %a@." Pp.pp_with
              (Pp.pr_enum ETerm.debug_print (Vector.to_list self_vector));
            Format.eprintf "vector: %a@." Pp.pp_with
              (Pp.pr_enum ETerm.debug_print (Height.Vector.to_list vector));
*)
            let return_pred = inverted_return_pred |>
              Eq.(cast (ETerm.morphism Env.assoc)) |>
              ETerm.liftn height
                Height.Ops.(return_pred_args_height + tail_height) |>
              Eq.(cast (ETerm.morphism (sym Env.assoc))) |>
              ETerm.substl
                (Height.Vector.map (ETerm.lift return_pred_args_height)
                  vector) |>
              ETerm.liftn tomatch_height return_pred_args_height |>
              ETerm.substl (Height.Vector.of_vector locals) |>
              Eq.(cast (ETerm.morphism (Env.assoc ++
                Env.morphism Refl (Env.plus tomatches_plus)))) |>
              ETerm.exliftn Lift.(liftn (Height.of_nat tomatch_length)
                 (height & + return_pred_height)) |>
              ETerm.substl
                (Height.Vector.of_vector (Vector.rev self_vector)) in
            let Exists return_pred_context =
              TomatchVector.make_return_pred_context tomatches in
            let* return_pred_env =
              push_rel_context_m (Exists return_pred_context.context)
                args_env in
            let* sigma = EvarMapMonad.get in
(*
            Format.eprintf "refined return pred: %a in env %a@."
              Pp.pp_with (ETerm.print (GlobalEnv.env return_pred_env) sigma
                return_pred)
              Pp.pp_with (Env.print (GlobalEnv.env return_pred_env));
*)
            let problem = {
              PatternMatchingProblem.env = args_env;
              tomatches;
              return_pred = ReturnPred.make return_pred return_pred_height;
              eqns = [
                Clause.check { env = args_env; ids; pats = pats_ok;
                  rhs = Rhs.make match_length.sum { f = make_body }; };
                Clause.check { env = args_env; ids; pats = pats_reject;
                  rhs = Rhs.make tomatch_length { f = make_idprop; }; }];
              previously_bounds = old_previously_bounds;
              expand_self = true;
            } in
            let* body = MatchContext.compile_loop problem in
            return (EJudgment.uj_val body) in
      return (ERelContext.it_mkLambda_or_LetIn (ERelContext.with_height args)
        branch)

    type ('env, 'ind, 'nrealdecls, 'tail_height) compile_branches = {
        branches : ('env ETerm.t, 'ind) Tuple.t;
        return_pred :
          (('env * 'nrealdecls Nat.succ) * 'tail_height) ETerm.t;
        apply : 'env ETerm.t Vector.exists;
      }

    let compile_branches
        (type params tail_length ind_tail
          tail_height previously_bounds)
        (tomatch_type :
          (env, ind, params, nrealargs, nrealdecls) TomatchType.desc)
        (tomatch_vector : (env EJudgment.t, tail_length) Vector.t)
        (return_pred : (env, (nrealdecls Nat.succ * tail_height)) ReturnPred.t)
        (tomatches :
           (env, tail_length Nat.succ,
             <ind: ind TomatchType.some * ind_tail;
               size: nrealdecls Nat.succ * tail_height>)
           TomatchVector.t)
        (branches :
           ((env, ind, nrealargs, tail_length, ind_tail)
             branch_clauses, ind) Tuple.t)
        (previously_bounds : (env Rel.t, previously_bounds) Vector.t) :
        (env, ind, nrealdecls, tail_height) compile_branches EvarMapMonad.t =
      let open EvarMapMonad.Ops in
      let* sigma = EvarMapMonad.get in
      let Exists arity_patterns = tomatch_type.pattern_structure in
(*
       Format.eprintf "env: @[%a@]@.arity_patterns.terms: @[%a@]@."
          Pp.pp_with (Env.print (GlobalEnv.env env))
          Pp.pp_with (Pp.pr_enum ETerm.debug_print (Vector.to_list arity_patterns.terms));
*)
      let patterns_height =
        Height.of_nat (Vector.length arity_patterns.terms) in
(*
      Format.eprintf "env: %a@."
        Pp.pp_with (Env.print (GlobalEnv.env env));
*)
      let generalize_context =
        generalize_context_of_binders (GlobalEnv.env env) sigma
          arity_patterns.terms in
(*
      Format.eprintf "binders: %a@."
        Pp.pp_with
        (Pp.pr_enum (ETerm.print (GlobalEnv.env env) sigma)
          (let Exists context = generalize_context in
            Vector.to_list context.binders));
*)
      let Exists { context = generalize_context; old_previously_bounds;
          new_previously_bounds } =
        generalize_previously_bounds (GlobalEnv.env env) sigma
          previously_bounds generalize_context in
(*
      Format.eprintf "previously_bounds: %a@.binders (previously bounds): %a@."
        Pp.pp_with
        (Pp.pr_enum (fun i -> Pp.int (Rel.to_int i))
           (Vector.to_list previously_bounds))
        Pp.pp_with
        (Pp.pr_enum (ETerm.print (GlobalEnv.env env) sigma)
          (Vector.to_list generalize_context.binders));
*)
      let Exists {
        accu = { level = diff_tomatches; context = generalize_context };
        result = tomatch_vector } =
        generalize_judgments (GlobalEnv.env env) sigma tomatch_vector
          generalize_context in
      let Exists { context; _ } =
        TomatchVector.make_return_pred_context tomatches in
      let Exists return_pred_desc = return_pred in
      Format.eprintf "previous: %a@.binders (tomatch): %a@."
        Pp.pp_with
        (Pp.pr_enum (ETerm.print (GlobalEnv.env env) sigma)
          (Vector.to_list return_pred_desc.previous))
        Pp.pp_with
        (Pp.pr_enum (ETerm.print (GlobalEnv.env env) sigma)
          (Vector.to_list generalize_context.binders));
      let Exists { accu = { binders = diff_previous; context = context' };
          result = previous } =
        generalize_terms ~allow_new_binders:false (GlobalEnv.env env) sigma
          return_pred_desc.previous generalize_context in
      Format.eprintf "generalized previous: %a@.binders: %a@."
        Pp.pp_with
        (Pp.pr_enum ETerm.debug_print
          (Vector.to_list previous))
        Pp.pp_with
        (Pp.pr_enum (ETerm.print (GlobalEnv.env env) sigma)
          (Vector.to_list context'.binders));
      let Refl =
        match diff_previous with
        | Zero_l -> Nat.zero_l_eq diff_previous
        | Succ_plus _ -> assert false in
(*
      Format.eprintf "env: %a@." Pp.pp_with (Env.print (GlobalEnv.env env));
      Format.eprintf "return pred: %a@." Pp.pp_with
        (ReturnPred.debug_print return_pred);
*)
      let sub_return_pred =
        let hypnaming = naming_of_program_mode MatchContext.program_mode in
        ReturnPred.generalize ~hypnaming env sigma (Exists context)
          patterns_height generalize_context.sum_binders
          generalize_context.binders previous return_pred_desc in
(*
      Format.eprintf "sub return pred: %a@." Pp.pp_with
        (ReturnPred.debug_print sub_return_pred);
*)
      let new_previously_bounds =
        Vector.map (Fin.add diff_tomatches) new_previously_bounds in
      let* inverted_return_pred =
        let arity =
          InductiveFamily.get_arity (GlobalEnv.env env)
            tomatch_type.inductive_type.family in
        invert_return_pred env tomatch_type.inductive_type arity
          (TomatchVector.tl tomatches)
          arity_patterns.args patterns_height
          (generalize_context.context (GlobalEnv.env env))
          generalize_context.sum_binders
          (ReturnPred.get sub_return_pred) tomatch.return_pred_height in
(*
      Format.eprintf "previous: %a@." Pp.pp_with
        (Pp.pr_enum ETerm.debug_print
          (Vector.to_list return_pred_desc.previous));
      Format.eprintf "generalized previous: %a@." Pp.pp_with
        (Pp.pr_enum ETerm.debug_print (Vector.to_list previous));
      Format.eprintf "sub return pred: %a@." Pp.pp_with
        (ReturnPred.debug_print sub_return_pred);
      Format.eprintf "inverted return pred: %a@." Pp.pp_with
        (ETerm.debug_print inverted_return_pred);
*)
      let* branches =
        branches |> Tuple.State.map
          (compile_branch tomatch_type.inductive_type
             inverted_return_pred sub_return_pred arity_patterns
             old_previously_bounds new_previously_bounds tomatch_vector
             generalize_context
             (TomatchVector.tl tomatches)) in
      return { branches; return_pred = inverted_return_pred;
        apply = Exists generalize_context.apply; }
  end

  let compile_destruct
      (type env ind params nrealargs nrealdecls tail_length ind_tail eqns_length
        tail_height previously_bounds)
      (tomatch : (env, ind TomatchType.some, nrealdecls Nat.succ) Tomatch.t)
      (tomatch_type :
        (env, ind, params, nrealargs, nrealdecls) TomatchType.desc)
      (problem :
        (env, tail_length Nat.succ, ind TomatchType.some * ind_tail,
          eqns_length, nrealdecls Nat.succ * tail_height,
          previously_bounds) PatternMatchingProblem.t) :
      env EJudgment.t EvarMapMonad.t =
    let open Tuple.Ops in
    let open EvarMapMonad.Ops in
    let env = GlobalEnv.env problem.env in
    let specif =
      InductiveSpecif.lookup env
        (fst (tomatch_type.inductive_type.family.def)) in
    let constructors = InductiveSpecif.constructors specif in
    let constructor_summaries =
      ConstructorSummary.get_tuple env tomatch_type.inductive_type.family
        specif in
    let nb_cstr = Tuple.length constructors in
    let branches = Tuple.init nb_cstr (fun i ->
      let Exists summary = constructor_summaries.%(i) in
      Exists { summary; clauses = [] }) in
    let add_eqn (Exists { v = clause; loc } :
        (env, tail_length Nat.succ, ind TomatchType.some * ind_tail) Clause.t) =
      let I (pat, plus) :: tail = clause.pats in
      match pat.v.desc with
      | Var ->
          Tuple.iter branches (fun i ->
            let Exists { summary; clauses } = branches.%(i) in
            let Exists { args; plus = args_plus } =
              Pattern.make_vars summary.arity in
            let pats = { as_name = pat.v.name; args; tail } in
            let Exists n = Nat.to_plus summary.arity in
            let rhs = Rhs.produce plus n clause.rhs in
            let clause = CAst.make ?loc Clause.{ clause with pats; rhs } in
            let Succ_plus Zero_l = plus in
            let Succ_plus plus' = Nat.move_succ_left n in
            let Refl = Nat.plus_fun args_plus plus' in
            branches.%(i) <-
              Exists { summary; clauses = Exists clause :: clauses })
      | Cstr { cstr; args } ->
          let i = Constructor.index cstr.cstr in
          let Exists { summary; clauses } = branches.%(i) in
          let Refl = Option.get (Nat.is_eq summary.arity cstr.arity) in
          let Exists { args; diff_a; diff_b } =
            Pattern.replace_args args in
          let Refl = Nat.zero_r_eq (Nat.move_succ_left diff_a) in
          let pats = { as_name = pat.v.name; args; tail } in
          let clause = CAst.make ?loc Clause.{ clause with pats } in
          let Refl = Nat.zero_r_eq (Nat.move_succ_left diff_a) in
          let Succ_plus plus' = plus in
          let Refl = Nat.plus_fun diff_b plus' in
          branches.%(i) <-
            Exists { summary; clauses = Exists clause :: clauses } in
    Vector.iter add_eqn problem.eqns;
    let tail_tomatches = TomatchVector.tl problem.tomatches in
    let tomatch_vector =
      let f (type a b) (I tomatch : (_, a, b) TomatchVector.A.t) =
        tomatch.judgment in
      TomatchVector.to_vector { f } tail_tomatches in
    let module Case = struct
      let expand_self = problem.expand_self
      type nonrec env = env
      type nonrec ind = ind
      type nonrec nrealargs = nrealargs
      type nonrec nrealdecls = nrealdecls
      let env = problem.env
      let tomatch = tomatch
    end in
    let module Compiler = CompileCase (Case) in
    let* { branches; return_pred; apply = Exists apply } =
      Compiler.compile_branches tomatch_type
        tomatch_vector problem.return_pred problem.tomatches
        branches problem.previously_bounds in
    let* sigma = EvarMapMonad.get in
    let tail_return_vector =
      tail_tomatches |>
      TomatchVector.concat_rev_map { f = fun tomatch ->
        get_tomatch_args (GlobalEnv.env problem.env) tomatch } |>
      Height.Vector.rev in
    let tail_return_height_vector =
      Height.Vector.map (ETerm.lift tomatch.return_pred_height)
        tail_return_vector in
    let local_return_pred =
      ETerm.substl tail_return_height_vector return_pred in
    let case =
      let return_pred =
        ERelContext.it_mkLambda_or_LetIn tomatch.return_pred_context
          local_return_pred in
(*
      Format.eprintf "return_pred: %a@." Pp.pp_with
        (ETerm.print env sigma return_pred);
*)
(*
      Format.eprintf "return_pred (debug): %a@." Pp.pp_with
        (ETerm.debug_print return_pred);
*)
      InductiveType.make_case_or_project (GlobalEnv.env problem.env) sigma
        tomatch_type.inductive_type
        MatchContext.style ~tomatch:(EJudgment.uj_val tomatch.judgment)
        ~return_pred branches in
    let apply = Vector.to_list (Vector.rev apply) in
(*
    Format.eprintf "before degeneralize: %a@.in env: %a@."
      Pp.pp_with (ETerm.print env sigma case)
      Pp.pp_with (Env.print env);
*)
    let case, apply' =
      degeneralize_list env sigma case apply in
(*
    Format.eprintf "after degeneralize: %a@.in env: %a@."
      Pp.pp_with (ETerm.print env sigma case)
      Pp.pp_with (Env.print env);
*)
    let case = ETerm.mkApp case (Array.of_list apply') in
(*
    let* sigma = EvarMapMonad.get in
    Format.eprintf "compiled case: %a@.in env: %a@."
      Pp.pp_with (ETerm.print env sigma case)
      Pp.pp_with (Env.print env);
*)
    let ty = ReturnPred.get problem.return_pred in
    let ty = Eq.cast (ETerm.morphism (Eq.sym Env.assoc)) ty in
    let ty = ETerm.substl tail_return_height_vector ty in
(*
    Format.eprintf "case type: %a@.in env: %a@."
      Pp.pp_with (ETerm.debug_print ty)
      Pp.pp_with (Env.print env);
    Format.eprintf "tomatch_args: %a@."
      Pp.pp_with (Pp.pr_sequence (ETerm.print env sigma)
        (Vector.to_list (get_tomatch_args env tomatch)));
*)
    let ty =
      ETerm.substl (Height.Vector.of_vector (get_tomatch_args env tomatch))
        ty in
(*
    let* sigma = EvarMapMonad.get in
    Format.eprintf "case type: %a@.in env: %a@."
      Pp.pp_with (ETerm.print env sigma ty)
      Pp.pp_with (Env.print env);
*)
    (*
    let ty = ETerm.prod_applist sigma
      (ETerm.substl (Height.Vector.of_vector (get_tomatch_args env tomatch))
        local_return_pred) apply in *)
    let j = EJudgment.make case ty in
    return j

  let compile_case
      (type env ind tail_length ind_tail eqns_length return_pred_height
        tail_height previously_bounds)
      (tomatch : (env, ind, return_pred_height) Tomatch.t)
      (problem :
         (env, tail_length Nat.succ, ind * ind_tail, eqns_length,
           return_pred_height * tail_height, previously_bounds)
         PatternMatchingProblem.t) :
      env EJudgment.t EvarMapMonad.t =
    let Exists eqns =
      Vector.of_list
        (Clause.remove_trailing_eqns (Vector.to_list problem.eqns)) in
    let problem = { problem with eqns } in
    let module V = Vector.UseMonad (Monad.Option) in
    match
      V.map Clause.extract_pat_var problem.eqns, problem.eqns,
      tomatch.inductive_type
    with
    | None, _, Inductive _
    | Some _, [], Inductive _ ->
        begin match tomatch.inductive_type with
        | Not_inductive _ -> assert false
        | Inductive desc -> compile_destruct tomatch desc problem
        end
    | Some vars, _, _ ->
        compile_case_trivial tomatch vars problem
    | None, _, Not_inductive _ ->
        assert false

  let compile_loop
      (type env tomatch_length ind eqns_length return_pred_height
        previously_bounds)
      (problem :
         (env, tomatch_length, ind, eqns_length, return_pred_height,
           previously_bounds) PatternMatchingProblem.t) :
      env EJudgment.t EvarMapMonad.t =
    Format.eprintf "compile in env: %a@."
      Pp.pp_with (Env.print (GlobalEnv.env problem.env));
    match problem.tomatches with
    | [] ->
        begin match problem.eqns with
        | [] ->
            (* TODO: compute the history *)
            error_non_exhaustive (Eq.cast Env.eq (GlobalEnv.env problem.env)) []
        | _ :: _ -> compile_base problem
        end
    | I tomatch :: _ ->
        compile_case tomatch problem

  let make_inverted_return_pred
      (type env ind length return_pred_height)
      (env : env GlobalEnv.t)
      (tomatches : (env, length, <ind: ind; size: return_pred_height>)
         TomatchVector.t)
      (Exists context :
         (env, return_pred_height) TomatchVector.make_return_pred_context)
      (return_pred : env return_pred) :
      (env * return_pred_height) ETerm.t EvarMapMonad.t =
    let open EvarMapMonad.Ops in
    let* subenv = push_rel_context_m (Exists context.context) env in
    let module EqnLength = struct type t = Nat.one Nat.succ end in
    let module T = TypeTomatch (EqnLength) in
    let* sigma = EvarMapMonad.get in
    let tomatches_vector =
      context.context.context |>
      ERelContext.to_rel_vector |>
      Vector.rev |>
      Eq.(cast (Vector.eq (EJudgment.morphism
        (Env.morphism Refl context.context.eq)))) |>
      Vector.map TomatchTuple.of_judgment in
    let patterns_list =
      tomatches |> TomatchVector.to_vector { f =
        fun (type annot annot_tail)
          (I tomatch : (_, annot, annot_tail) TomatchVector.A.t) ->
        match tomatch.inductive_type with
        | Not_inductive _ -> 0, []
        | Inductive { pattern_structure = Exists { args; _ }; _ } ->
            Nat.to_int (Pattern.size_of_args args O),
            Vector.map (
              fun pattern ->
                Vector.[
                  pattern;
                  Pattern.ex_var Anonymous])
              (Pattern.to_vector args) |> Vector.to_list } |>
      Vector.to_list in
    let Exists patterns =
      Vector.of_list (List.flatten (List.map snd patterns_list)) in
    let Refl = Option.get (Nat.is_eq (Vector.length patterns)
      (Vector.length tomatches_vector)) in
    let tomatches = Vector.join tomatches_vector patterns in
    let* Exists tomatches = T.type_tomatches subenv tomatches in
    let module V = T.PrepareTomatch.TomatchWithContextVector in
    let binders_length_int =
      List.fold_left
        (fun acc (x, _) -> acc + x) 0 patterns_list in
    let Exists binders_length = Nat.of_int binders_length_int in
    let tomatch_length = Vector.length tomatches_vector in
    let Exists pats_ok = V.proj_pats Fin.zero tomatches in
    let Exists pats_reject = V.proj_pats Fin.one tomatches in
    let env = subenv in
    let ids = Names.Id.Set.empty in
    let tomatches = V.to_tomatch_vector tomatches in
    let Exists return_pred_context =
      TomatchVector.make_return_pred_context tomatches in
    let* return_pred_env =
      push_rel_context_m (Exists return_pred_context.context) env in
    let* s = Evd.new_sort_variable Evd.univ_flexible in
    let make_return_pred ({ globenv; context = context' } : _ Rhs.args) =
      let env = GlobalEnv.env globenv in
      let Exists context' =
        ERelContext.push context' context.context.context in
      let* return_pred = return_pred.f context'.context in
      let return_pred = return_pred |>
        Eq.(cast (ETerm.morphism (
          Env.morphism Refl (
            sym (Env.rev_plus context'.decls)) ++
          sym Env.assoc))) in
      let* sigma = EvarMapMonad.get in
(*
      Format.eprintf "get_sort_of: %a@." Pp.pp_with
        (EJudgment.print env sigma return_pred);
*)
      let s' = ETerm.get_sort_of env sigma return_pred in
      let* () = (*
        match s' with
        | SProp | Prop | Set -> EvarMapMonad.set_eq_sort env s' s
        | Type _ -> *) EvarMapMonad.set_leq_sort env s' s in
      let* sigma = EvarMapMonad.get in
      return (EJudgment.of_term env sigma return_pred) in
    let make_unit_rhs ({ globenv; _ } : _ Rhs.args) =
      let env = GlobalEnv.env globenv in
      let* unit_judgment = EJudgment.unit_m env in
      let* sigma = EvarMapMonad.get in
      return (EJudgment.of_term env sigma (EJudgment.uj_type unit_judgment)) in
    let problem = {
      PatternMatchingProblem.env;
      tomatches;
      return_pred =
        ReturnPred.make ~generalize:false (ETerm.mkSort s)
          (Eq.cast (Height.morphism return_pred_context.context.eq)
            (Height.of_nat return_pred_context.length));
      eqns = [
        Clause.check { env; ids; pats = pats_ok;
          rhs = Rhs.morphism (Env.morphism Refl context.context.eq)
            (Rhs.make binders_length { f = make_return_pred }); };
        Clause.check { env; ids; pats = pats_reject;
          rhs = Rhs.make tomatch_length { f = make_unit_rhs }; }];
      previously_bounds = [];
      expand_self = true;
    } in
    let* judgment = MatchContext.compile_loop problem in
(*
    let* sigma = EvarMapMonad.get in
    Format.eprintf "make inverted return pred: %a@." Pp.pp_with
      (EJudgment.print (GlobalEnv.env env) sigma judgment);
*)
    return (EJudgment.uj_val judgment)

  let compile_cases (type env tomatch_count eqns_length)
      ~(generalize_return_pred : bool)
      (env : env GlobalEnv.t)
      (return_pred : env return_pred)
      (tomatches : (env TomatchTuple.t, tomatch_count) Vector.t)
      (eqns :
         ((env, tomatch_count) Clause.untyped, eqns_length) Vector.t) :
      env EJudgment.t EvarMapMonad.t =
    let open EvarMapMonad.Ops in
    let module EqnLength = struct type t = eqns_length end in
    let module T = TypeTomatch (EqnLength) in
    let pats = eqns |> Vector.map (
    fun (Exists eqn : (env, tomatch_count) Clause.untyped) :
      (tomatch_count, Nat.zero) Pattern.args_exists_length ->
      Exists eqn.v.pats) in
    let module M = Vector.UseMonad (Monad.State) in
    let* tomatches =
      tomatches |> M.mapi (fun i tuple ->
        let get_pats (Exists pats : _ Pattern.args_exists_length) =
          Pattern.Ops.(pats.%(i)) in
        return (tuple, Vector.map get_pats pats)) in
    let* Exists tomatches = T.type_tomatches env tomatches in
    let* sigma = EvarMapMonad.get in
    let eqns =
      T.PrepareTomatch.TomatchWithContextVector.to_clauses env eqns tomatches in
    let tomatches =
      T.PrepareTomatch.TomatchWithContextVector.to_tomatch_vector tomatches in
    let Exists return_pred_context =
      TomatchVector.make_return_pred_context tomatches in
    let* return_pred =
      if tomatches |> TomatchVector.for_all { f = fun (type annot annot_tail)
          (I tomatch : (_, annot, annot_tail) TomatchVector.A.t) ->
            match tomatch.inductive_type with
            | Not_inductive _ -> true
            | Inductive { pattern_structure = Exists pattern_structure; _ } ->
                Pattern.args_all_vars pattern_structure.args } then
        begin
          let* return_pred =
            return_pred.f return_pred_context.context.context in
          let return_pred = return_pred |>
            Eq.cast (ETerm.morphism
              (Env.morphism Refl return_pred_context.context.eq)) in
          return return_pred
        end
      else
        begin
          make_inverted_return_pred env tomatches (Exists return_pred_context)
            return_pred
        end in
(*
    let* _, return_pred_env =
      push_rel_context_m return_pred_context.context env in
    let return_pred_env = return_pred_env |> Eq.cast (GlobalEnv.morphism
          (Env.morphism Refl return_pred_context.length_eq)) in
    let* sigma = EvarMapMonad.get in
    Format.eprintf "initial return pred: %a in env: %a@." Pp.pp_with
      (EJudgment.print (GlobalEnv.env return_pred_env) sigma return_pred)
      Pp.pp_with (Env.print (GlobalEnv.env return_pred_env));
*)
    let return_pred_height = Height.of_nat return_pred_context.length in
    let return_pred_height =
      Eq.(cast (Height.morphism return_pred_context.context.eq))
        return_pred_height in
    let return_pred =
      ReturnPred.make ~generalize:generalize_return_pred return_pred
        return_pred_height in
    compile_loop
      { env; tomatches; return_pred; eqns;
        previously_bounds = []; expand_self = false; }
end

let compile_cases ?loc ~(program_mode : bool) (style : Constr.case_style)
  ((typing_fun : compile_cases_typing_fun), sigma)
  (tycon : Evardefine.type_constraint) (env : GlobEnv.t)
    ((predopt : Glob_term.glob_constr option),
      (tomatchl : Glob_term.tomatch_tuples),
      (eqns : Glob_term.cases_clauses)) :
    Evd.evar_map * EConstr.unsafe_judgment =
  let open EvarMapMonad.Ops in
  let env = Eq.cast (Eq.sym GlobalEnv.eq) env in
  let tycon = Option.map (Eq.cast (Eq.sym ETerm.eq)) tycon in
  let judgment_of_glob_constr (type env) ?(tycon : env ETerm.t option)
      (env : env GlobalEnv.t) (constr : Glob_term.glob_constr) :
      (env EJudgment.t) EvarMapMonad.t =
(*
    Format.eprintf "initial return pred: %a in env: %a@." Pp.pp_with
      (Printer.pr_lglob_constr_env (GlobalEnv.env env) sigma constr)
      Pp.pp_with (Env.print (GlobalEnv.env env));
*)
    Eq.cast (EvarMapMonad.eq (Eq.sym EJudgment.eq) Refl)
      (fun sigma ->
        typing_fun (Eq.cast (Eq.option ETerm.eq) tycon)
          (Eq.cast GlobalEnv.eq env) sigma
          constr) in
  let hypnaming = naming_of_program_mode program_mode in
  let infer_return_pred = predopt = None in
  let return_pred return_pred_context =
    let* sigma = EvarMapMonad.get in
    let return_pred_env =
      GlobalEnv.push_rel_context ~hypnaming sigma
        (ERelContext.with_height return_pred_context) env in
    match predopt with
    | Some term ->
        let* s = Evd.new_sort_variable Evd.univ_flexible_alg in
        let* j =
          judgment_of_glob_constr ~tycon:(ETerm.mkSort s) return_pred_env
            term in
        return (EJudgment.uj_val j)
    | None ->
        match tycon with
        | None ->
            let* (ty, _) =
              EvarMapMonad.new_type_evar (GlobalEnv.env return_pred_env)
                Evd.univ_flexible_alg in
            return ty
        | Some tycon ->
            let length = ERelContext.length return_pred_context in
            return (ETerm.lift (Height.of_nat length) tycon) in
  let make_tomatch_tuple (tuple : Glob_term.tomatch_tuple) :
      'env TomatchTuple.t EvarMapMonad.t =
    let open EvarMapMonad.Ops in
    let term, predicate_pattern = tuple in
    let* judgment = judgment_of_glob_constr env term in
    return ({ judgment; predicate_pattern } : 'env TomatchTuple.t) in
  let Exists tomatches = Vector.of_list tomatchl in
  let module V = Vector.UseMonad (Monad.State) in
  let sigma, tomatches =
    EvarMapMonad.run sigma (V.map make_tomatch_tuple tomatches) in
  let Exists eqns = Vector.of_list eqns in
  let make_clause (type tomatch_count) (tomatch_count : tomatch_count Nat.t)
      ({ v = (ids, pats, rhs); loc } : Glob_term.cases_clause) :
      ('env, tomatch_count) Clause.untyped =
    let Exists pats = Pattern.args_of_concrete pats in
    let Refl = Option.get (Nat.is_eq tomatch_count (Pattern.length pats)) in
    let f ({ globenv; return_pred } : _ Rhs.untyped_args) =
(*
      let* sigma = EvarMapMonad.get in
      Format.eprintf "Typing rhs in %a (expected type: %a)." Pp.pp_with
        (Env.print (GlobalEnv.env globenv))
        Pp.pp_with (ETerm.print (GlobalEnv.env globenv) sigma return_pred);
*)
      judgment_of_glob_constr ~tycon:return_pred globenv rhs in
    let desc : _ Clause.desc =
      { env; ids = Names.Id.Set.of_list ids; pats;
        rhs = ({ f } : _ Rhs.untyped_poly)} in
    Exists (CAst.make ?loc desc) in
  let eqns = Vector.map (make_clause (Vector.length tomatches)) eqns in
  let try_with ~small_inversion =
    let module Compiler = struct
      module rec Context : MatchContextS = struct
        let style = style
        let program_mode = program_mode
        let small_inversion = small_inversion
        let compile_loop = Compiler.compile_loop
      end
      and Compiler : CompilerS = Make (Context)
      include Compiler
    end in
    Compiler.compile_cases ~generalize_return_pred:infer_return_pred env
      { f = return_pred } tomatches eqns in
  let sigma, judgment =
    if infer_return_pred then
      try_with ~small_inversion:true sigma
    else
      try
        try_with ~small_inversion:false sigma
      with _ ->
        try_with ~small_inversion:true sigma in
  EvarMapMonad.run sigma begin
(*
    let* sigma = EvarMapMonad.get in
    Format.eprintf "Coerce 3: %a@." Pp.pp_with (EJudgment.print (GlobalEnv.env env) sigma judgment);
*)
    let* judgment =
      EJudgment.inh_conv_coerce_to_tycon ~program_mode (GlobalEnv.env env)
        judgment tycon in
(*
    let* sigma = EvarMapMonad.get in
    Format.eprintf "Coerce 3 done: %a@." Pp.pp_with (EJudgment.print (GlobalEnv.env env) sigma judgment);
*)
(*
    Format.eprintf "%a@." Pp.pp_with (EJudgment.print (GlobalEnv.env env) sigma
      judgment);
    Format.eprintf "%a@." Pp.pp_with (ETerm.debug_print (EJudgment.uj_val judgment));
*)
    let judgment = Eq.cast EJudgment.eq judgment in
    return judgment
  end

let make_return_predicate_ltac_lvar env sigma (na : Names.Name.t)
      (tm : Glob_term.glob_constr) c =
  (* If we have an [x as x return ...] clause and [x] expands to [c],
     we have to update the status of [x] in the substitution:
     - if [c] is a variable [id'], then [x] should now become [id']
     - otherwise, [x] should be hidden *)
  match na, DAst.get tm with
  | Name id, (GVar id' | GRef (VarRef id', _)) when Names.Id.equal id id' ->
     let expansion : Names.Name.t = match EConstr.kind sigma c with
       | Var id' -> Name id'
       | _ -> Anonymous in
       GlobEnv.hide_variable env expansion id
  | _ -> env
