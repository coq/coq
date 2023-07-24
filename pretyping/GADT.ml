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

(*
    let get : type state . (state, state) t =
      fun state -> M.Ops.return (state, state)
*)

(*
    let set : type state . state -> (unit, state) t =
      fun new_state state -> M.Ops.return (new_state, ())
*)

    let use : type state . (state -> 'a) -> ('a, state) t =
      fun f state -> M.Ops.return (state, f state)

    let update : type state . (state -> state) -> (unit, state) t =
      fun f state -> M.Ops.return (f state, ())
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

  type univ_instance

  type rel_declaration = (t, t) Context.Rel.Declaration.pt

  type rel_context = (t, t) Context.Rel.pt

  val exliftn : Esubst.lift -> t -> t

  val mkRel : int -> t

  val mkProp : t

  val mkIndU : Names.inductive * univ_instance -> t

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

  val mkIndU : 'ind InductiveDef.t * Concrete.univ_instance -> 'env t

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

  let mkIndU ((ind : 'ind InductiveDef.t), (instance : X.univ_instance)) : 'env t =
    Eq.cast (Eq.sym (Eq.((InductiveDef.eq ^* Eq.Refl) ^-> eq))) X.mkIndU (ind, instance)

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
    type univ_instance = Univ.Instance.t

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
