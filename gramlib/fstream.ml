(* camlp5r *)
(* fstream.ml,v *)
(* Copyright (c) INRIA 2007-2017 *)

exception Cut;

type mlazy_c 'a =
  [ Lfun of unit -> 'a
  | Lval of 'a ]
;
type mlazy 'a =
  [ Cval of 'a
  | Clazy of ref (mlazy_c 'a) ]
;
value mlazy f = Clazy (ref (Lfun f));
value mlazy_force l =
  match l with
  [ Cval v -> v
  | Clazy l ->
      match l.val with
      [ Lfun f -> do { let x = f () in l.val := Lval x; x }
      | Lval v -> v ] ]
;
value mlazy_is_val l =
  match l with
  [ Cval _ -> True
  | Clazy l ->
      match l.val with
      [ Lval _ -> True
      | Lfun _ -> False ] ]
;

type t 'a = { count : int; data : mlazy (data 'a) }
and data 'a =
  [ Nil
  | Cons of 'a and t 'a
  | App of t 'a and t 'a ]
;

value from f =
  loop 0 where rec loop i =
    {count = 0;
     data =
       mlazy
         (fun () ->
            match f i with
            [ Some x -> Cons x (loop (i + 1))
            | None -> Nil ])}
;

value rec next s =
  let count = s.count + 1 in
  match mlazy_force s.data with
  [ Nil -> None
  | Cons a s -> Some (a, {count = count; data = s.data})
  | App s1 s2 ->
      match next s1 with
      [ Some (a, s1) ->
          Some (a, {count = count; data = mlazy (fun () -> App s1 s2)})
      | None ->
          match next s2 with
          [ Some (a, s2) -> Some (a, {count = count; data = s2.data})
          | None -> None ] ] ]
;

value empty s =
  match next s with
  [ Some _ -> None
  | None -> Some ((), s) ]
;

value nil = {count = 0; data = Cval Nil};
value cons a s = Cons a s;
value app s1 s2 = App s1 s2;
value flazy f = {count = 0; data = mlazy f};

value of_list l =
  List.fold_right (fun x s -> flazy (fun () -> cons x s)) l nil
;

value of_string s =
  from (fun c -> if c < String.length s then Some s.[c] else None)
;

value of_channel ic =
  from (fun _ -> try Some (input_char ic) with [ End_of_file -> None ])
;

value iter f =
  do_rec where rec do_rec strm =
    match next strm with
    [ Some (a, strm) ->
        let _ = f a in
        do_rec strm
    | None -> () ]
;

value count s = s.count;

value count_unfrozen s =
  loop 0 s where rec loop cnt s =
    if mlazy_is_val s.data then
      match mlazy_force s.data with
      [ Cons _ s -> loop (cnt + 1) s
      | _ -> cnt ]
    else cnt
;

(* backtracking parsers *)

type kont 'a 'b = [ K of unit -> option ('b * t 'a * kont 'a 'b) ];
type bp 'a 'b = t 'a -> option ('b * t 'a * kont 'a 'b);

value bcontinue = fun [ (K k) -> k () ];

value bparse_all p strm =
  loop (fun () -> p strm) where rec loop p =
    match p () with
    [ Some (r, _, K k) -> [r :: loop k]
    | None -> [] ]
;

value b_seq a b strm =
  let rec app_a kont1 () =
    match kont1 () with
    [ Some (x, strm, K kont1) -> app_b (fun () -> b x strm) kont1 ()
    | None -> None ]
  and app_b kont2 kont1 () =
    match kont2 () with
    [ Some (y, strm, K kont2) -> Some (y, strm, K (app_b kont2 kont1))
    | None -> app_a kont1 () ]
  in
  app_a (fun () -> a strm) ()
;

value b_or a b strm =
  loop (fun () -> a strm) () where rec loop kont () =
    match kont () with
    [ Some (x, strm, K kont) -> Some (x, strm, K (loop kont))
    | None -> b strm ]
;

value b_term f strm =
  match next strm with
  [ Some (x, strm) ->
      match f x with
      [ Some y -> Some (y, strm, K (fun _ -> None))
      | None -> None ]
  | None -> None ]
;

value b_act a strm = Some (a, strm, K (fun _ -> None));
