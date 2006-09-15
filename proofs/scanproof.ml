
type result =
    Okay
  | Wrong_num_gg of Proof_type.goal list
  | Tac_failure of exn
  | Cancelled

type info = {
    goal_num : int;
    num_gg : int;
    cool : Proof_type.tactic;
    mutable res : result
}

(* Raised when a tactic created in the new proof a different
   number of goals than in the old one.
   old number * new number *)
exception Tactic_diverged of int * int

(* Boolean list to know whether each current subgoal was kept.
   If it is shorter than the number of current subgoals, all the
   last ones were kept. *)
let kept = ref []

let reset () =
  kept := []

(* If some goals of the old proof at the same state
   have been discarded in the new one, the indices
   of the remaining ones are changed. This function
   returns the new indoex of a goal if it is still
   here, -1 otherwise. *)
let get_new_num n =
  let rec aux m n = function
      [] -> n
    | true::q -> if m=1 then n
                 else aux (pred m) n q
    | false::q -> if m=1 then -1
                  else aux (pred m) (pred n) q
  in aux n n !kept

let discarding goal_num num_gg =
  let rec aux goal_num num_gg = function
      [] when num_gg = 0 -> []
    | [] when goal_num = 1 -> false::(aux 1 (pred num_gg) [])
    | [] -> true::(aux (pred goal_num) num_gg [])
    | a::q when goal_num > 1 -> a::(aux (pred goal_num) num_gg q)
    | a::q when num_gg = 0 -> q
    | l -> false::(aux 1 (pred num_gg) l)
  in kept := aux goal_num num_gg !kept

let keeping goal_num num_gg =
  let rec aux goal_num num_gg = function
      [] -> []
    | a::q when goal_num > 1 -> a::(aux (pred goal_num) num_gg q)
    | a::q when num_gg = 0 -> q
    | l -> true::(aux 1 (pred num_gg) l)
  in kept:= aux goal_num num_gg !kept

let is_discarded n =
  let rec aux n = function
      [] -> false
    | a::q ->
	if n=1 then not a
	else aux (pred n) q
  in
  let res = aux n !kept
  in assert (not res); res

