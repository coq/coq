Require Import Ltac2.Ltac2.

Import Ltac2.Control.

(** Alternative implementation of the hyp primitive *)
Ltac2 get_hyp_by_name x :=
  let h := hyps () in
  let rec find x l := match l with
  | [] => zero Not_found
  | p :: l =>
    match p with
    | (id, _, t) =>
      match Ident.equal x id with
      | true => t
      | false => find x l
      end
    end
  end in
  find x h.

Print Ltac2 get_hyp_by_name.

Goal forall n m, n + m = 0 -> n = 0.
Proof.
refine (fun () => '(fun n m H => _)).
let t := get_hyp_by_name @H in Message.print (Message.of_constr t).
Abort.
