(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module InProg = struct
  type _ t =
    | Ignore : unit t
    | Use : Declare.OblState.t t

  let cast (type a) (x:Declare.OblState.t) (ty:a t) : a =
    match ty with
    | Ignore -> ()
    | Use -> x
end

module OutProg = struct
  type _ t =
    | No : unit t
    | Yes : Declare.OblState.t t
    | Push
    | Pop

  let cast (type a) (x:a) (ty:a t) (orig:Declare.OblState.t NeList.t) : Declare.OblState.t NeList.t  =
    match ty with
    | No -> orig
    | Yes -> NeList.map_head (fun _ -> x) orig
    | Push -> NeList.push Declare.OblState.empty (Some orig)
    | Pop -> (match NeList.tail orig with Some tl -> tl | None -> assert false)
end

module InProof = struct
  type _ t =
    | Ignore : unit t
    | Reject : unit t
    | Use : Declare.Proof.t t
    | UseOpt : Declare.Proof.t option t

  let cast (type a) (x:Declare.Proof.t option) (ty:a t) : a =
    match x, ty with
    | _, Ignore -> ()
    | None, Reject -> ()
    | Some _, Reject -> CErrors.user_err (Pp.str "Command not supported (Open proofs remain).")
    | Some x, Use -> x
    | None, Use -> CErrors.user_err (Pp.str "Command not supported (No proof-editing in progress).")
    | _, UseOpt -> x
end

module OutProof = struct
  type _ t =
    | No : unit t
    | Close : unit t
    | Update : Declare.Proof.t t
    | New : Declare.Proof.t t

end

type ('inprog,'outprog,'inproof,'outproof) vernac_type = {
  inprog : 'inprog InProg.t;
  outprog : 'outprog InProg.t;
  inproof : 'inproof InProof.t;
  outproof : 'outproof OutProof.t;
}

type typed_vernac =
    TypedVernac : {
      inprog : 'inprog InProg.t;
      outprog : 'outprog OutProg.t;
      inproof : 'inproof InProof.t;
      outproof : 'outproof OutProof.t;
      run : pm:'inprog -> proof:'inproof -> 'outprog * 'outproof;
    } -> typed_vernac

let vtdefault f =
  TypedVernac { inprog = Ignore; outprog = No; inproof = Ignore; outproof = No;
                run = (fun ~pm:() ~proof:() ->
                    let () = f () in
                    (), ()) }

let vtnoproof f =
  TypedVernac { inprog = Ignore; outprog = No; inproof = Ignore; outproof = No;
                run = (fun ~pm:() ~proof:() ->
                    let () = f () in
                    (), ())
              }

let vtcloseproof f =
  TypedVernac { inprog = Use; outprog = Yes; inproof = Use; outproof = Close;
                run = (fun ~pm ~proof ->
                    let pm = f ~lemma:proof ~pm in
                    pm, ())
              }

let vtopenproof f =
  TypedVernac { inprog = Ignore; outprog = No; inproof = Ignore; outproof = New;
                run = (fun ~pm:() ~proof:() ->
                    let proof = f () in
                    (), proof)
              }

let vtmodifyproof f =
  TypedVernac { inprog = Ignore; outprog = No; inproof = Use; outproof = Update;
                run = (fun ~pm:() ~proof ->
                    let proof = f ~pstate:proof in
                    (), proof)
              }

let vtreadproofopt f =
  TypedVernac { inprog = Ignore; outprog = No; inproof = UseOpt; outproof = No;
                run = (fun ~pm:() ~proof ->
                    let () = f ~pstate:proof in
                    (), ())
              }

let vtreadproof f =
  TypedVernac { inprog = Ignore; outprog = No; inproof = Use; outproof = No;
                run = (fun ~pm:() ~proof ->
                    let () = f ~pstate:proof in
                    (), ())
              }

let vtreadprogram f =
  TypedVernac { inprog = Use; outprog = No; inproof = Ignore; outproof = No;
                run = (fun ~pm ~proof:() ->
                    let () = f ~pm in
                    (), ())
              }

let vtmodifyprogram f =
  TypedVernac { inprog = Use; outprog = Yes; inproof = Ignore; outproof = No;
                run = (fun ~pm ~proof:() ->
                    let pm = f ~pm in
                    pm, ())
              }

let vtdeclareprogram f =
  TypedVernac { inprog = Use; outprog = No; inproof = Ignore; outproof = New;
                run = (fun ~pm ~proof:() ->
                    let proof = f ~pm in
                    (), proof)
              }

let vtopenproofprogram f =
  TypedVernac { inprog = Use; outprog = Yes; inproof = Ignore; outproof = New;
                run = (fun ~pm ~proof:() ->
                    let pm, proof = f ~pm in
                    pm, proof)
              }
