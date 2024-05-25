Inductive boring1 := Boring1.
Inductive boring2 := Boring2.

Inductive output_wrapper := OutputWrapper {
    ow_alice : boring1;
}.

#[projections(primitive)]
Inductive request := InputWrapper {
    req_alice : boring1;
    req_next_bob := Boring2;
}.

Definition do_the_thing (req : request) : output_wrapper.
Proof.
  exact (
      match req with
      | {|
          req_alice := alice;
       |} =>
        OutputWrapper alice
      end
  ).
  Validate Proof.
Qed.
