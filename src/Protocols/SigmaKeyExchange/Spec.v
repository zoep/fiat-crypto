Require Import Crypto.Spec.Trace.
(**
// All single-letter symbols in this comment represent public DH keys.
// Capital letters represent long-term and others are per-connection
// ephemeral. [msg](PK1<>PK2) denotes nacl/box authenticated encryption.
//--> a
//<-- b
//<-- [B,[b,a](B<>a)](a<>b)
//--> [A,[a,b](A<>b)](a<>b)
//--> [data](a<>b)
//<-- [data](a<>b)
*)

(* Parameter: g *)
(* Per-connection parameter: A *)
(* Per-connection choice: x *)
(* Per-connection choice: b *)
(* Per-connection choice: B *)
(* Constraint: if there's a first message on the wire from our side,
then there must be a message from the RNG before that which gives x *)
(* Constraint: if there's a first message on the wire from our side, it
must be g^x *)
(* Constraint: if you recieve more than just [b] before you send [a],
must abort *)
(* Constraint: if you send a non-abort message after sending [a], you
must have recieved [b] (and it must match the choice of [b]) *)
(* Constraint: if you send a non-abort message after sending [a] and
"the long message", you must have recieved a long message, and it must
be the message you got immediately after the short message, and it
must match the choice of [B], and the format must be correct *)

Section spec.
  Context (connection_id : Type)
          (secret public : Type)
          (message ciphertext : Type)
          (text_of_pair : message * message -> message)
          (text_of_public : public -> message)
          (text_of_cipher : ciphertext -> message)
          (pair_of_text : message -> message * message)
          (public_of_text : message -> public)
          (cipher_of_text : message -> ciphertext).
  Let random := secret.
  Context (keygen : secret -> public) (* Parameter: g *)
          (box_seal : secret -> public -> message -> ciphertext)
          (box_open : secret -> public -> ciphertext -> option message).

  Section per_connection_parameters.
    Context (our_longterm_public : public) (* Per-connection parameter: A *)
            (our_longterm_secret : secret).
    Section per_connection_choices.
      Context (our_ephemeral_secret : secret) (* Per-connection choice: x *)
              (their_ephemeral_public : public) (* Per-connection choice: b *)
              (their_longterm_public : public) (* Per-connection choice: B *).

      Context {state : Type}.

      Inductive input :=
        Random (_ : random) | ConnectionStart | RecieveNetwork (_ : message).
      Inductive pre_output :=
        RequestRandom | SendNetwork (_ : message).
      Let output := option pre_output.
      Context (init : state -> Prop)
              (step : state -> input -> output -> state -> Prop).

      (* Constraint: if there's a first message on the wire from our
          side, then there must be a message from the RNG before that
          which gives x *)
      Definition get_randomness_spec
                 (trace : list (connection_id * input * output)) : Prop
        :=

(* Constraint: if there's a first message on the wire from our side, it
must be g^x *)
(* Constraint: if you recieve more than just [b] before you send [a],
must abort *)
(* Constraint: if you send a non-abort message after sending [a], you
must have recieved [b] (and it must match the choice of [b]) *)
(* Constraint: if you send a non-abort message after sending [a] and
"the long message", you must have recieved a long message, and it must
be the message you got immediately after the short message, and it
must match the choice of [B], and the format must be correct *)
