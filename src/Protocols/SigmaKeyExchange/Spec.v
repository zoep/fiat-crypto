Require Import Crypto.Spec.Trace.
Require Import Crypto.Protocols.SigmaKeyExchange.Combinators.
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
(* Constraint: the form of our second message must be correct *)
(* Constraint: if you send a non-abort message after sending [a] and
"the long message", you must have recieved a long message, and it must
be the message you got immediately after the short message, and it
must match the choice of [B], and the format must be correct *)

(* Secrets constraint: If you recieve a randomness message, you may
immediately emit [g^x] and update the secret-x-value with [x], or you
may do anything which does not depend on the contents of the random
message.  (the decision must depend only on public things) *)
(* Secrets constraint: You may at any time emit a message matching
long-form or short-form using the secret-x-value in the appropriate
place and not in other places, or else you must emit somthing not
depending on the secret-x-value (the decision must depend only on
public things) *)

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
    Context (our_longterm_secret : secret).
    Let our_longterm_public : public (* Per-connection parameter: A *)
      := keygen our_longterm_secret.
    Section per_connection_choices.
      Context (our_ephemeral_secret : secret) (* Per-connection choice: x *)
              (their_ephemeral_public : public) (* Per-connection choice: b *)
              (their_longterm_public : public) (* Per-connection choice: B *).
      Let our_ephemeral_public : public
        := keygen our_ephemeral_secret.

      Context {state : Type}.

      Inductive input :=
        Random (_ : random) | ConnectionStart | RecieveNetwork (_ : message).
      Inductive pre_output :=
        RequestRandom | SendNetwork (_ : message) | CloseConnection | UserOutput (_ : secret * public * public).
      Let output := option pre_output.
      Context (init : state -> Prop)
              (step : state -> input -> output -> state -> Prop).

      (* Constraint: we don't send anything after CloseConnection *)
      Definition close_connection_closed
                 (trace : list (input * output)) : Prop
        := holds_of_all_messages_strictly_after_nth_message_matching
             0
             (on_output (fun m_out => m_out = Some CloseConnection))
             (fun _ => on_output (fun m_out => m_out = None))
             trace.

      (* Constraint: if there's a first message on the wire from our
          side, then there must be a message from the RNG before that
          which gives x *)
      Definition get_randomness_spec
                 (trace : list (input * output)) : Prop
        := holds_of_some_message_before_nth_message_matching
             0
             (on_output (fun m_out => exists v, m_out = Some (SendNetwork v)))
             (fun _ => on_input (fun m_in => m_in = Random our_ephemeral_secret))
             trace.

      Let Send_a := Some (SendNetwork (text_of_public our_ephemeral_public)).

      (* Constraint: if there's a first message on the wire from our
          side, it must be g^x *)
      Definition output_g_x
                 (trace : list (input * output)) : Prop
        := holds_of_nth_message_matching
             0
             (on_output (fun m_out => exists v, m_out = Some (SendNetwork v)))
             (on_output (fun m_out => m_out = Send_a))
             trace.

      (* Constraint: if you recieve more than just [b] before you send
          [a], must abort *)
      (* Skipped for now *)

      (* Constraint: if you send a non-abort message after sending
          [a], you must have recieved [b] (and it must match the
          choice of [b]) *)
      Definition must_set_b
                 (trace : list (input * output)) : Prop
        := holds_of_nth_message_matching
             0
             (on_input (fun m_in => exists v, m_in = RecieveNetwork v))
             (on_input (fun m_in => m_in = RecieveNetwork (text_of_public their_ephemeral_public)))
             trace.
      Definition must_recieve_b
                 (trace : list (input * output)) : Prop
        := holds_of_some_message_strictly_before_nth_message_matching
             1
             (on_output (fun m_out => exists v, m_out = Some (SendNetwork v)))
             (fun _ => on_input (fun m_in => m_in = RecieveNetwork (text_of_public their_ephemeral_public)))
             trace.

      (* Constraint: the form of our second message must be correct *)
      (* //--> [A,[a,b](A<>b)](a<>b) *)
      Definition second_message_correct
                 (trace : list (input * output)) : Prop
        := holds_of_nth_message_matching
             1
             (on_output (fun m_out => exists v, m_out = Some (SendNetwork v)))
             (on_output
                (fun m_out
                 => m_out
                    = Some
                        (SendNetwork
                           (text_of_cipher
                              (box_seal
                                 our_ephemeral_secret
                                 their_ephemeral_public
                                 (text_of_pair
                                    (text_of_public our_longterm_public,
                                     text_of_cipher
                                       (box_seal
                                          our_longterm_secret
                                          their_ephemeral_public
                                          (text_of_pair
                                             (text_of_public our_ephemeral_public,
                                              text_of_public their_ephemeral_public))))))))))
             trace.

      (* Constraint: if you send a non-abort message after sending [a]
          and "the long message", you must have recieved a long
          message, and it must be the message you got immediately
          after the short message, and it must match the choice of
          [B], and the format must be correct *)
      (* //<-- [B,[b,a](B<>a)](a<>b) *)
      Definition second_message_recieved_correct_form
                 (trace : list (input * output)) : Prop
        := holds_of_nth_message_matching
             1
             (on_input (fun m_in => exists v, m_in = RecieveNetwork v))
             (on_input
                (fun m_in
                 => forall v boxed_b_a,
                     m_in = RecieveNetwork v
                     -> box_open
                          our_ephemeral_secret
                          their_ephemeral_public
                          (cipher_of_text v)
                        = Some (text_of_pair
                                  (text_of_public their_longterm_public,
                                   text_of_cipher boxed_b_a))
                        /\ box_open
                             our_ephemeral_secret
                             their_longterm_public
                             boxed_b_a
                           = Some (text_of_pair
                                     (text_of_public their_ephemeral_public,
                                      text_of_public our_ephemeral_public))))
             trace.
      (* Also spec output here *)
      Definition second_message_recieved
                 (trace : list (input * output)) : Prop
        := holds_of_some_message_strictly_before_nth_message_matching
             0
             (on_output (fun m_out => exists v, m_out = Some (UserOutput v)))
             (fun _
              => on_input
                   (fun m_in
                    => forall v boxed_b_a,
                        m_in = RecieveNetwork v
                        -> box_open
                             our_ephemeral_secret
                             their_ephemeral_public
                             (cipher_of_text v)
                           = Some (text_of_pair
                                     (text_of_public their_longterm_public,
                                      text_of_cipher boxed_b_a))
                           /\ box_open
                                our_ephemeral_secret
                                their_longterm_public
                                boxed_b_a
                              = Some (text_of_pair
                                        (text_of_public their_ephemeral_public,
                                         text_of_public our_ephemeral_public))))
             trace.
      Definition output_correct_form
                 (trace : list (input * output)) : Prop
        := holds_of_nth_message_matching
             0
             (on_output (fun m_out => exists v, m_out = Some (UserOutput v)))
             (on_output
                (fun m_out
                 => m_out
                    = Some
                        (UserOutput
                           (our_ephemeral_secret,
                            their_ephemeral_public,
                            their_longterm_public))))
             trace.
      Definition nothing_after_user_output
                 (trace : list (input * output)) : Prop
        := holds_of_all_messages_strictly_after_nth_message_matching
             0
             (on_output (fun m_out => exists v, m_out = Some (UserOutput v)))
             (fun _ => on_output (fun m_out => m_out = None))
             trace.

      Section stateful.
        Let secret_x_value_type := random.
        Let longterm_secret_type := secret.
        Context (public_state_type : Type)
                (project_secret_x_value : state -> option secret_x_value_type)
                (project_public : state -> public_state_type)
                (project_longterm_secret : state -> option longterm_secret_type).

        (* Secrets constraint: If you recieve a randomness message,
            you may immediately emit [g^x] and update the
            secret-x-value with [x], or you may do anything which does
            not depend on the contents of the random message.  (the
            decision must depend only on public things) *)
        Definition on_recieve_random
                   (step : input * state -> output * state)
          : Prop
          := forall st : input * state,
            let '(m_out, st') := step st in
            let '(m_in, st) := st in
            exists (decide_emit_g_x : public_state_type -> bool)
                   (update_public_on_emit_g_x : public_state_type -> public -> public_state_type)
                   (emit_on_not_g_x : public_state_type -> output)
                   (update_public_on_not_emit_g_x : public_state_type -> public_state_type),
              forall v,
                m_in = Random v
                -> if decide_emit_g_x (project_public st)
                   then (m_out
                         = Some
                             (SendNetwork (text_of_public (keygen v)))
                         /\ project_secret_x_value st' = Some v
                         /\ project_longterm_secret st' = project_longterm_secret st
                         /\ project_public st' = update_public_on_emit_g_x (project_public st) (keygen v))
                   else (m_out = emit_on_not_g_x (project_public st)
                         /\ project_secret_x_value st' = project_secret_x_value st
                         /\ project_longterm_secret st' = project_longterm_secret st
                         /\ project_public st' = update_public_on_not_emit_g_x (project_public st)).

        (* Secrets constraint: You may at any time emit a message
            matching long-form using the secret-x-value in the
            appropriate place and not in other places, or else you
            must emit somthing not depending on the secret-x-value
            except through whether or not box_open succeeds *)
        Definition only_use_secret_x
                   (step : input * state -> output * state)
          : Prop
          := forall st : input * state,
            let '(m_out, st') := step st in
            let '(m_in, st) := st in
            exists (decide_emit_long : input * public_state_type -> bool)
                   (emit_long : input -> public_state_type -> secret_x_value_type -> longterm_secret_type -> message)
                   (emit_non_long : public_state_type
                                    -> input
                                    -> (public -> ciphertext -> bool (* unseal was called and also succeeds *))
                                    -> output)
                   (update_public : public_state_type
                                    -> output
                                    -> (public -> ciphertext -> bool (* unseal was called and also succeeds *))
                                    -> public_state_type)
                   (update_secret_x_value : option secret_x_value_type -> input -> option secret_x_value_type),
              if decide_emit_long (m_in, project_public st)
              then (exists our_ephemeral_secret (out_longterm_secret : longterm_secret_type),
                       project_secret_x_value st = Some our_ephemeral_secret
                       /\ project_longterm_secret st = Some our_longterm_secret
                       /\ let our_ephemeral_public := keygen our_ephemeral_secret in
                         (m_out
                          = Some
                              (SendNetwork (emit_long m_in (project_public st) our_ephemeral_secret our_longterm_secret)))
                         /\ project_public st' = update_public (project_public st) m_out (fun _ _ => false)
                         /\ project_secret_x_value st' = project_secret_x_value st
                         /\ project_longterm_secret st' = project_longterm_secret st)
              else (let decide_unseal
                        := (fun p c
                            => match project_secret_x_value st with
                               | Some our_ephemeral_secret
                                 => match box_open our_ephemeral_secret p c with
                                    | Some _ => true
                                    | None => false
                                    end
                               | None => false
                               end) in
                    m_out = emit_non_long (project_public st) m_in decide_unseal
                    /\ project_public st' = update_public (project_public st) m_out decide_unseal
                    /\ project_secret_x_value st' = update_secret_x_value (project_secret_x_value st) m_in
                    /\ project_longterm_secret st' = project_longterm_secret st).
