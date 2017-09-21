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

      Inductive input :=
        Random (_ : random) | ConnectionStart | RecieveNetwork (_ : message).
      Inductive pre_output :=
        RequestRandom | SendNetwork (_ : message) | CloseConnection | UserOutput (_ : secret * public * public).
      Let output := option pre_output.

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
        := nth_message_matching_exists
             1
             (on_output (fun m_out => exists v, m_out = Some (SendNetwork v)))
             trace
           -> holds_of_nth_message_matching
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
        := nth_message_matching_exists
             2
             (on_output (fun m_out => exists v, m_out = Some (SendNetwork v)))
             trace
           -> holds_of_nth_message_matching
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

      (* grep Definition src/Protocols/SigmaKeyExchange/SpecWithSanitization.v | sed s'/Definition//g' | sed s'/^\s*//g' | sed s'|^|/\\\\ |g' | sed s'/\s*$/ trace/g' *)
      Definition trace_satisfies_full_SKE_spec (trace : list (input * output)) : Prop
        := close_connection_closed trace
           /\ get_randomness_spec trace
           /\ output_g_x trace
           /\ must_set_b trace
           /\ must_recieve_b trace
           /\ second_message_correct trace
           /\ second_message_recieved_correct_form trace
           /\ second_message_recieved trace
           /\ output_correct_form trace
           /\ nothing_after_user_output trace.

      Section sanitized.
        Inductive secret_free_input :=
        | SFFreshPublic (_ : public)
        | SFConnectionStart
        | SFRecieveTheirEphemeralPublic (_ : message) (_ : public)
        | SFRecieveTheirLongtermPublic
            (_ : message)
            (their_longterm_public : public)
            (their_ephemeral_public : public)
            (claimed_our_emphemeral_public : public)
        | SFRecieveCorruptedTheirLongtermPublic (_ : message)
        | SFRecieveExtraMessage (_ : message).
        Inductive seal_with := ephemeral | longterm.
        Inductive secret_free_pre_output :=
        | SFRequestRandom
        | SFSendOurEphemeralPublic (_ : public)
        | SFSendNestedBox
            (outer_boxes : list (seal_with * public * (message -> message)))
            (inner_msg : message)
            (inner_seal : seal_with * public)
        | SFCloseConnection
        | SFUserOutputWithOurEphemeralSecret (_ : public * public).

        Inductive RNGState := next_random_is_keypair.
        Inductive ExpectingNextNetworkState :=
          NTheirEphemeralPublic | NTheirLongtermPublic | NOther.

        Definition init_st : RNGState * ExpectingNextNetworkState
          := (next_random_is_keypair, NTheirEphemeralPublic).

        Definition sanitize_input (st_msg : (RNGState * ExpectingNextNetworkState) * input) : (RNGState * ExpectingNextNetworkState) * secret_free_input
          := let '((rng_st, net_st), msg) := st_msg in
             match rng_st, net_st, msg with
             | next_random_is_keypair, _, Random x
               => ((rng_st, net_st), SFFreshPublic (keygen x))
             | _, _, ConnectionStart
               => ((next_random_is_keypair, NTheirEphemeralPublic), SFConnectionStart)
             | _, NTheirEphemeralPublic, RecieveNetwork m
               => ((rng_st, NTheirLongtermPublic), SFRecieveTheirEphemeralPublic m (public_of_text m))
             | _, NTheirLongtermPublic, RecieveNetwork v
               => ((rng_st, NOther),
                   match box_open
                           our_ephemeral_secret
                           their_ephemeral_public
                           (cipher_of_text v)
                   with
                   | Some m
                     => let '(p, c) := pair_of_text m in
                        let their_longterm_public := public_of_text p in
                        match box_open
                                our_ephemeral_secret
                                their_longterm_public
                                (cipher_of_text c)
                        with
                        | Some m'
                          => let '(t, o) := pair_of_text m' in
                             let their_ephemeral_public := public_of_text t in
                             let claimed_our_ephemeral_public := public_of_text o in
                             SFRecieveTheirLongtermPublic
                               v
                               their_longterm_public
                               their_ephemeral_public
                               claimed_our_ephemeral_public
                        | None
                          => SFRecieveCorruptedTheirLongtermPublic v
                        end
                   | None => SFRecieveCorruptedTheirLongtermPublic v
                   end)
             | _, NOther, RecieveNetwork v
               => ((rng_st, net_st), SFRecieveExtraMessage v)
             end.

        Definition enrich_output (msg : secret_free_pre_output) : pre_output
          := match msg with
             | SFRequestRandom => RequestRandom
             | SFSendOurEphemeralPublic v
               => SendNetwork (text_of_public v)
             | SFSendNestedBox outer_boxes inner_msg (inner_seal, inner_pub)
               => let secret_of_seal seal :=
                      match seal with
                      | ephemeral => our_ephemeral_secret
                      | longterm => our_longterm_secret
                      end in
                  let do_seal seal pub msg
                      := text_of_cipher
                           (box_seal
                              (secret_of_seal seal)
                              pub
                              msg) in
                  let m := do_seal inner_seal inner_pub inner_msg in
                  SendNetwork
                    (List.fold_right
                       (fun '(seal, pub, f) msg
                        => do_seal seal pub (f msg))
                       m
                       outer_boxes)
             | SFCloseConnection
               => CloseConnection
             | SFUserOutputWithOurEphemeralSecret (p1, p2)
               => UserOutput (our_ephemeral_secret, p1, p2)
             end.
      End sanitized.
    End per_connection_choices.
  End per_connection_parameters.

  Definition synthesis_goal
    := { state : Type
     & { init : state -> Prop
     & { step : _ (* state -> input -> option pre_output -> state -> Prop *)
     & { state_public : Type
     & { pr_public : state -> state_public
     & { init_public : state_public -> Prop
     & { step_public : _
       | forall trace
                (our_longterm_secret : secret),
           exists (our_ephemeral_secret : secret)
                  (their_ephemeral_public their_longterm_public : public),
             @allows_behavior state input (option pre_output) init step trace
             -> @trace_satisfies_full_SKE_spec our_longterm_secret our_ephemeral_secret their_ephemeral_public their_longterm_public trace
                /\ exists trace_public,
                 @allows_behavior state_public secret_free_input (option secret_free_pre_output) init_public step_public trace_public
                 /\ List.map (fun '(i, o) => option_map (enrich_output our_longterm_secret our_ephemeral_secret) o) trace_public
                    = List.map (fun '(i, o) => o) trace
                 /\ List.map (fun '(i, o) => i) trace_public
                    = list_rect
                        (fun _ => RNGState * ExpectingNextNetworkState
                                  -> list secret_free_input)
                        (fun st => nil)
                        (fun msg_in _ rec st
                         => let '(st, m) := sanitize_input our_ephemeral_secret their_ephemeral_public (st, msg_in) in
                            (m :: rec st)%list)
                        (List.map (fun '(i, o) => i) trace)
                        init_st
                                               } } } } } } }.
End spec.
