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

      (* TODO: MOVE ME *)
      Fixpoint holds_of_messages_around_nth_message_matching_aux
               (n : nat)
               {T}
               (matcher : T -> Prop)
               (property : list T -> T -> list T -> Prop)
               (pre_trace : list T)
               (trace : list T)
        : Prop
        := match trace with
           | nil => True
           | m :: ms
             => (matcher m ->
                 match n with
                 | 0 => property pre_trace m ms
                 | S n'
                   => holds_of_messages_around_nth_message_matching_aux
                        n'
                        matcher
                        property
                        (pre_trace ++ m::nil)
                        ms
                 end)
                /\ (~matcher m
                    -> holds_of_messages_around_nth_message_matching_aux
                         n
                         matcher property (pre_trace ++ (m::nil)) ms)
           end%list.
      Fixpoint holds_of_messages_around_nth_message_matching
               (n : nat)
               {T}
               (matcher : T -> Prop)
               (property : list T -> T -> list T -> Prop)
               (trace : list T)
        : Prop
        := holds_of_messages_around_nth_message_matching_aux
             n matcher property nil trace.
      Definition holds_of_messages_before_nth_message_matching
                 (n : nat)
                 {T}
                 (matcher : T -> Prop)
                 (property : list T -> T -> Prop)
                 (trace : list T)
        : Prop
        := holds_of_messages_around_nth_message_matching
             n matcher (fun before m after => property before m) trace.
      Definition holds_of_nth_message_matching
                 (n : nat)
                 {T}
                 (matcher : T -> Prop)
                 (property : T -> Prop)
                 (trace : list T)
        : Prop
        := holds_of_messages_around_nth_message_matching
             n matcher (fun _ m _=> property m) trace.
      Definition holds_of_messages_after_nth_message_matching
                 (n : nat)
                 {T}
                 (matcher : T -> Prop)
                 (property : T -> list T -> Prop)
                 (trace : list T)
        : Prop
        := holds_of_messages_around_nth_message_matching
             n matcher (fun before m after => property m after) trace.

      (* Constraint: we don't send anything after CloseConnection *)
      Definition close_connection_closed
                 (trace : list (input * output)) : Prop
        := holds_of_messages_after_nth_message_matching
             0
             (fun '(m_in, m_out) => m_out = Some CloseConnection)
             (fun _ after
              => List.Forall
                   (fun '(m_in, m_out) => m_out = None)
                   after)
             trace.

      (* Constraint: if there's a first message on the wire from our
          side, then there must be a message from the RNG before that
          which gives x *)
      Definition get_randomness_spec
                 (trace : list (input * output)) : Prop
        := holds_of_messages_before_nth_message_matching
             0
             (fun '(m_in, m_out) => exists v, m_out = Some (SendNetwork v))
             (fun pre_trace m
              => List.Exists (fun '(m_in, m_out)
                              => m_in = Random our_ephemeral_secret)
                             (pre_trace ++ (m::nil)))
             trace.

      Let Send_a := Some (SendNetwork (text_of_public our_ephemeral_public)).

      (* Constraint: if there's a first message on the wire from our
          side, it must be g^x *)
      Definition output_g_x
                 (trace : list (input * output)) : Prop
        := holds_of_nth_message_matching
             0
             (fun '(m_in, m_out)
              => exists v, m_out = Some (SendNetwork v))
             (fun '(m_in, m_out)
              => m_out = Send_a)
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
             (fun '(m_in, m_out) => exists v, m_in = RecieveNetwork v)
             (fun '(m_in, m_out) => m_in = RecieveNetwork (text_of_public their_ephemeral_public))
             trace.
      Definition must_recieve_b
                 (trace : list (input * output)) : Prop
        := holds_of_messages_around_nth_message_matching
             1
             (fun '(m_in, m_out) => exists v, m_out = Some (SendNetwork v))
             (fun before m after
              => List.Exists
                   (fun '(m_in, m_out) => m_in = RecieveNetwork (text_of_public their_ephemeral_public))
                   before)
             trace.

      (* Constraint: the form of our second message must be correct *)
      (* //--> [A,[a,b](A<>b)](a<>b) *)
      Definition second_message_correct
                 (trace : list (input * output)) : Prop
        := holds_of_nth_message_matching
             1
             (fun '(m_in, m_out) => exists v, m_out = Some (SendNetwork v))
             (fun '(m_in, m_out)
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
                                           text_of_public their_ephemeral_public)))))))))
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
             (fun '(m_in, m_out) => exists v, m_in = RecieveNetwork v)
             (fun '(m_in, m_out)
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
                                   text_of_public our_ephemeral_public)))
             trace.
      (* Also spec output here *)
      Definition second_message_recieved
                 (trace : list (input * output)) : Prop
        := holds_of_messages_before_nth_message_matching
             0
             (fun '(m_in, m_out) => exists v, m_out = Some (UserOutput v))
             (fun before _
              => List.Exists
                   (fun '(m_in, m_out)
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
                                         text_of_public our_ephemeral_public)))
                   before)
             trace.
      Definition output_correct_form
                 (trace : list (input * output)) : Prop
        := holds_of_nth_message_matching
             0
             (fun '(m_in, m_out) => exists v, m_out = Some (UserOutput v))
             (fun '(m_in, m_out)
              => m_out
                 = Some
                     (UserOutput
                        (our_ephemeral_secret,
                         their_ephemeral_public,
                         their_longterm_public)))
             trace.
      Definition nothing_after_user_output
                 (trace : list (input * output)) : Prop
        := holds_of_messages_after_nth_message_matching
             0
             (fun '(m_in, m_out) => exists v, m_out = Some (UserOutput v))
             (fun _ after
              => List.Forall
                   (fun '(m_in, m_out) => m_out = None)
                   after)
             trace.


(* Secrets constraint: If you recieve a randomness message, you may
immediately emit [g^x] and update the secret-x-value with [x], or you
may do anything which does not depend on the contents of the random
message.  (the decision must depend only on public things) *)
(* Secrets constraint: You may at any time emit a message matching
long-form or short-form using the secret-x-value in the appropriate
place and not in other places, or else you must emit somthing not
depending on the secret-x-value (the decision must depend only on
public things) *)
