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
      | Random (_ : random) | ConnectionStart | RecieveNetwork (_ : message)
      | APISendNetwork | APICloseConnection | APIUserOutput.

      Inductive pre_output :=
      | RequestRandom | SendNetwork (_ : message) | CloseConnection | UserOutput (_ : secret * public * public)
      | APIGotRandom | APIGotConnectionStart
      | APIGotTheirEphemeralPublic (_ : message) (_ : public)
      | APIGotTheirLongtermPublicAndPassedValidation (_ : message) (_ : public)
      | APIGotTheirLongformFailedValidation (_ : message)
      | APIGotRecieveNetworkGeneric (_ : message).
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

      Let longform
        := (text_of_cipher
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
                              text_of_public their_ephemeral_public))))))).

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
                           longform)))
             trace.

      Let input_passes_validation m_in
        := (forall v boxed_b_a,
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
                                text_of_public our_ephemeral_public))).

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
             (fun _ => on_input input_passes_validation)
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

      Definition trace_satisfies_external_SKE_spec (trace : list (input * output)) : Prop
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
      Section secrets.
        Definition on_input_Random
                   (trace : list (input * output)) : Prop
          := holds_of_all_messages
               (fun '(m_in, m_out)
                => (exists v, m_in = Random v)
                   <-> m_out = Some APIGotRandom)
               trace.
        Definition on_input_ConnectionStart
                   (trace : list (input * output)) : Prop
          := holds_of_all_messages
               (fun '(m_in, m_out)
                => m_in = ConnectionStart
                   <-> m_out = Some APIGotConnectionStart)
               trace.
        Definition on_output_CloseConnection
                   (trace : list (input * output)) : Prop
          := holds_of_all_messages
               (fun '(m_in, m_out)
                => m_in = APICloseConnection
                   <-> m_out = Some CloseConnection)
               trace.
        Definition on_output_UserOutput
                   (trace : list (input * output)) : Prop
          := holds_of_all_messages
               (fun '(m_in, m_out)
                => m_in = APIUserOutput
                   <-> (exists v, m_out = Some (UserOutput v)))
               trace.
        Definition on_output_SendNetwork
                   (trace : list (input * output)) : Prop
          := holds_of_all_messages
               (fun '(m_in, m_out)
                => m_in = APISendNetwork
                   <-> (exists v, m_out = Some (SendNetwork v)))
               trace.
        Definition on_input_RecieveNetwork
                   (trace : list (input * output)) : Prop
          := holds_of_all_messages
               (fun '(m_in, m_out)
                => (exists v, m_in = RecieveNetwork v)
                   <-> match m_in, m_out with
                       | RecieveNetwork v, Some (APIGotTheirEphemeralPublic v' _)
                       | RecieveNetwork v, Some (APIGotTheirLongtermPublicAndPassedValidation v' _)
                       | RecieveNetwork v, Some (APIGotTheirLongformFailedValidation v')
                       | RecieveNetwork v, Some (APIGotRecieveNetworkGeneric v')
                         => v = v'
                       | _, _ => False
                       end)
               trace.
        Definition on_input_RecieveNetwork0
                   (trace : list (input * output)) : Prop
          := holds_of_nth_message_matching
               0
               (on_input (fun m_in => exists v, m_in = RecieveNetwork v))
               (fun '(m_in, m_out)
                => exists v,
                    m_in = RecieveNetwork v
                    /\ m_out = Some (APIGotTheirEphemeralPublic v (public_of_text v)))
               trace.
        Definition on_input_RecieveNetwork1
                   (trace : list (input * output)) : Prop
          := holds_of_nth_message_matching
               1
               (on_input (fun m_in => exists v, m_in = RecieveNetwork v))
               (fun '(m_in, m_out)
                => exists v,
                    m_in = RecieveNetwork v
                    /\ m_out = Some (APIGotTheirEphemeralPublic v (public_of_text v)))
               trace.
        Definition on_input_RecieveNetwork2
                   (trace : list (input * output)) : Prop
          := holds_of_nth_message_matching
               2
               (on_input (fun m_in => exists v, m_in = RecieveNetwork v))
               (fun '(m_in, m_out)
                => exists v,
                    m_in = RecieveNetwork v
                    /\ ((input_passes_validation m_in
                         /\ m_out = Some (APIGotTheirLongtermPublicAndPassedValidation v their_longterm_public))
                        \/ (~input_passes_validation m_in
                            /\ m_out = Some (APIGotTheirLongformFailedValidation v))))
               trace.
        Definition on_input_RecieveNetworkGe3
                   (trace : list (input * output)) : Prop
          := holds_of_nth_messages_matching_if_they_exist
               (fun n => n > 2)
               (on_input (fun m_in => exists v, m_in = RecieveNetwork v))
               (fun '(m_in, m_out)
                => exists v,
                    m_in = RecieveNetwork v /\ m_out = Some (APIGotRecieveNetworkGeneric v))
               trace.

        Definition trace_satisfies_full_SKE_spec (trace : list (input * output)) : Prop
          := trace_satisfies_external_SKE_spec trace
             /\ on_input_Random trace
             /\ on_input_ConnectionStart trace
             /\ on_output_CloseConnection trace
             /\ on_output_UserOutput trace
             /\ on_output_SendNetwork trace
             /\ on_input_RecieveNetwork trace
             /\ on_input_RecieveNetwork0 trace
             /\ on_input_RecieveNetwork1 trace
             /\ on_input_RecieveNetwork2 trace
             /\ on_input_RecieveNetworkGe3 trace.
      End secrets.

      Definition at_most_one {T} (P : T -> Prop)
        := forall x y : T, P x -> P y -> x = y.

      Definition is_deterministicT
        := forall (partial_trace : list (input * output))
                  (m_in : input),
          at_most_one
            (fun m_out
             => (exists rest : list (input * output),
                    trace_satisfies_full_SKE_spec (partial_trace ++ (m_in, m_out)::rest))).

      Require Import Crypto.Util.Tactics.DestructHead.
      Require Import Crypto.Util.Tactics.Test.
      Require Import Crypto.Util.Option.
      Lemma pull_ex_not {T} (P : T -> Prop)
        : (~ex P) <-> forall v, ~P v.
      Proof.
        split; intros H; [ intros v H' | intros [v H'] ];
          eapply H; [ eexists | ]; eassumption.
      Qed.
      Lemma impl_and_l {A B C : Prop} : (A /\ B -> C) <-> (A -> B -> C).
      Proof. tauto. Qed.
      Lemma holds_of_messages_around_nth_messages_matching_aux_lift_impl
            is_n
            (P1 P2 : Prop)
            (HP : P1 -> P2)
            T
            (matcher : _ -> Prop)
            (property1 property2 : _ -> _ -> _ -> Prop)
            init1 init2
            (Hproperty : forall pre m post, matcher m -> property1 (init1 ++ pre)%list m post -> property2 (init2 ++ pre)%list m post)
            trace
        : @holds_of_messages_around_nth_messages_matching_aux is_n P1 T matcher property1 init1 trace
          -> @holds_of_messages_around_nth_messages_matching_aux is_n P2 T matcher property2 init2 trace.
      Proof.
        clear -Hproperty HP.
        revert P1 P2 HP is_n init1 init2 Hproperty; induction trace as [|x xs IHxs]; intros P1 P2 HP is_n init1 init2 Hproperty; simpl.
        { assumption. }
        { pose proof (Hproperty nil).
          assert (Hp' : forall pre m post,
                     matcher m
                     -> property1 ((init1 ++ x::nil) ++ pre)%list m post
                     -> property2 ((init2 ++ x::nil) ++ pre)%list m post)
            by (intros ???; rewrite <- !List.app_assoc; apply Hproperty).
          repeat first [ progress simpl @List.app in *
                       | progress rewrite !List.app_nil_r in *
                       | apply conj
                       | intro
                       | assumption
                       | progress destruct_head'_and
                       | match goal with
                         | [ H : ?A -> ?B, H' : ?A |- _ ] => specialize (H H')
                         end
                       | solve [ eauto ] ].
          { eapply IHxs; [ .. | eassumption ]; [ tauto | eauto ]. } }
      Qed.
      Lemma holds_of_all_messages_cons {T} P x xs
        : @holds_of_all_messages T P (x :: xs)
          <-> (P x /\ @holds_of_all_messages T P xs).
      Proof.
        clear.
        repeat autounfold with trace_combinators; simpl.
        repeat first [ apply conj
                     | intro
                     | assumption
                     | progress destruct_head'_and
                     | match goal with
                       | [ H : True -> _ |- _ ] => specialize (H I)
                       | [ H : ~True -> _ |- _ ] => clear H
                       end
                     | solve [ eauto ]
                     | eapply holds_of_messages_around_nth_messages_matching_aux_lift_impl; [.. | eassumption ] ].
      Qed.
      Lemma holds_of_all_messages_app {T} P ls1 ls2
        : @holds_of_all_messages T P (ls1 ++ ls2)
          <-> (@holds_of_all_messages T P ls1 /\ @holds_of_all_messages T P ls2).
      Proof.
        clear.
        revert ls2; induction ls1 as [|x xs IHxs]; intro ls2.
        { repeat autounfold with trace_combinators; simpl; tauto. }
        { simpl; rewrite !holds_of_all_messages_cons, IHxs; tauto. }
      Qed.
      Lemma is_deterministic : is_deterministicT.
      Proof.
        intros partial_trace m_in x y [restx Hx] [resty Hy].
        unfold trace_satisfies_full_SKE_spec in *.
        unfold on_input_Random, on_input_ConnectionStart, on_output_CloseConnection, on_output_SendNetwork, on_output_UserOutput in *.
        (*destruct_head'_and
        , trace_satisfies_external_SKE_spec in *.*)
        Local Ltac do_unfold :=
          repeat first [ progress simpl @List.app in *
                       | match goal with
                         | [ H : context[?f _ /\ _] |- _ ]
                           => lazymatch type of f with
                              | list _ -> _ => unfold f in H
                              end
                         | [ H : context[_ /\ ?f _] |- _ ]
                           => lazymatch type of f with
                              | list _ -> _ => unfold f in H
                              end
                         | [ H : context[~(exists v : ?T, ?m = @?k v) -> _] |- _ ]
                           => rewrite (@pull_ex_not T (fun v => m = k v)) in H
                         | [ H : context[(?A /\ ?B) -> ?C] |- _ ]
                           => rewrite (@impl_and_l A B C) in H
                         end
                       | progress destruct_head'_and
                       | progress destruct_head'_prod
                       | progress repeat autounfold with trace_combinators in *
                       | progress simpl in *
                       | progress unfold Send_a in * ].
        Local Ltac do_solve :=
          repeat match goal with
                 | [ H : True -> _ |- _ ] => specialize (H I)
                 | [ H : False |- _ ] => exfalso; exact H
                 | [ |- ?x = ?x ] => reflexivity
                 | _ => progress destruct_head'_and
                 | _ => progress destruct_head'_ex
                 | _ => progress destruct_head' iff
                 | _ => progress subst
                 | [ H : RecieveNetwork _ = RecieveNetwork _ |- _ ]
                   => inversion H; clear H
                 | [ H : SendNetwork _ = SendNetwork _ |- _ ]
                   => inversion H; clear H
                 | [ H : Some _ = Some _ |- _ ]
                   => inversion H; clear H
                 | [ H : (exists v, _ = _) -> _ |- _ ]
                   => specialize (H (ex_intro _ _ eq_refl))
                 | [ H : _ = _ -> _ |- _ ]
                   => specialize (H eq_refl)
                 end.
        induction partial_trace as [|m partial_trace IH].
        { do_unfold; pose m_in as m_in'; destruct m_in; do_solve. }
        { simpl @List.app in *.
          unfold on_input_RecieveNetwork in *.
          repeat match goal with
                 | [ H : context[@holds_of_all_messages ?T ?P (?x :: ?xs)%list] |- _ ]
                   => rewrite (@holds_of_all_messages_cons T P x xs) in H
                 | [ H : context[@holds_of_all_messages ?T ?P (?ls1 ++ ?ls2)%list] |- _ ]
                   => rewrite (@holds_of_all_messages_app T P x xs) in H
                 end.
          repeat first [ progress destruct_head'_prod
                       | progress destruct_head'_and
                       | progress destruct_head' iff ].
          apply IH; clear IH;
            repeat match goal with |- and _ _ => apply conj end; try assumption.
(*          Focus 2.
          { assumption.
            repeat match goal with
                   | [ H : _ = _ -> _ |- _ ] => specialize (H eq_refl)
                   | _ => progress subst
                   | [ H : (exists v, _ = _) -> _ |- _ ] => specialize (H (ex_intro _ _ eq_refl))
                   | _ => progress destruct_head'_ex
                   | [ H : Random _ = Random _ |- _ ] => inversion H; clear H
                   | [ H : ?x = ?y -> _ |- _ ]
                     => is_var x; destruct x
                   end.
          end.
          rewrite H' in H4.
                     (input * option pre_output)
                     _
                     m
                     (partial_trace ++ (m_in, x) :: restx)%list)
            in H4.
          unfold holds_of_all_messages
        { do_unfold; pose m_in as m_in'; destruct m_in; do_solve. }
        destruct partial_trace as [|m0 [|m1 [|m2 [|m3 [|m4 partial_trace].
        { do_unfold; pose m_in as m_in'; destruct m_in; do_solve. }
        { destruct m0 as [m0 ?]; pose m0 as m0'; do_unfold; destruct m0; do_solve.
          { destruct partial_trace as [|m1 partial_trace].*)
            (*
            { pose m_in as m_in'; destruct m_in; do_unfold; do_solve.
        }
        { do_unfold; pose m_in as m_in'; destruct m_in.

          do_solve. }
        { do_unfold; destruct_head' input; do_solve. }
        { do_unfold; pose m_in as m_in'; destruct m_in; do_solve. }
            pose m_in as m_in'; destruct m_in;
              (*destruct_head input;*)

            { repeat match goal with
                     | [ H : ~True -> _ |- _ ] => clear H
                     end.
              repeat match goal with
                         | _ => progress destruct_head'_and
                         | [ H : (exists v, ?m = @?k v) -> _ |- _ ]
                           => specialize (H (ex_intro _ _ eq_refl))
                         | [ H : context[~(exists v : ?T, ?m = @?k v) -> _] |- _ ]
                           => rewrite (@pull_ex_not T (fun v => m = k v)) in H
                         | [ H : context[(?A /\ ?B) -> ?C] |- _ ]
                           => rewrite (@impl_and_l A B C) in H
                         | [ H : (exists v, ?m = @?k v) -> _ |- _ ]
                           => first [ specialize (H (ex_intro _ m eq_refl))
                                    | let H' := fresh in
                                      assert (H' : forall v, m <> k v) by (clear; discriminate);
                                      clear H H' ]
                         | [ H : Some ?x = Some ?y -> _ |- _ ]
                           => first [ specialize (H eq_refl)
                                    | let H' := fresh in
                                      assert (H' : x <> y) by (clear; discriminate);
                                      clear H H' ]
                         | [ H : ?A, H' : ?A -> ?B |- _ ]
                           => specialize (H' H)
                         | [ H : (forall v, ?m <> @?k v) -> ?P |- _ ]
                           => let H' := fresh in
                              first [ assert (H' : forall v, m <> k v) by (clear; discriminate);
                                      cbv beta in H';
                                      specialize (H H')
                                    (*| clear H*) ]
                         | [ H : ?x <> ?x -> _ |- _ ]
                           => clear H
                         | [ H : (?x <> ?y) -> ?P |- _ ]
                           => let H' := fresh in
                              assert (H' : x <> y) by (clear; discriminate);
                                specialize (H H')
                         | [ H : ?x = ?y -> ?P |- _ ]
                           => first [ specialize (H eq_refl)
                                    | let H' := fresh in
                                      assert (H' : x <> y) by (clear; discriminate);
                                      clear H H' ]
                         | [ H : (?A -> ?B) -> ?C, H' : ?A |- _ ]
                           => assert (B -> C) by (intro; apply H; intro; assumption);
                                clear H
                         | [ H : ((exists v, ?m = @?k v) -> _) -> ?P |- _ ]
                           => assert P
                             by (apply H; let H' := fresh in intro H'; exfalso; revert H'; apply pull_ex_not; clear; discriminate);
                                clear H
                         end.
                  repeat match goal with
                         | [ H : False |- _ ] => exfalso; exact H
                         | [ H : context[List.Exists _ (_ :: _)] |- _ ]
                           => rewrite List.Exists_cons in H
                         | [ H : context[List.Exists _ nil] |- _ ]
                           => rewrite List.Exists_nil in H
                         | [ H : True -> _ |- _ ] => specialize (H I)
                         | [ H : _ \/ False |- _ ] => destruct H
                         end.
                  unfold Send_a in *.
              clear H95 H23.
            Focus 2.
              match goal with
              end.
              match goal with
                   | [ H : Some ?x <> Some _ -> (True -> Random _ = ?k) /\ _ |- _ ]
                     => is_var x; lazymatch k with Random _ => fail | _ => idtac end;
                          destruct x
                   | [ H : ?x <> Some _ -> (True -> Random _ = ?k) /\ _ |- _ ]
                     => is_var x; lazymatch k with Random _ => fail | _ => idtac end;
                          destruct x
                   end.

          { destruct_head' output.
            { destruct_head' pre_output; try reflexivity.
              { destruct_head' input.
                { repeat match goal with
                         | _ => progress destruct_head'_and
                         | [ H : (exists v, ?m = @?k v) -> _ |- _ ]
                           => specialize (H (ex_intro _ _ eq_refl))
                         | [ H : context[~(exists v : ?T, ?m = @?k v) -> _] |- _ ]
                           => rewrite (@pull_ex_not T (fun v => m = k v)) in H
                         | [ H : context[(?A /\ ?B) -> ?C] |- _ ]
                           => rewrite (@impl_and_l A B C) in H
                         | [ H : (exists v, ?m = @?k v) -> _ |- _ ]
                           => first [ specialize (H (ex_intro _ m eq_refl))
                                    | let H' := fresh in
                                      assert (H' : forall v, m <> k v) by (clear; discriminate);
                                      clear H H' ]
                         | [ H : Some ?x = Some ?y -> _ |- _ ]
                           => first [ specialize (H eq_refl)
                                    | let H' := fresh in
                                      assert (H' : x <> y) by (clear; discriminate);
                                      clear H H' ]
                         | [ H : ?A, H' : ?A -> ?B |- _ ]
                           => specialize (H' H)
                         | [ H : (forall v, ?m <> @?k v) -> ?P |- _ ]
                           => let H' := fresh in
                              first [ assert (H' : forall v, m <> k v) by (clear; discriminate);
                                      cbv beta in H';
                                      specialize (H H')
                                    (*| clear H*) ]
                         | [ H : ?x <> ?x -> _ |- _ ]
                           => clear H
                         | [ H : (?x <> ?y) -> ?P |- _ ]
                           => let H' := fresh in
                              assert (H' : x <> y) by (clear; discriminate);
                                specialize (H H')
                         | [ H : ?x = ?y -> ?P |- _ ]
                           => first [ specialize (H eq_refl)
                                    | let H' := fresh in
                                      assert (H' : x <> y) by (clear; discriminate);
                                      clear H H' ]
                         | [ H : (?A -> ?B) -> ?C, H' : ?A |- _ ]
                           => assert (B -> C) by (intro; apply H; intro; assumption);
                                clear H
                         | [ H : ((exists v, ?m = @?k v) -> _) -> ?P |- _ ]
                           => assert P
                             by (apply H; let H' := fresh in intro H'; exfalso; revert H'; apply pull_ex_not; clear; discriminate);
                                clear H
                         end.
                  repeat match goal with
                         | [ H : False |- _ ] => exfalso; exact H
                         | [ H : context[List.Exists _ (_ :: _)] |- _ ]
                           => rewrite List.Exists_cons in H
                         | [ H : context[List.Exists _ nil] |- _ ]
                           => rewrite List.Exists_nil in H
                         | [ H : True -> _ |- _ ] => specialize (H I)
                         | [ H : _ \/ False |- _ ] => destruct H
                         end.
                  SearchAbout List.Exists.
                  simpl in *.
                  move H0 at bottom.
                  repeat match goal with
                         end.
                  match goal with
                  end.
                  .
                  intro
                  clear H14.

                  match goal with
                  | [

                  simpl in *.

                  => rewrite pull_ex_not in H
                end.
                  => assert P; [ apply H; cut (forall v, m <> k v); clear;
                                 [ | discriminate ]
                               | ]
                end.

                cut (
                  test (assert (forall v, m <> k v) by (clear; discriminate));

                end.
                clear.
                discriminate.
          progress simpl in *.
        unfold unfold trace_satisfies_external_SKE_spec


    End
             *)
      Abort.
    End per_connection_choices.
  End per_connection_parameters.

  Definition synthesis_goal
    := { state : Type
     & { init : state -> Prop
     & { step : _ (* state -> input -> option pre_output -> state -> Prop *)
       | forall trace
                (our_longterm_secret : secret),
           exists (our_ephemeral_secret : secret)
                  (their_ephemeral_public their_longterm_public : public),
             @allows_behavior state input (option pre_output) init step trace
             -> @trace_satisfies_full_SKE_spec our_longterm_secret our_ephemeral_secret their_ephemeral_public their_longterm_public trace
         } } }.
End spec.
