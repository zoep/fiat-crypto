Require Import Coq.Lists.List.
Require Import Crypto.Spec.Trace.
Require Import Crypto.Protocols.TLS13.Structures.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.GetGoal.

(* 1. Synthesize "intersection negotiation" of options, e.g., choose
curve
2. same as 1, but with "forall stream" quantifiers for multiple
connections Alternatively, we might parameterize over a record that is
FMap-like, but allows add to fail (to allow fixed number of
connections)
3. randomness - get g^x, g^y, send g^(x*y) *)

Notation eta x := (fst x, snd x).

(* TODO: multiple other messages *)
Definition output_in_list_and_previous_input_matching_satisfies
           {input output} (matcher : output -> Prop) (R : input -> output -> Prop)
           trace
  := forall message : input * output,
    List.In message trace
    -> matcher (snd message)
    -> exists other_message : input * output,
        List.In other_message trace
        /\ R (fst other_message) (snd message).

Lemma output_in_list_and_previous_input_matching_satisfies_nil
      {input output matcher R}
  : @output_in_list_and_previous_input_matching_satisfies input output matcher R nil.
Proof.
  intros ? H; inversion H.
Qed.

Lemma output_in_list_and_previous_input_matching_satisfies_snoc
      {input output matcher R}
      trace msg
  : @output_in_list_and_previous_input_matching_satisfies input output matcher R trace
    -> (matcher (snd msg)
        -> exists other_message,
           List.In other_message (trace ++ (msg::nil))
           /\ R (fst other_message) (snd msg))
    -> @output_in_list_and_previous_input_matching_satisfies input output matcher R (trace ++ (msg::nil)).
Proof.
  unfold output_in_list_and_previous_input_matching_satisfies.
  setoid_rewrite in_app_iff; simpl.
  intros H0 H1 message Hin Hmatcher.
  destruct_head'_or; destruct_head' False; subst; eauto.
  { specialize (H0 message); specialize_by_assumption.
    destruct_head'_ex; destruct_head'_and; eauto. }
Qed.

Section Example_1_Negotiation.
  Definition trace_satisfies_negotiation_spec
             (trace : list (list nat (*input*) * option nat (*output*))) : Prop
    := output_in_list_and_previous_input_matching_satisfies
         (fun output => True)
         (fun i o => i <> nil -> exists v, o = Some v -> List.In v i)
         trace.
  Definition trace_satisfies_negotiation_spec_error
             (trace : list (list nat (*input*) * option nat (*output*))) : Prop
    := output_in_list_and_previous_input_matching_satisfies
         (fun output => True)
         (fun i o => i = nil -> o = None)
         trace.
End Example_1_Negotiation.

Section Example_1_Negotiation_Synthesis.
  Opaque output_in_list_and_previous_input_matching_satisfies.

  Lemma handle_stateless {state input output init}
        {trace matcher} {R : _ -> _ -> Prop}
        (handler : input -> output)
        (step : state -> input -> output -> state -> Prop
         := fun _ i o _ => handler i = o)
        (handler_ok : forall i, R i (handler i))
    : (forall st0 st1 io, step st0 (fst io) (snd io) st1
                          -> R (fst io) (snd io))
      -> (@allows_behavior state input output init step trace
          -> output_in_list_and_previous_input_matching_satisfies
               matcher R trace).
  Proof.
    subst step; cbv beta.
    intros Hstep Hbehavior.
    repeat first [ progress destruct_head_hnf' ex
                 | progress destruct_head'_and ].
    let H := match goal with H : multistep _ _ _ _ |- _ => H end in
    induction H as [|??????? IH]; subst.
    { apply output_in_list_and_previous_input_matching_satisfies_nil. }
    { repeat first [ progress specialize_by_assumption
                   | assumption
                   | apply output_in_list_and_previous_input_matching_satisfies_snoc
                   | setoid_rewrite List.in_app_iff
                   | intro
                   | eexists
                   | apply conj
                   | eapply (Hstep (_, _)); simpl; reflexivity
                   | solve [ auto ]
                   | progress simpl ]. }
  Qed.

  Lemma handle_membership_with_first {T} (default : T)
    : forall i : list T, i <> nil -> In (hd default i) i.
  Proof. intros [|? ?] ?; simpl; auto; congruence. Qed.

  Lemma handle_membership_with_first_alt {T} (default : T) handler
    : (forall i : list T, i <> nil -> handler i = Some (hd default i))
      -> forall i : list T, i <> nil -> exists v, handler i = Some v -> In v i.
  Proof.
    intros H ls Hnil; specialize (H ls Hnil); rewrite H; clear H.
    exists (hd default ls); intros _.
    destruct ls; simpl; auto; congruence.
  Qed.

  Lemma handle_decidable_equality {T} (val : T) {Hdec : forall v, Decidable (v = val)} {U} (retv : U) handler
    : forall v : T, v = val -> (if dec (v = val) then retv else handler v) = retv.
  Proof.
    intros; subst.
    edestruct dec; congruence.
  Qed.

  Ltac start :=
    repeat match goal with
           | [ |- sigT _ ] => eexists
           | [ |- sig _ ] => eexists
           end.
  Ltac hnf_under_and G :=
    match G with
    | ?A /\ ?B
      => hnf_under_and A; hnf_under_and B
    | _ => let G' := (eval hnf in G) in
           change G with G'
    end.
  Ltac hnf_under_and_goal :=
    let G := get_goal in
    hnf_under_and G.
  Ltac start_unfold :=
    lazymatch goal with
    | [ |- forall trace, allows_behavior ?init ?step trace -> ?satisfies ]
      => let H := fresh in
         intros ? H; hnf_under_and_goal; revert H
    end.
  Ltac split_and_under_arrow :=
    lazymatch goal with
    | [ |- allows_behavior _ _ _ -> _ ]
      => let H := fresh in
         intro H; repeat apply conj; revert H
    end.
  Ltac handle_decidable_equality :=
    lazymatch goal with
    | [ |- forall v, v = ?k -> ?handler v = ?retv ]
      => is_evar handler;
         let lem := constr:(@handle_decidable_equality _ k _) in
         eapply (lem _ retv _)
    | [ |- forall v, (if dec (@?p v = ?k) then ?retv else _) = @?q v -> @?p v = ?k -> @?q v = ?retv ]
      => intro; edestruct dec; congruence
    end.
  Lemma strip_handle_decidable_equality {T} (val : T) {Hdec : forall v, Decidable (v = val)} {U} (retv : U) handler (P : U -> T -> Prop)
    : (forall v : T, v <> val -> P (if dec (v = val) then retv else handler v) v)
      <-> (forall v : T, v <> val -> P (handler v) v).
  Proof.
    split; intros H v Hval; specialize (H v Hval);
      edestruct dec; try assumption; congruence.
  Qed.
  Ltac strip_handle_decidable_equality :=
    lazymatch goal with
    | [ |- forall ls : ?T, ls <> ?val -> _ ]
      => let ls' := fresh ls in
         let H := fresh in
         intros ls' H;
         lazymatch goal with
         | [ |- context[if (@dec (ls' = val) ?Hdec) then ?t else ?f] ]
           => pattern (if (@dec (ls' = val) Hdec) then t else f);
              let P := lazymatch goal with |- ?P _ => P end in
              let P := lazymatch (eval pattern ls' in P) with ?P _ => P end in
              let f := lazymatch (eval pattern ls' in f) with ?f _ => f end in
              revert ls' H;
              apply (proj2 (@strip_handle_decidable_equality _ val _ _ t f (fun a b => P b a)))
         end
    end.
  Goal { state : Type
     & { init : state -> Prop
     & { step : _
       | forall trace,
           @allows_behavior state (list nat) (option nat) init step trace
           -> @trace_satisfies_negotiation_spec trace
              /\ @trace_satisfies_negotiation_spec_error trace} } }.
  Proof.
    start.
    start_unfold.
    split_and_under_arrow;
      (eapply handle_stateless; [ | intros ?? ]);
      [ > repeat first [ handle_decidable_equality
                       | progress cbv beta
                       | strip_handle_decidable_equality ].. ];
      [ > repeat first [ handle_decidable_equality
                       | progress cbv beta
                       | strip_handle_decidable_equality ].. ].
    { eapply handle_membership_with_first_alt; reflexivity. }
    { cbv beta.
      intros [? ?]; intros; edestruct dec; try congruence; simpl in *; subst.
      eexists; intro H; inversion H; subst.
      destruct_one_head list; auto; congruence. }
    Grab Existential Variables.
    exact 0.
    exact 0.
    exact (fun _ => True).
    exact unit.
  Defined.
End Example_1_Negotiation_Synthesis.

Import EqNotations.

Section Example_2_ServerNegotiateDH.
  Context (decision_dataT : Type)
          (using_diffie_hellman : decision_dataT -> bool).

  Definition server_negotiation_DH_spec
             (global_data : decision_dataT)
             (trace : list (Handshake (*input*) * Handshake (*output*))) : Prop
    := forall io, List.In io trace
                  -> forall length hello,
        snd io = {| Handshake.msg_type := server_hello;
                    Handshake.length := length;
                    Handshake.payload := hello |}
        -> using_diffie_hellman global_data = true
           <-> exists extension,
            List.In extension (ServerHello.extensions hello)
            /\ Extension.extension_type _ extension = key_share.

  Definition server_negotiation_DH_spec'
             (global_data : decision_dataT)
             (trace : list (Handshake (*input*) * Handshake (*output*))) : Prop
    := forall io, List.In io trace
                  -> forall length hello,
        snd io = {| Handshake.msg_type := server_hello;
                    Handshake.length := length;
                    Handshake.payload := hello |}
        -> using_diffie_hellman global_data = true
           <-> exists extension,
            List.In extension (ServerHello.extensions hello)
            /\ Extension.extension_type _ extension = supported_groups.
End Example_2_ServerNegotiateDH.
