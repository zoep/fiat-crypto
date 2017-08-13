Require Import Coq.Lists.List.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.SpecializeBy.

Section Trace.
  Context {state input output : Type}
          (init : state -> Prop)
          (step : state -> input -> output -> state -> Prop).
  Inductive multistep : state -> list (input*output) -> state -> Prop :=
  | multistep_nil (s:state) : multistep s nil s
  | multistep_snoc (s0 s1 s2:state) l (i:input) (o:output)
                   (_:multistep s0 l s1)
                   (_:step s1 i o s2) :
      multistep s0 (l++(i,o)::nil) s2.

  Definition allows_behavior l :=
    exists s0 s1, init s0 /\ multistep s0 l s1.
End Trace.

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
             (trace : list (list nat (*input*) * nat (*output*))) : Prop
    := output_in_list_and_previous_input_matching_satisfies
         (fun output => True)
         (fun i o => i <> nil -> List.In o i)
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

  Goal { state : Type
     & { init : state -> Prop
     & { step : _
       | forall trace,
           @allows_behavior state (list nat) nat init step trace
           -> @trace_satisfies_negotiation_spec trace } } }.
  Proof.
    Ltac start :=
      repeat match goal with
             | [ |- sigT _ ] => eexists
             | [ |- sig _ ] => eexists
             end.
    Ltac start_unfold :=
      lazymatch goal with
      | [ |- forall trace, allows_behavior ?init ?step trace -> ?satisfies ]
        => let H := fresh in
           intros ? H; hnf; revert H
      end.
    start.
    start_unfold.
    { eapply handle_stateless.
      Lemma handle_membership_with_first {T} (default : T)
        : forall i : list T, i <> nil -> In (hd default i) i.
      Proof. intros [|? ?] ?; simpl; auto; congruence. Qed.
      apply (handle_membership_with_first 0).
      intros ?? [ls ?] ?; simpl in *; subst; apply handle_membership_with_first. }
    Grab Existential Variables.
    exact (fun _ => True).
    exact unit.
  Defined.
End Example_1_Negotiation_Synthesis.
