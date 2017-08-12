Require Import Coq.Lists.List.
Require Import Crypto.Util.Decidable.

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
  (* FIXME: maybe replace with invariant definition *)
  Definition allows_behavior l :=
    exists s0 s1, init s0 -> multistep s0 l s1.
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
        R (fst other_message) (snd message).

Section Example_1_Negotiation.
  Definition trace_satisfies_negotiation_spec
             (trace : list (list nat (*input*) * nat (*output*))) : Prop
    := output_in_list_and_previous_input_matching_satisfies
         (fun output => True)
         (fun i o => List.In o i)
         trace.
End Example_1_Negotiation.

Section Example_1_Negotiation_Synthesis.
  Opaque output_in_list_and_previous_input_matching_satisfies.
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
      Require Import Crypto.Util.Tactics.DestructHead.
      destruct_head_hnf' ex.

    Abort.
  Abort.
End Example_1_Negotiation_Synthesis.
