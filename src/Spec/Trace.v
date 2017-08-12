Require Import Coq.Lists.List.

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

Section Example_1_Negotiation.
  Definition trace_satisfies_negotiation_spec
             (trace : list (list nat (*input*) * nat (*output*))) : Prop
    := forall io, List.In io trace
                  -> let '(i, o) := eta io in List.In o i.
End Example_1_Negotiation.

Section Example_1_Negotiation_Synthesis.
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
          {step : state -> input -> output -> state -> Prop}
          {trace P}
      : (forall st0 st1 io, step st0 (fst io) (snd io) st1
                            -> P io)
        -> (@allows_behavior state input output init step trace
            -> forall v, In v trace -> P v).
    Abort.
  Abort.
End Example_1_Negotiation_Synthesis.
