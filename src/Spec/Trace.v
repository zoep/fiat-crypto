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
    exists s0 s1, init s0 /\ multistep s0 l s1.
End Trace.
