Require Import Coq.Lists.List.

Create HintDb trace_combinators discriminated.

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
Hint Unfold holds_of_messages_before_nth_message_matching : trace_combinators.
Definition holds_of_nth_message_matching
           (n : nat)
           {T}
           (matcher : T -> Prop)
           (property : T -> Prop)
           (trace : list T)
  : Prop
  := holds_of_messages_around_nth_message_matching
       n matcher (fun _ m _=> property m) trace.
Hint Unfold holds_of_nth_message_matching : trace_combinators.
Definition holds_of_messages_after_nth_message_matching
           (n : nat)
           {T}
           (matcher : T -> Prop)
           (property : T -> list T -> Prop)
           (trace : list T)
  : Prop
  := holds_of_messages_around_nth_message_matching
       n matcher (fun before m after => property m after) trace.
Hint Unfold holds_of_messages_after_nth_message_matching : trace_combinators.
Definition on_input {input output T} (f : input -> T) : input * output -> T
  := fun '(i, o) => f i.
Hint Unfold on_input : trace_combinators.
Definition on_output {input output T} (f : output -> T) : input * output -> T
  := fun '(i, o) => f o.
Hint Unfold on_output : trace_combinators.

Definition holds_of_all_messages_after_nth_message_matching_gen
           (include_nth_msg : bool)
           (n : nat)
           {T}
           (matcher : T -> Prop)
           (property : T (* nth_msg *) -> T (* other message *) -> Prop)
           (trace : list T)
  : Prop
  := holds_of_messages_after_nth_message_matching
       n
       matcher
       (fun m after
        => List.Forall (property m) (if include_nth_msg then m::after else after))
       trace.
Hint Unfold holds_of_all_messages_after_nth_message_matching_gen : trace_combinators.
Notation holds_of_all_messages_after_nth_message_matching
  := (holds_of_all_messages_after_nth_message_matching_gen true).
Notation holds_of_all_messages_strictly_after_nth_message_matching
  := (holds_of_all_messages_after_nth_message_matching_gen false).
Definition holds_of_some_message_before_nth_message_matching_gen
           (include_nth_message : bool)
           (n : nat)
           {T}
           (matcher : T -> Prop)
           (property : T (* nth_msg *) -> T (* other message *) -> Prop)
           (trace : list T)
  : Prop
  := holds_of_messages_before_nth_message_matching
       n
       matcher
       (fun before m
        => List.Exists (property m) (if include_nth_message then (before ++ (m::nil))%list else before))
       trace.
Hint Unfold holds_of_some_message_before_nth_message_matching_gen : trace_combinators.
Notation holds_of_some_message_before_nth_message_matching
  := (holds_of_some_message_before_nth_message_matching_gen true).
Notation holds_of_some_message_strictly_before_nth_message_matching
  := (holds_of_some_message_before_nth_message_matching_gen false).
