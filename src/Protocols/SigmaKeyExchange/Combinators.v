Require Import Coq.Lists.List.

Create HintDb trace_combinators discriminated.

Fixpoint holds_of_messages_around_nth_messages_matching_aux
         (is_n : nat -> Prop)
         (if_none_found : Prop)
         {T}
         (matcher : T -> Prop)
         (property : list T -> T -> list T -> Prop)
         (pre_trace : list T)
         (trace : list T)
: Prop
:= match trace with
   | nil => if_none_found
   | m :: ms
     => (matcher m ->
         (is_n 0 -> property pre_trace m ms)
         /\ holds_of_messages_around_nth_messages_matching_aux
              (fun n' => is_n (S n'))
              (is_n 0 \/ if_none_found)
              matcher
              property
              (pre_trace ++ m::nil)
              ms)
        /\ (~matcher m
            -> holds_of_messages_around_nth_messages_matching_aux
                 is_n
                 if_none_found
                 matcher property (pre_trace ++ (m::nil)) ms)
   end%list.
Class reverse_search := do_reverse : bool.
Definition holds_of_messages_around_nth_messages_matching
           {rev : reverse_search}
           (is_n : nat -> Prop)
           (if_none_found : Prop)
           {T}
           (matcher : T -> Prop)
           (property : list T -> T -> list T -> Prop)
           (trace : list T)
  : Prop
  := holds_of_messages_around_nth_messages_matching_aux
       is_n if_none_found
       matcher
       (fun pre m post
        => if rev
           then property (List.rev post) m (List.rev pre)
           else property pre m post)
       nil
       (if rev then List.rev trace else trace).
Hint Unfold holds_of_messages_around_nth_messages_matching : trace_combinators.
Notation holds_of_messages_around_nth_message_matching n
  := (holds_of_messages_around_nth_messages_matching (fun n' => n = n') True).
Definition holds_of_messages_before_nth_messages_matching
           {rev : reverse_search}
           (is_n : nat -> Prop)
           (if_none_found : Prop)
           {T}
           (matcher : T -> Prop)
           (property : list T -> T -> Prop)
           (trace : list T)
  : Prop
  := holds_of_messages_around_nth_messages_matching
       is_n if_none_found matcher (fun before m after => property before m) trace.
Hint Unfold holds_of_messages_before_nth_messages_matching : trace_combinators.
Notation holds_of_messages_before_nth_message_matching n
  := (holds_of_messages_before_nth_messages_matching (fun n' => n = n') True).
Notation holds_of_messages_before_all_messages_matching
  := (holds_of_messages_before_nth_messages_matching (fun _ => True) True).
Definition holds_of_nth_messages_matching
           {rev : reverse_search}
           (is_n : nat -> Prop)
           (if_none_found : Prop)
           {T}
           (matcher : T -> Prop)
           (property : T -> Prop)
           (trace : list T)
  : Prop
  := holds_of_messages_around_nth_messages_matching
       is_n if_none_found matcher (fun _ m _=> property m) trace.
Hint Unfold holds_of_nth_messages_matching : trace_combinators.
Definition holds_of_nth_messages_matching_if_they_exist {rev} is_n {T}
  := holds_of_nth_messages_matching (rev:=rev) is_n True (T:=T).
Hint Unfold holds_of_nth_messages_matching_if_they_exist : trace_combinators.
Definition holds_of_nth_message_matching {rev} n {T}
  := @holds_of_nth_messages_matching rev (fun n' => n = n') True T.
Hint Unfold holds_of_nth_message_matching : trace_combinators.
Definition holds_of_nth_to_last_message_matching n {T}
  := holds_of_nth_message_matching n (rev:=true) (T:=T).
Hint Unfold holds_of_nth_to_last_message_matching : trace_combinators.
Definition holds_of_all_messages_matching {T}
  := @holds_of_nth_messages_matching false (fun _ => True) True T.
Hint Unfold holds_of_all_messages_matching : trace_combinators.
Definition holds_of_all_messages {T}
  := @holds_of_all_messages_matching T (fun _ => True).
Hint Unfold holds_of_all_messages : trace_combinators.
Definition holds_of_nth_message_matching_which_must_exist {rev} n {T}
  := @holds_of_nth_messages_matching rev (fun n' => n = n') False T.
Hint Unfold holds_of_nth_message_matching_which_must_exist : trace_combinators.
Definition holds_of_nth_to_last_message_matching_which_must_exist n {T}
  := holds_of_nth_message_matching_which_must_exist n (rev:=true) (T:=T).
Hint Unfold holds_of_nth_to_last_message_matching_which_must_exist : trace_combinators.
Definition nth_message_matching_exists {rev} n {T} matcher
  := @holds_of_nth_message_matching_which_must_exist rev n T matcher (fun _ => True).
Hint Unfold nth_message_matching_exists : trace_combinators.
Definition holds_of_messages_after_nth_messages_matching
           {rev : reverse_search}
           (is_n : nat -> Prop)
           (if_none_found : Prop)
           {T}
           (matcher : T -> Prop)
           (property : T -> list T -> Prop)
           (trace : list T)
  : Prop
  := holds_of_messages_around_nth_messages_matching
       is_n if_none_found matcher (fun before m after => property m after) trace.
Hint Unfold holds_of_messages_after_nth_messages_matching : trace_combinators.
Notation holds_of_messages_after_nth_message_matching n
  := (holds_of_messages_after_nth_messages_matching (fun n' => n = n') True).
Definition on_input {input output T} (f : input -> T) : input * output -> T
  := fun '(i, o) => f i.
Hint Unfold on_input : trace_combinators.
Definition on_output {input output T} (f : output -> T) : input * output -> T
  := fun '(i, o) => f o.
Hint Unfold on_output : trace_combinators.

Definition holds_of_all_messages_after_nth_messages_matching_gen
           {rev : reverse_search}
           (include_nth_msg : bool)
           (is_n : nat -> Prop)
           (if_none_found : Prop)
           {T}
           (matcher : T -> Prop)
           (property : T (* nth_msg *) -> T (* other message *) -> Prop)
           (trace : list T)
  : Prop
  := holds_of_messages_after_nth_messages_matching
       is_n
       if_none_found
       matcher
       (fun m after
        => List.Forall (property m) (if include_nth_msg then m::after else after))
       trace.
Hint Unfold holds_of_all_messages_after_nth_messages_matching_gen : trace_combinators.
Notation holds_of_all_messages_after_nth_messages_matching
  := (holds_of_all_messages_after_nth_messages_matching_gen true).
Notation holds_of_all_messages_after_nth_message_matching n
  := (holds_of_all_messages_after_nth_messages_matching (fun n' => n = n') True).
Notation holds_of_all_messages_strictly_after_nth_messages_matching
  := (holds_of_all_messages_after_nth_messages_matching_gen false).
Notation holds_of_all_messages_strictly_after_nth_message_matching n
  := (holds_of_all_messages_strictly_after_nth_messages_matching (fun n' => n = n') True).
Definition holds_of_some_message_before_nth_messages_matching_gen
           {rev : reverse_search}
           (include_nth_message : bool)
           (is_n : nat -> Prop)
           (if_none_found : Prop)
           {T}
           (matcher : T -> Prop)
           (property : T (* nth_msg *) -> T (* other message *) -> Prop)
           (trace : list T)
  : Prop
  := holds_of_messages_before_nth_messages_matching
       is_n
       if_none_found
       matcher
       (fun before m
        => List.Exists (property m) (if include_nth_message then (before ++ (m::nil))%list else before))
       trace.
Hint Unfold holds_of_some_message_before_nth_messages_matching_gen : trace_combinators.
Notation holds_of_some_message_before_nth_messages_matching
  := (holds_of_some_message_before_nth_messages_matching_gen true).
Notation holds_of_some_message_before_nth_message_matching n
  := (holds_of_some_message_before_nth_messages_matching (fun n' => n = n') True).
Notation holds_of_some_message_strictly_before_nth_messages_matching
  := (holds_of_some_message_before_nth_messages_matching_gen false).
Notation holds_of_some_message_strictly_before_nth_message_matching n
  := (holds_of_some_message_strictly_before_nth_messages_matching (fun n' => n = n') True).

Global Instance default_rev : reverse_search := false.
