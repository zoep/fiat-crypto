(** * Definition and Notations for [do { body }] *)
Require Import Coq.omega.Omega.
Require Import Crypto.Util.Notations.

Section with_state.
  (** TODO: MOVE ME *)
  Local Notation "'return' x" := (fun {T} (continuation:_->T) => continuation x) (at level 70).
  Local Notation "x <- v ; C" := (v _ (fun x => C)) (at level 70, right associativity, format "'[v' x  <-  v ; '/' C ']'").
  Local Notation "~> R" := (forall {T} (_:R->T), T) (at level 70).
  Local Notation "A ~> R" := (forall (_:A) {T} (_:R->T), T) (at level 99).

  Context {state : Type}.

  Definition loop_cps_step
             (loop_cps
              : forall (max_iter : nat)
                       (initial : state)
                       (body : state -> forall {T} (continue : state -> T) (break : state -> T), T),
                 ~> state)
             (max_iter : nat)
    : forall (initial : state)
             (body : state -> forall {T} (continue : state -> T) (break : state -> T), T),
      ~> state
    := fun st body
       => match max_iter with
          | 0
            => (return st)
          | S max_iter'
            => fun T ret
               => body st T (fun st' => @loop_cps max_iter' st' body _ ret) ret
          end.

  Fixpoint loop_cps (max_iter : nat)
    : forall (initial : state)
             (body : state -> forall {T} (continue : state -> T) (break : state -> T), T),
      ~> state
    := loop_cps_step loop_cps max_iter.

  Lemma unfold_loop_cps
        (max_iter : nat)
    : loop_cps max_iter
      = loop_cps_step loop_cps max_iter.
  Proof.
    destruct max_iter; reflexivity.
  Qed.

  Theorem loop_cps_def (max_iter : nat)
          (initial : state)
          (body : state -> forall {T} (continue : state -> T) (break : state -> T), T)
          T ret
    : loop_cps (S max_iter) initial body T ret =
      body initial (fun st' => @loop_cps max_iter st' body _ ret) ret.
  Proof.
    reflexivity.
  Qed.

  Theorem loop_cps_ind
          (invariant : state -> Prop)
          T (P : T -> Prop) n v0 body rest
    : invariant v0
      -> (forall v continue break,
             (forall v, invariant v -> P (continue v))
             -> (forall v, invariant v -> P (break v))
             -> invariant v
             -> P (body v T continue break))
      -> (forall v, invariant v -> P (rest v))
      -> P (loop_cps n v0 body T rest).
  Proof.
    revert v0 rest.
    induction n as [|n IHn]; intros v0 rest Hinv Hbody HP; simpl; auto.
  Qed.

  Local Hint Extern 2 => omega.

  Theorem loop_cps_wf_ind
          (measure : state -> nat)
          (invariant : state -> Prop)
          T (P : T -> Prop) n v0 body rest
    : invariant v0
      -> (forall v continue,
             invariant v
             -> (forall break,
                    (forall v', measure v' < measure v -> invariant v' -> P (continue v'))
                    -> P (body v T continue break))
                \/ P (body v T continue rest))
      -> measure v0 < n
      -> P (loop_cps n v0 body T rest).
  Proof.
    revert v0 rest.
    induction n as [|n IHn]; intros v0 rest Hinv Hbody Hmeasure; simpl; try omega.
    edestruct Hbody as [Hbody'|Hbody']; eauto.
  Qed.
End with_state.

(* N.B., Coq doesn't yet print this *)
Notation "'loop' _{ fuel } ( state1 .. staten = initial ) 'labels' ( continue , break ) {{ body }} ; rest"
  := (@loop_cps _ fuel initial
                (fun state1 => .. (fun staten => id (fun T continue break => body)) .. )
                _ (fun state1 => .. (fun staten => rest) .. ))
       (at level 200, state1 binder, staten binder, rest at level 10,
        format "'[v  ' 'loop' _{ fuel }  ( state1 .. staten  =  initial )  'labels'  ( continue ,  break )  {{ '//' body ']' '//' }} ; '//' rest").

Check loop _{ 10 } (x = 0) labels (continue, break) {{ continue (x + 1) }} ; x.
                 
Compute
  loop _{ 1234 } ('(i, a) = (0, 0)) labels (continue, break)
  {{
      if i <? 10
      then 
        continue (i + 1, a+1)
      else
        break (0, a)
  }};
  a.

(*
  for ( i = s; i < f; i++) updating (P = zero) labels (continue, break)
  {{
      continue (P+P)
  }};
  P.

  for ( i = s; i < f; i++) updating (P = zero) labels (continue)
  {{
      continue (P+P)
  }};
  P.
*)

(*
table of xi*(32^i)*B
        for 
        0 <= xi <= 8 (with sign flips, -8 <= xi <= 8)
        0 <= i <= 31
*)

Require Import Crypto.Util.Tuple.
Print Tuple.repeat.
Section ScalarMult.
  Context (G:Type) (zero:G).
  Context (k s w:nat). (* k steps of s stripes of w-bit chunks *)
  Let l : nat := k * s * w.


Check
  loop _{k} ('(i, P_s) = (0, Tuple.repeat zero s)) labels (continue, break)
  {{ if negb (i <? k) then break (i, P_s) else
      let i' := i + s in
      
      loop _{s} (j = 0) labels (continue, break)
           {{ if negb (j <? s) then break (j) else
                let j' := j + s in
               continue (j + 1)
           }};
      continue (i', P_s)
  }};
  P_s.

Check
  loop _{k} ('(i, P_s) = (0, Tuple.repeat zero s)) labels (continue, break)
  {{ if negb (i <? k) then break (i, P_s) else
      let i' := i + s in
      
      loop _{s} ('(j, x) = (0,0)) labels (continue, break)
           {{ if negb (j <? s) then break (j, x) else
                let j' := j + s in
               continue (j +1, x)
           }};
      continue (i', P_s)
  }};
  P_s.