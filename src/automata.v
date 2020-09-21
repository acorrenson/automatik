Require Import 
  Lists.List
  Init.Nat
  Lia
  Program.Equality.
Import ListNotations.

Set Implicit Arguments.

Record dfa (S A : Type) := DFA {
  initial_state : S;
  is_final : S -> bool;
  next : S -> A -> S
}.

Definition sem_denot_dfa (S A : Type) (w : list A) (m : dfa S A) : bool :=
  is_final m (fold_left (next m) w (initial_state m)).

(* Inductive sem_op_dfa (S A : Type) (m : dfa S A) : S -> A -> S -> Prop :=
  | step : forall q c,
    sem_op_dfa m q c (next m q c). *)

Inductive sem_op_dfa (S A : Type) (m : dfa S A) : S -> list A -> S -> Prop :=
  | no_step   : forall q,
    sem_op_dfa m q [] q
  
  | one_step  : forall q c,
    sem_op_dfa m q [c] (next m q c)
  
  | steps     : forall q q' c w,
    sem_op_dfa m (next m q c) w q' ->
    sem_op_dfa m q (c::w) q'.


Notation "[| m |] w " := (sem_denot_dfa w m) (at level 80).
Notation "[| m |] ( w , q )" := (fold_left (next m) w q) (at level 80).
Notation "( m , q1 , w ) --> q2" := (sem_op_dfa m q1 w q2) (at level 80).


Lemma fold_trans :
  forall S A (m : dfa S A) w q1 q2,
  fold_left (next m) w q1 = q2
  <->
  sem_op_dfa m q1 w q2.
Proof.
  intros. split.
  - dependent induction w; intros H.
    + elim H. apply no_step.
    + apply steps.
      apply IHw.
      assumption.
  - dependent induction w; intros H.
    + inversion H; subst; reflexivity.
    + inversion H; subst.
      ++ reflexivity.
      ++ simpl. apply IHw. assumption.
Qed.


Theorem sem_equiv :
  forall S A (m : dfa S A) w,
  sem_denot_dfa w m = true
  <->
  exists k, is_final m k = true /\ sem_op_dfa m (initial_state m) w k.
Proof.
  intros S A m w. 
  eelim (fold_trans m w).
  intros. split.
  - intro.
    unfold sem_denot_dfa in H1.
    exists ([|m|](w, initial_state m)).
    split; [assumption | apply H; reflexivity].
  - intros [x [H1 H2]].
    apply fold_trans in H2.
    unfold sem_denot_dfa; simpl.
    subst.
    assumption.
Qed.