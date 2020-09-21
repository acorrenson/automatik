Require Import 
  Lists.List
  Init.Nat
  Lia
  Nat
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
  
Lemma steps_r :
  forall S A (m : dfa S A) q q' c w,
    sem_op_dfa m q w  q' ->
    sem_op_dfa m q (w ++ [c]) (next m q' c).
Proof.
  intros.
  dependent induction H; simpl.
  - apply one_step.
  - apply steps, one_step.
  - apply steps.
    apply IHsem_op_dfa.
Qed.

(* Notation "[| m |] w " := (sem_denot_dfa w m) (at level 40).
Notation "[| m |] ( w , q )" := (fold_left (next m) w q) (at level 40).
Notation "( m , q1 , w ) --> q2" := (sem_op_dfa m q1 w q2) (at level 40). *)


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
    exists (fold_left (next m) w (initial_state m)).
    split; [assumption | apply H; reflexivity].
  - intros [x [H1 H2]].
    apply fold_trans in H2.
    unfold sem_denot_dfa; simpl.
    subst.
    assumption.
Qed.

Inductive binary := I | O.

Inductive states := S0 | S1 | S2.

Definition m3 : dfa states binary := {|
  initial_state := S0;
  is_final s := match s with S0 => true | _ => false end;
  next s x :=
    match s, x with
    | S0, O => S0
    | S0, I => S1
    | S1, O => S2
    | S1, I => S0
    | S2, O => S1
    | S2, I => S1
    end
|}.

Fixpoint base_2' (w : list binary) : nat :=
  match w with
  | [] => 0
  | I::x => pow 2 (length x) + (base_2' x)
  | O::x => base_2' x
  end.

Definition nat_of_bin n :=
  match n with
  | I => 1
  | O => 0
  end.

Definition base_2 w := fold_left (fun a b => nat_of_bin b + 2 * a) w 0.

Definition divide a b := exists k, b = a*k.

Theorem bin_ind:
    forall P : list binary -> Prop,
    P [] ->
    (forall (w : list binary), P w -> P (w ++ [I])) ->
    (forall (w : list binary), P w -> P (w ++ [O])) ->
    forall w, P w.
Proof.
Admitted.

Lemma base_2_wI:
  forall w, 
  base_2 (w ++ [I]) = 2*(base_2 w) + 1.
Proof.
  induction w.
  - simpl. reflexivity.
  - unfold base_2.
    rewrite fold_left_app.
    simpl.
    lia.
Qed.

Lemma base_2_WO:
  forall w,
  base_2 (w ++ [O]) = 2 *(base_2 w).
Proof.
  induction w.
  - simpl; reflexivity.
  - unfold base_2.
    rewrite fold_left_app.
    simpl.
    lia.
Qed.

Lemma case_S0:
  forall w,
  sem_op_dfa m3 S0 w S0 ->
  divide 3 (base_2 w).
Proof.
  intro.
  elim w using bin_ind.
  + intro; exists 0; reflexivity.
  + intros.
    inversion H0; subst.
    ++ assert (forall w, [] <> w ++ [I]).
      * intro. induction w1; discriminate.
      * apply H1 in H3. contradiction.
    ++ 
Abort.


(* Lemma trans_S0_I :
  forall w,
  sem_op_dfa m3 S0 w S0 ->
  sem_op_dfa m3 S0 (w ++ [I]) S1.
Proof.
  intros.
  replace (S1) with (next m3 S0 I) by reflexivity.
  apply steps_r.
  assumption.
Qed.

Lemma trans_S0_O :
  forall w,
  sem_op_dfa m3 S0 w S0 ->
  sem_op_dfa m3 S0 (w ++ [O]) S0.
Proof.
  intros.
  replace (S0) with (next m3 S0 O) by reflexivity.
  apply steps_r.
  assumption.
Qed.

Lemma trans_S1_I: 
  forall w,
  sem_op_dfa m3 S0 w S1 ->
  sem_op_dfa m3 S0 (w ++ [I]) S2.
Proof.
  intros.
  replace (S2) with (next m3 S1 I) by reflexivity.
  apply steps_r.
  assumption.
Qed.
 *)

Lemma sem_app:
  forall S A (m : dfa S A) q1 q2 q3 w1 w2,
  sem_op_dfa m q1 w1 q2 ->
  sem_op_dfa m q2 w2 q3 ->
  sem_op_dfa m q1 (w1 ++ w2) q3.
Proof.
  intros.
  dependent induction H0.
  - rewrite app_nil_r. assumption.
  - apply steps_r. assumption.
  - dependent induction H.
    + simpl.
      apply steps. assumption.
    + simpl. apply steps.
      apply steps.
      assumption.
    + simpl.
      apply steps.
      apply IHsem_op_dfa.
      ++ assumption.
      ++ intro.

Qed.

Lemma m3_correct:
  forall w, 
  sem_op_dfa m3 S0 w S0 ->
  divide 3 (base_2 w).
Proof.
  intro.
  elim w using bin_ind.
  + intro.
    exists 0; reflexivity.
  + intros.