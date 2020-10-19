Require Import List Program PeanoNat Lia.
Import ListNotations.

Theorem destruct_post:
  forall A (l : list A),
  {exists a l', l = l' ++ [a]} + {l = []}.
Proof.
  intros.
  induction l.
  + right. reflexivity.
  + destruct IHl.
    - left.
      elim e.
      intros.
      elim H.
      intros.
      exists x.
      exists (a :: x0).
      simpl.
      rewrite H0.
      reflexivity.
    - left.
      exists a, [].
      simpl.
      subst.
      reflexivity.
Qed.

Lemma length_app:
  forall A (a : A) l, length l < length (l ++ [a]).
Proof.
  intros.
  induction l; simpl; lia.
Qed.

Program Fixpoint induction_post {A}
  (P : list A -> Prop)
  (init : forall l, l = [] -> P l)
  (hered : forall l a, P l -> P (l ++ [a]))
  (l : list A) {measure (length l)}: P l :=
  match destruct_post A l with
  | left x => _
  | right x => _
  end.

Next Obligation.
  apply hered.
  apply (induction_post _ _ init hered).
  apply length_app.
Qed.

(* Any kind of AUTOMATA *)
Record Automata {Alpha  State : Type} := AUTOMATA {
  transition  : State -> Alpha -> State -> Prop;
  initial     : State -> Prop;
  final       : State -> Prop;
}.

(* There exists a path q0 -> w -> q1 *)
Inductive path
  {Alpha State : Type}
  (aut : Automata)
  (q0 : State) : list Alpha -> State -> Prop :=

  | epsilon_transition :
    path aut q0 [] q0

  | many_transitions : forall (a : Alpha) (w : list Alpha) (q1 q2: State),
    (transition aut q0 a q1) ->
    (path aut q1 w q2) ->
    path aut q0 (a::w) q2.

Ltac valid_trans := (simpl; trivial).
Ltac stabilize q := (destruct q; try contradiction).


Lemma join_transitions :
  forall (A S : Type) (m : @Automata A S) (w1 w2 : list A) (q1 q2 q3 : S),
  path m q1 w1 q2 -> path m q2 w2 q3 -> path m q1 (w1 ++ w2) q3.
Proof.
  intros.
  dependent induction w1.
  - simpl. inversion H. assumption.
  - simpl.
    inversion H.
    eapply many_transitions.
    * apply H3.
    * eapply IHw1.
      + apply H5.
      + assumption.
Qed.

Definition accept {A S : Type} (aut : @Automata A S) w :=
  exists qi qf,
  path aut qi w qf
  /\ initial aut qi
  /\ final aut qf.

Inductive alphabet :=
  | lettre_i
  | lettre_n
  | lettre_t.

Inductive states :=
  | s1
  | s2
  | s3
  | s4.

Definition ma_relation (q1 : states) (a : alphabet) (q2 : states) :=
  match q1, a, q2 with
  | s1, lettre_i, s2 => True
  | s2, lettre_n, s3 => True
  | s3, lettre_t, s4 => True
  | _, _, _ => False
  end.

Definition la_fin (q : states) := match q with s4 => True | _ => False end.
Definition le_debut (q : states) := match q with s1 => True | _ => False end.

Definition mon_automate := {|
    transition := ma_relation;
    final := la_fin;
    initial := le_debut;
|}.



Theorem test_int:
  exists (q0 q1 : states),
    path mon_automate q0 [lettre_i; lettre_n; lettre_t] q1
    /\ initial mon_automate q0
    /\ final mon_automate q1.
Proof.
  exists s1.
  exists s4.
  repeat split.
  apply many_transitions with (q1 := s2); valid_trans.
  apply many_transitions with (q1 := s3); valid_trans.
  apply many_transitions with (q1 := s4); valid_trans.
  apply epsilon_transition.
Qed.


Theorem test_i:
  forall (n : nat),
    not (accept mon_automate (repeat lettre_i n)).
Proof.
  destruct n; intros (qi & qf & [C [H1 H2]]).
  all: stabilize qi; stabilize qf.
  all: inversion C; subst.
  destruct n; stabilize q1.
  all: inversion H5; subst.
  stabilize q1.
Qed.


Inductive trans_just {A : Type} (w : list A) : nat -> A -> nat -> Prop :=
  | trans_char: forall c n,
    nth_error w n = Some c ->
    trans_just w n c (n + 1).

Definition just {A} (w : list A) := {|
  transition := trans_just w;
  final := fun x => if Nat.eqb x (length w) then True else False;
  initial := fun x => if Nat.eqb x 0 then True else False;
|}.

Lemma just_init:
  forall A (w : list A) q,
    initial (just w) q -> q = 0.
Proof.
  intros.
  induction w.
  + stabilize q. reflexivity.
  + apply IHw.
    stabilize q.
    auto.
Qed.

Lemma just_final:
  forall A (w : list A) q,
    final (just w) q -> q = length w.
Proof.
  intros.
  simpl in H.
  destruct (q =? length w) eqn:E.
  + apply Nat.eqb_eq in E. assumption.
  + contradiction.
Qed.

Lemma get_final:
  forall A (w : list A),
  final (just w) (length w).
Proof.
  intros.
  unfold just.
  simpl.
  assert (length w = length w) by reflexivity.
  rewrite <- (Nat.eqb_eq) in H.
  replace (length w =? length w) with true by apply H.
  trivial.
Qed.

Lemma nth_app:
  forall A a (l l' : list A) n,
  nth_error l n = Some a -> nth_error (l ++ l') n = Some a.
Proof.
  intros.
  assert (nth_error l n <> None).
  + intro C. replace (nth_error l n) with (@None A) in H.
    discriminate H.
  + apply nth_error_Some in H0.
    erewrite nth_error_app1; assumption.
Qed.

Lemma path_cons:
  forall A S (m : @Automata A S) (a : A) (w : list A) (q1 q2 : S),
  path m q1 (a :: w) q2 -> exists q3, (transition m q1 a q3).
Proof.
  intros.
  inversion H; subst.
  exists q0.
  apply H2.
Qed.

Lemma just_app_path:
  forall A  (w1 w2 w3 : list A) q1 q2,
  path (just w1) q1 w3 q2 ->
  path (just (w1 ++ w2)) q1 w3 q2.
Proof.
  intros.
  induction H.
  - apply epsilon_transition.
  - eapply many_transitions.
    + simpl. apply trans_char.
      inversion H; subst.
      apply nth_app. assumption.
    + inversion H; subst.
      apply IHpath.
Qed.

Lemma nth_post:
  forall A (w : list A) a,
  nth_error (w ++ [a]) (length w) = Some a.
Proof.
  intros.
  induction w.
  + simpl. reflexivity.
  + simpl. apply IHw.
Qed.

Lemma just_accept:
  forall A (w : list A), accept (just w) w.
Proof.
  intros.
  unfold accept.
  exists 0, (length w).
  induction w using (@induction_post); repeat split; subst.
  - apply epsilon_transition.
  - simpl. trivial.
  - inversion IHw as [Hpath _].
    eapply join_transitions.
    + simpl. apply just_app_path.
      apply Hpath.
    + eapply many_transitions.
      * simpl. apply trans_char.
        apply nth_post.
      * rewrite app_length. simpl.
        apply epsilon_transition.
  - apply get_final.
Qed.