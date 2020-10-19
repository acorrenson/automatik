Require Import List Program Relation_Definitions Bool.Sumbool Psatz.
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

Check (left).
Compute (ex).

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



