Require Import Coq.Lists.List Init.Nat Coq.Program.Equality Lia. 
Import ListNotations.

Set Implicit Arguments.

Record dfa (S A : Type) := DFA {
  initial_state : S;
  is_final : S -> bool;
  next : S -> A -> option S
}.

Definition apply_trans S A (m : dfa S A) s a :=
  match s with
  | None    => None
  | Some s' => next m s' a
  end.

Definition check S A (m : dfa S A) s :=
  match s with
  | None    => false
  | Some s' => is_final m s'
  end.

Inductive transition (S A : Type) (m : dfa S A) : S -> A -> S -> Prop :=
  | step :
    forall s1 c s2,
    next m s1 c = Some (s2) -> transition m s1 c s2.

Inductive transitions (S A : Type) (m : dfa S A) : S -> list A -> S -> Prop :=
  | one_step :
    forall s1 c s2,
    transition m s1 c s2 ->
    transitions m s1 [c] s2
  | no_step :
    forall s,
    transitions m s [] s
  | many_steps :
    forall s1 c w s2 s3,
    transition m s1 c s2 ->
    transitions m s2 w s3 ->
    transitions m s1 (c::w) s3.


Definition run_dfa S A (m : dfa S A) (l : list A) : bool :=
  let i := Some (initial_state m) in
  check m (fold_left (apply_trans m) l i).

Theorem transitions_run_dfa:
  forall S A (m : dfa S A) w,
  run_dfa m w = true <-> exists f, is_final m f = true /\ transitions m (initial_state m) w f. 
Proof.
  intros S A m w.
  induction w; split; intro.
  - unfold run_dfa in *; simpl in *.
    exists (initial_state m).
    split; [assumption | apply no_step].
  - unfold run_dfa in *; simpl in *.
    elim H. intros x [H1 H2].
    inversion H2. subst.
    assumption.
  - unfold run_dfa in H.
    destruct (fold_left (apply_trans m) (a :: w) (Some (initial_state m))).
    + exists s.
      split.
      * inversion H; reflexivity.
      * eapply many_steps.
        ** apply.





Qed.

Inductive binary := I | O.

Inductive states := S0 | S1 | S2.

Definition m3 : dfa states binary := {|
  initial_state := S0;
  is_final s := match s with S0 => true | _ => false end;
  next s x :=
    match s, x with
    | S0, O => Some S0
    | S0, I => Some S1
    | S1, O => Some S2
    | S1, I => Some S0
    | S2, O => Some S1
    | S2, I => Some S1
    end;
|}.

Fixpoint base_2 (w : list binary) : nat :=
  match w with
  | [] => 0
  | I::x => (pow 2 (length x)) * base_2 x
  | O::x => base_2 x
  end.

Definition divide a b := exists k, b = a*k.


Theorem m3_correct1 :
  forall w, run_dfa m3 w = true -> divide 3 (base_2 w).
Proof.
  induction w; intro H.
  - exists 0; reflexivity.
  - destruct a; simpl.
    case_eq (run_dfa m3 w); intro.
    + elim (IHw H0). intros.
      exists (x * 2 ^ length w). lia.
    + unfol
    
    
  
  - intros [k Hw].
    induction w.
    + reflexivity.
    + destruct a.
      unfold run_dfa in *.
      simpl.
  -


