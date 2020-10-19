(***********************************************)
(*   Small library to manipulate DFAs in Coq   *)
(*            Arthur Correnson                 *)
(*      <arthur.correnson@ens-rennes.fr>       *)
(***********************************************)

Require Import
  Lists.List
  Init.Nat
  Lia
  Nat
  Program.Equality.

Import ListNotations.

Set Implicit Arguments.

(***********************************************)
(** * Definitions                              *)
(***********************************************)


(** Definition of DFAs *)
Record dfa (S A : Type) := DFA {
  initial_state : S;
  is_final : S -> bool;
  next : S -> A -> S
}.

(** Run a DFA [m] from state [q] *)
Definition run_from (S A : Type) (m : dfa S A) (q : S) (w : list A) : S :=
  fold_left (next m) w q.

(**
  Check if a word [w] is accepted by a dfa [m].
  [accept m] can be thought of as [m]'s denotational semantic.
*)
Definition accept (S A : Type) (m : dfa S A) (w : list A) : bool :=
  is_final m (run_from m (initial_state m) w).

(**
  Inductive predicate indicating the existence of a path ([q] [w] [q']) wrt [m].
  Usefull for proofs requiring to keep track of the states
  taken by the dfa.
  [path m] can be thought of as [m]'s operational semantic.
*)
Inductive path (S A : Type) (m : dfa S A) : S -> list A -> S -> Prop :=
  (* Epsilon transitions can always be simulated *)
  | epsilon_path : forall q,
    path m q [] q
  
  (* There exists a path of size 1 ([q] [c] [q']) for every transition (q, c, q') *)
  | unit_path  : forall q c,
    path m q [c] (next m q c)
  
  (* If there exists a path ([q] [w] [q']) and a path ([q'] [w'] [q''])
    then, there exists a path ([q] [w.w'] [q'']) *)
  | trans_path : forall q1 q2 q3 w1 w2,
    path m q1 w1 q2 ->
    path m q2 w2 q3 ->
    path m q1 (w1 ++ w2) q3.


(***********************************************)
(** * Usefull properties                       *)
(***********************************************)

(**
  If there exists a path ([q'] [w] [q'']) and if
  (q, a, q') is a transition, then there exists
  a path ([q] [a.w] [q''])
*)
Lemma cons_path:
  forall (S A : Type) (m : dfa S A) a w q1 q2,
  path m (next m q1 a) w q2 ->
  path m q1 (a::w) q2.
Proof.
  intros.
  dependent destruction H.
  - apply unit_path.
  - replace ([a; c]) with ([a] ++ [c]) by reflexivity.
    eapply trans_path; apply unit_path.
  - replace (a :: w1 ++ w2) with ([a] ++ w1 ++ w2) by reflexivity.
    eapply trans_path.
    + apply unit_path.
    + eapply trans_path.
      ++ apply H.
      ++ apply H0.
Qed.

Notation "( m , q1 , w ) --> q2" := (path m q1 w q2) (at level 80).

(**
  If runing [m] on a word [w] from state [q] places [m] 
  in a new state [q'], then there exists a path ([q] [w] [q'])
  and reciprocally.
*)
Lemma run_from_path :
  forall S A (m : dfa S A) w q1 q2,
  run_from m q1 w = q2
  <->
  path m q1 w q2.
Proof.
  intros. split.
  - dependent induction w; intros H.
    + elim H. apply epsilon_path.
    + apply (cons_path _ _ (IHw _ _ H)).
  - intro.
    dependent induction H.
    + reflexivity.
    + reflexivity.
    + unfold run_from in *.
      rewrite fold_left_app; subst.
      reflexivity.
Qed.

(**
  If [m] accepts [w], then there exists a path from the initial state
  to a terminal state and reciprocally.
*)
Theorem accept_path :
  forall S A (m : dfa S A) w,
  accept m w = true
  <->
  exists k, is_final m k = true /\ path m (initial_state m) w k.
Proof.
  intros S A m w.
  edestruct (run_from_path m w (initial_state m)) as [H1 H2]; split.
  + intro H3.
    exists (run_from m (initial_state m) w).
    split; [exact H3 | apply H1; reflexivity].
  + intros [qf [H3 H4]].
    apply run_from_path in H4.
    subst.
    assumption.
Qed.

