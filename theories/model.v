(** Coq Model of Graphs/Automaton *)

Require Import Automatik.operators Automatik.pset.
Require Import List.
Import ListNotations.

Section Model.

Variable S : Type.
Variable A : Type.


(** ** Abstract Representation of a graph/automata *)


Record t : Type := {
  m_initial   : list S;
  m_final     : list S;
  m_relation  : S -> list (A * S);
}.


(** ** Semantic of a graph/automata *)


(** Taking a labeled step *)
Definition lstep (m : t) x a y :=
  In (a, y) (m_relation m x).
Instance lstep_op : LstepOp t S A := lstep.

(** Taking a step *)
Definition step (m : t) (x y : S) :=
  exists a, lstep m x a y.
Instance step_op : StepOp t S := step.


(** ** Properties of Automaton *)


(** What it means to be deterministic *)
Definition Determinist (m : t) : Prop :=
  forall s,
    m_relation m s = [] \/
    exists s', m_relation m s = [s'].

(** What it means to be complete *)
Definition Complete (m : t) : Prop :=
  forall s a, exists s',
    m $ s -[a]-> s'.


(** ** Finite Traces, Paths and Words *)

(** A finite path is a list of labels and states *)
Definition fin_path := list (A * S).

(** A finite trace is a list of states *)
Definition fin_trace := list S.

(** A finite word is a list of labels *)
Definition fin_word := list A.

(** What it means to be a valid finite path in 
    a graph.
*)
Inductive FinPath (m : t) : S -> fin_path -> S -> Prop :=
  | fin_path_empty_ x : FinPath m x [] x
  | fin_path_cons_ x a y p z :
    m $ x -[a]-> y ->
    FinPath m y p z ->
    FinPath m x ((a, x)::p) z.

Instance FinPath_lsteps_op : LstepsOp t S (list (A * S)) := FinPath.

(** The set of valid pathes of a graph. *)
Definition Pathes (m : t) (s : S) : pset fin_path :=
  fun p => exists s', m $ s -[p]->* s'.

(** What it means to be a valid finite trace in
    a graph.
*)
Inductive FinTrace (m : t) : S -> fin_trace -> S -> Prop :=
  | fin_trace_empty_ x : FinTrace m x [] x
  | fin_trace_cons_ x y t z :
    m $ x --> y ->
    FinTrace m y t z ->
    FinTrace m x (x::t) z.

Instance FinTrace_lsteps_op : LstepsOp t S (list S) := FinTrace.

(** The set of valid traces of a graph. *)
Definition Traces (m : t) (s : S) : pset fin_trace :=
  fun t => exists s', m $ s -[t]->* s'.

(** What it means to be a finite word starting in 
    an automata.
*)
Inductive FinWord (m : t) : S -> fin_word -> Prop :=
  | fin_word_empty_ x : FinWord m x []
  | fin_word_cons_ x a y w:
    m $ x -[a]-> y ->
    FinWord m y w ->
    FinWord m x (a::w).

(** The set of valid (finite) words starting in a given state
    of an automata. *)
Definition Words (m : t) (s : S) : pset fin_word :=
  fun w => FinWord m s w.

(** The language of an automata. *)
Definition Language (m : t) : pset fin_word :=
  fun w => exists s, In s (m_initial m) /\ FinWord m s w.

Theorem FinTrace_FinPath:
  forall m x t y,
    FinTrace m x t y ->
    exists p, FinPath m x p y.
Proof.
  intros m x t y Ht.
  induction Ht.
  - repeat econstructor.
  - destruct IHHt as (p' & Hp').
    destruct H as (a & Ha).
    exists ((a, x)::p').
    econstructor; eauto.
Qed.

Definition to_trace (p : fin_path) : fin_trace :=
  List.map (fun '(x, y) => y) p.
Coercion to_trace : fin_path >-> fin_trace.

Definition to_word (p : fin_path) : fin_word :=
  List.map (fun '(x, y) => x) p.
Coercion to_word : fin_path >-> fin_word.

Theorem FinPath_FinTrace:
  forall m x p y,
    FinPath m x p y ->
    FinTrace m x p y.
Proof.
  intros. induction H; subst.
  - econstructor.
  - simpl. repeat econstructor; eauto.
Qed.

Theorem FinPath_FinWord:
  forall m x p y,
    FinPath m x p y ->
    FinWord m x p.
Proof.
  intros m x t y Hp.
  induction Hp.
  - repeat econstructor.
  - econstructor; eauto.
Qed.

Theorem FinWord_FinPath:
  forall m x w,
    FinWord m x w ->
    exists p y, FinPath m x p y.
Proof.
  intros m x w Hw.
  induction Hw.
  - repeat econstructor.
  - destruct IHHw as (p & z & Hp).
    exists ((a, x)::p), z.
    econstructor; eauto.
Qed.

End Model.