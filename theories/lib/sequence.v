(** * Nat-indexed infinite sequences *)

Require Import Automatik.lib.operators.
Require Import Arith List.
Import ListNotations.

Section Sequence.

Definition t (A : Type) : Type :=
  nat -> A.

Definition nth {A : Type} (s : t A) (i : nat) : A :=
  s i.

Definition equ {A : Type} (s1 s2 : t A) : Prop :=
  forall i, s1 i = s2 i.

Definition shift {A : Type} (s : t A) (i : nat) : t A :=
  fun x => s (i + x).

Lemma shift_assoc:
  forall A (s : @t A) i j,
    equ (shift (shift s i) j) (shift s (i + j)).
Proof.
  intros * n.
  unfold shift.
  now rewrite Nat.add_assoc.
Qed.

Fixpoint range {A : Type} (s : t A) (i j : nat) {struct j} : list A :=
  if j <? i then []
  else if i =? j then [s i]
  else match j with
  | 0 => []
  | S j' => (range s i j') ++ [s j]
  end.

Definition repeat {A : Type} (a : A) (l : list A) : t A :=
  fun i => List.nth (i mod (List.length l)) l a.

End Sequence.

Instance nth_op (A : Type) : NthOp (t A) A := nth.
Instance shift_op (A : Type) : ShiftOp (t A) A := shift.
Instance range_op (A : Type) : RangeOp (t A) A (list A) := range.
Instance equ_op (A : Type) : EquOp (t A) := equ.
