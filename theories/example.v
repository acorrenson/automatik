Require Import Automatik.lib.pset.
Require Import Automatik.lib.sequence.
Require Import Automatik.lib.operators.
Require Import List.
Import ListNotations.

Definition P : pset nat := fun x => x = 1.
Definition Q : pset nat := fun x => x = 2.
Definition R : pset nat := P ∩ Q.

Definition s1 : sequence.t nat := fun x => x + 1.
Definition s2 : sequence.t nat := fun x => x + 2.
Definition s3 := s1⟨1+⟩.

Goal s2 ≡ s3.
Proof.
  unfold s2, s3. unfold s1.
  intros i. cbn.
  Require Import Lia.
  lia.
Qed.

Goal s1⟨1…3⟩ = [2; 3 ; 4].
Proof.
  reflexivity.
Qed.

Definition s4 := sequence.repeat 0 [1; 2; 3].

Goal s4⟨0…5⟩ = [1; 2; 3; 1; 2; 3].
Proof.
  reflexivity.
Qed.