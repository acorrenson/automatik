Require Import Automatik.pset.
Require Import Automatik.operators.

Definition P : pset nat := fun x => x = 1.
Definition Q : pset nat := fun x => x = 2.
Definition R : pset nat := P ∩ Q.