Class InOp (x X : Type) :=
  in_op_ : x -> X -> Prop.

Notation "x ∈ X" := (in_op_ x X) (at level 39).

Class CupOp (A : Type) :=
  cup_op_ : A -> A -> A.

Notation "x ∪ y" := (cup_op_ x y) (at level 40).

Class CapOp (A : Type) :=
  cap_op_ : A -> A -> A.

Notation "x ∩ y" := (cap_op_ x y) (at level 40).

Class SubsetOp (A : Type) :=
  subset_op_ : A -> A -> Prop.

Notation "x ⊂ y" := (subset_op_ x y) (at level 39).

Class SubseteqOp (A : Type) :=
  subseteq_op_ : A -> A -> Prop.

Notation "x ⊆ y" := (subseteq_op_ x y) (at level 39).

Class StepOp (A B : Type) :=
  step_op_ : A -> B -> B -> Prop.

Notation "x $ y --> z" := (step_op_ x y z) (at level 39).

Class StepsOp (A B : Type) :=
  steps_op_ : A -> B -> B -> Prop.

Notation "x $ y ->* z" := (steps_op_ x y z) (at level 39).

Class LstepOp (A B C : Type) :=
  lstep_op_ : A -> B -> C -> B -> Prop.

Notation "w $ x -[ y ]-> z" := (lstep_op_ w x y z) (at level 39).

Class LstepsOp (A B C : Type) :=
  lsteps_op_ : A -> B -> C -> B -> Prop.

Notation "w $ x -[ y ]->* z" := (lsteps_op_ w x y z) (at level 39).