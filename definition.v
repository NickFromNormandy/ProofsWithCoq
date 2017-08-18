
Variable U : Type.

Definition set := U -> Prop.

Definition element (x:U) (S:set) := S x.

Definition subset (A B : set) := forall x:U, element x A -> element x B.

Definition transitive (T:Type) (R:T -> T -> Prop) := forall x y z: T, R x y -> R y z -> R x z.

Lemma subset_transitive : transitive set subset.
unfold transitive.
unfold subset.
intro A.
intro B.
intro C.
intro AIsIncludedInB.
intro BIsIncludedInC.
intro MySet.
intro AIsIncludedInC.
apply BIsIncludedInC.
apply AIsIncludedInB.
assumption.
Qed.

Print U.
Print element.
Print subset.
Print transitive.
Print subset_transitive.