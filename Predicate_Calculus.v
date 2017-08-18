(*

Section Predicate_Calculus.

Variables P Q : nat -> Prop.
Variables R : nat -> nat -> Prop.

Lemma PQR :
  forall x y : nat, (R x x -> P x -> Q x) -> P x -> R x y -> Q x.

intros.
generalize H0.
cut (R x x); trivial.
Abort.

*)

