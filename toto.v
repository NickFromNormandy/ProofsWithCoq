
(*
Check 0.
Check nat.

Section Declaration.
Variable n : nat.
Check gt.
Definition one := (S 0).
Definition two : nat := S one.
Definition three := S two : nat.
Definition double (m:nat) := plus m m.

Reset Initial.

Section Minimal_Logic.

Variable A B C : Prop.
Check (A -> B).
Goal (A-> B->C) -> (A ->B) -> A -> C.
intro H.
intros H' HA.
apply H.
exact HA.
apply H'.
assumption.
Save trivial_lemma.

Lemma distr_impl : (A->B->C) -> (A ->B) -> A -> C.

intros.
apply H; [ assumption | apply H0; assumption].
Save.

Lemma distr_impl2 : (A -> B -> C) -> (A->B) -> A -> C.
auto.
Abort.

Lemma and_commutative : A /\ B -> B /\ A.
intro.
elim H.
split.
assumption.
assumption.
Qed.

Lemma or_commutative : A \/ B -> B \/ A.
intro H.
elim H.
intro HA.
clear H.
right.
assumption.
intro HB.
clear H.
left.
assumption.
Qed.

Print or_commutative.
Print or_ind.
Print or_intror.
Print or_introl.

Lemma distr_and : A -> B /\ C -> (A -> B) /\ (A -> C).
tauto.
Qed.
Print distr_and.

Require Import Classical.
Check NNPP.
Lemma Pierce : ((A -> B) -> A) -> A.
apply NNPP; tauto.
Qed.

*)
