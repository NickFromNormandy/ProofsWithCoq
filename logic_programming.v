
Inductive le (n:nat) : nat -> Prop :=
  | le_n : le n n 
  | le_S : forall m:nat, le n m -> le n (S m).

Check le.
Check le_ind.

Lemma le_n_S : forall n m : nat, le n m -> le (S n) (S m).
intros n m n_le_m.
elim n_le_m.
apply le_n; trivial.
intros; apply le_S;trivial.
Restart.
Hint Resolve le_n le_S.
simple induction 1;auto.

Qed.

Print le_n_S.

Lemma tricky : forall n : nat, le n 0 -> n = 0.
intros n H; inversion_clear H.
trivial.
Qed.
