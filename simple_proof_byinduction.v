
Lemma plus_n_0 : forall n:nat, n = n + 0.
intro n; elim n.
simpl.
auto.
simpl; auto.
Qed.
Print plus_n_0.
Print eq_refl.
Hint Resolve plus_n_0.

Lemma plus_n_S : forall n m : nat, S (n + m) = n + S m.
simple induction n; simpl; auto.
Qed.

Lemma plus_com : forall n m : nat, n+m = m+n.
simple induction m; simpl; auto.
intros m' E; rewrite <- E; auto.
Qed.

Print plus_com.
Print nat_ind.

Definition Is_S (n:nat) := match n with 
| 0 => False
| S p => True
end.

Lemma S_Is_S : forall n:nat, Is_S (S n).
simpl; trivial.
Qed.

Lemma no_confusion : forall n:nat, 0 <> S n.
red; intros n H.
change (Is_S 0).
rewrite H; trivial.
simpl; trivial.
Qed.

Theorem plus_id_example : forall n m :nat,
                            n = m -> n+n = m + m.

Proof.
intros.
rewrite -> H.
reflexivity.
Qed.

Theorem plus_id_exercise : forall n m o : nat,
                             n = m -> m = o -> n + m = m + o.
Proof.
intros.
rewrite -> H.
rewrite -> H0.
simpl.
reflexivity.
Qed.

Theorem plus_0_n : forall n : nat, 0 + n = n.
Proof.
  intros n. simpl. reflexivity. Qed.

Theorem mult_0_plus : forall n m : nat,
(0 + n) * m = n *m.
intros n m.
rewrite -> plus_0_n.
reflexivity. Qed.

Theorem mult_S_1 : forall n m : nat,
  m = S n -> m * (1 + n) = m * m.
Proof.
intros.
rewrite -> H.
reflexivity.
Qed.

(*
Theorem plus_1_neq_0_firsttry : forall n : nat,
  beq_nat (n + 1) 0 = false.
*)