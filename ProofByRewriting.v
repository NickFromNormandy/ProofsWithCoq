

(*
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

Theorem mult_0_plus : forall n m : nat,
(0 + n) * m = n *m.
intros n m.
rewrite -> plus_0_n.
reflexivity. Qed.

*)
