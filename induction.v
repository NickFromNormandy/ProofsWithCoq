

Inductive nat : Set :=  | O : nat | S : nat -> nat.

Definition prim_rec := nat_rec (fun i : nat => nat).

Definition addition (n m : nat) := prim_rec m (fun p rec:nat => S rec) n.

Eval compute in (addition (S (S O)) (S (S (S O)))).

Fixpoint plus (n m:nat) {struct n} : nat :=
  match n with 
    | O => m
    | S p => S (plus p m)
  end.



Inductive bool : Set := true | false.
Check bool_ind.
Check bool_rec.
Check bool_rect.

Lemma duality : forall b:bool, b =true \/ b = false.
intro b.
elim b.
left; trivial.
right; trivial.
Qed.

