(*
Inductive  binary_number : Type :=
  | Zero : binary_number
  | Twice : binary_number -> binary_number
  | MoreThanTwice : binary_number -> binary_number.


Fixpoint incr(n : binary_number ) : binary_number :=
  match n with
    | Zero => MoreThanTwice Zero
    | Twice x => MoreThanTwice x
    | MoreThanTwice x => Twice (incr x)
  end.


Fixpoint bin_to_nat(n : binary_number) : nat :=
  match n with
 | Zero => 0
 | Twice x => 2*(bin_to_nat(x))
 | MoreThanTwice(x) => 1+2*bin_to_nat(x)
  end.

Definition a := Zero.
Definition b := incr(a).
Compute a.

Example test_incr1 : bin_to_nat(b) = 1.
Proof.
simpl.
reflexivity.
Qed.


Example test_incr2 : bin_to_nat(incr(b)) = 2.
Proof.
simpl.  
reflexivity.
Qed.

Example test_incr3 : bin_to_nat(incr(incr(incr(a)))) = 3.
Proof.
simpl.
reflexivity.
Qed.

Example test_incr4 : bin_to_nat(incr(incr(incr(incr(a))))) = 4.
Proof.
simpl.
reflexivity.
Qed.

Example test_incr5 : bin_to_nat(incr(incr(incr(incr(incr(a)))))) = 5.
Proof.
simpl.
reflexivity.
Qed.

Example test_incr6 :  bin_to_nat(incr(incr(incr(incr(incr(incr(a))))))) = 6.
Proof.
simpl.
reflexivity.
Qed.


Compute bin_to_nat (MoreThanTwice(Twice (Twice Zero))).

Compute bin_to_nat (Twice(Twice (Twice Zero))).

Compute bin_to_nat (Zero).

Compute S(S(S(S O))).

Theorem bin_to_nat_pres_incr : forall n : binary_number, bin_to_nat(incr n) = S(bin_to_nat(n)).
Proof.
intros.
induction n as [|n1 IHn1|n2 IHn2].
simpl.
reflexivity.
simpl.
reflexivity.
simpl.
rewrite -> IHn2.
simpl.
replace (bin_to_nat n2 + 0) with (bin_to_nat n2).

*)
