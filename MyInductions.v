Section MyInductions.

Require Import Coq.Classes.SetoidClass.

(* /build/HACMS/AMAS-CD/Software Drop DEC 15/amas_software_src *)

Theorem plus_n_0_firsttry : forall n : nat, n = n + 0.
Proof.
  intros n.
  simpl.
Abort.

Theorem plus_n_0_secondtry : forall n : nat, n = n + 0.
Proof.
  intros n. destruct n as [| n'].
  reflexivity.
simpl.  
Abort.

Theorem plus_n_0 : forall n : nat, n = n + 0.
Proof.
  intros n. induction n as [| n' IHn'].
reflexivity.
simpl. rewrite <- IHn'. reflexivity. Qed.

Theorem mult_0_r : forall n : nat, n * 0 = 0.
Proof.
  intros n. induction n as [|n' IHn'].
  reflexivity.
  simpl. 
  assumption. 
Qed.

Theorem plus_n_Sm : forall n m : nat,  S (n + m) = n + (S m).
Proof.
  intros.
  induction n as [|n' IHn'].
  induction m as [|m' IHm'].
  simpl. reflexivity.
  simpl. reflexivity.
  induction m as [|m' IHm'].  
  simpl. rewrite <- IHn'. reflexivity.
  simpl. rewrite <- IHn'. reflexivity.
Qed.

Print plus_n_Sm.

Theorem plus_comm : forall n m : nat, n + m = m + n.
Proof.
  intros.
  induction n as [|n' IHn'].
  induction m as [|m' IHm'].
  auto.
  simpl.
  apply plus_n_0.
  simpl.
  rewrite <- plus_n_Sm.
  rewrite <- IHn'.
  reflexivity.
Qed.

Print plus_comm.

Theorem plus_assoc : forall n m p : nat, n + (m + p) = (n + m) + p.
Proof.
  intros.
  induction n as [|n' IHn'].
  induction m as [|m' IHm'].
  simpl.
  reflexivity.
  induction p as [|p' IHp'].
  simpl.
  reflexivity.
  simpl.
  reflexivity.
  induction p as [|p' IHp'].
  induction m as [|m' IHm'].
  simpl.
  auto.
  simpl.
  rewrite <- plus_n_0.
  simpl.
  rewrite <- plus_n_0.
  reflexivity.
  induction m as [|m' IHm'].
  rewrite <- plus_n_0.
  reflexivity.
  simpl.
  rewrite <- IHn'.
  reflexivity.  
Qed.

Print plus_assoc.

Fixpoint double (n:nat) :=
  match n with
| O => O
| S n' => S (S (double n'))
 end.

Compute double (100).


Example test_double2 : 1 + double (2) = 1+2+2.
Proof. simpl. reflexivity. Qed.

(*
Lemma double_plus1 : forall n, double (S n) = S ( S ( double n)).
Proof.
intros.
simpl.
induction n.
simpl.
reflexivity.
f_equal.
rewrite.
*)

 
Lemma double_plus : forall n, double n = n + n.
Proof.
  intros.
  induction n as [|n' IHn'].
  simpl.
  reflexivity.
  simpl.
  rewrite -> IHn'.
  rewrite -> plus_n_Sm.
  reflexivity.
Qed.

(* Proof within Proofs *)

Theorem mult_0_plus' : forall n m : nat, (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n). { reflexivity. }
  rewrite -> H.
  reflexivity.
Qed.

Theorem plus_rearrange : forall n m p q : nat, (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
  { rewrite -> plus_comm. reflexivity. }
  rewrite -> H. reflexivity. Qed.

Theorem plus_swap : forall n m p : nat, n + (m + p) = m + (n + p).
Proof.
  intros.
  rewrite plus_assoc.
  rewrite plus_assoc at 1.
  assert (H: n + m = m + n).
  { rewrite -> plus_comm. reflexivity. }
  rewrite <- H.
  reflexivity.
Qed.

Theorem mult_0_elm : forall n : nat, n * 0 = 0.
Proof.
  auto.
Qed.

Theorem mult_0_elm2: forall n : nat, 0 * n = 0.
  intros.
  auto.
Qed.

Theorem mult_1_elm : forall n : nat, n * 1 = n.
Proof.
  intro.
  induction n as [| n' IHn'].
  rewrite mult_0_elm2 at 1.
  reflexivity.
  rewrite <- IHn'.
  destruct n' as [| n'' IHn''].
  auto.
  rewrite -> IHn'.
  simpl.
  rewrite IHn' at 1.
  reflexivity.
Qed.

Theorem mult_1_elm2 : forall n : nat, n = n *1.
Proof.
  intros.
  induction n as [| n' IHn'].
  rewrite mult_0_elm2 at 1.
  reflexivity.
  destruct n' as [| n'' IHn''].
  simpl.
  reflexivity.
  rewrite -> mult_1_elm.
  reflexivity.
Qed.


Theorem remove_plus : forall a b : nat, (S(a) = S(b)) -> (a = b).
Proof.
intros.
induction a as [|a0 IHa0].
induction b as [|b0 IHb0].
reflexivity.
destruct b0.
auto.
auto.
auto.
Qed.

Theorem remove_plus2 : forall a b : nat, a = b -> (S(a) = S(b)).
Proof.
intros.
auto.
Qed.

Lemma s_b_eq_b_p_1 : forall b : nat, (S b) = b +1.
  intros.
  induction b as [|bo IHM0].
  simpl.
  reflexivity.
  simpl.
  rewrite <- IHM0 at 1.
  reflexivity.
Qed.

Lemma un_p_b_p_un : forall b : nat, 1+b+1 = b+2.
Proof.
  intros.
  replace (1+b) with (b+1).
  rewrite <- plus_assoc.
  replace (1+1) with 2.
  reflexivity.
  simpl.
  reflexivity.
  rewrite plus_comm.
  reflexivity.
Qed.


(*
Theorem start_distribution : forall a b :nat, (S(b)*a) = a+a*b.
Proof.
intros.
induction a as [|x IHa0].
simpl.     
rewrite ->mult_0_r.
reflexivity.
induction b as [|y IHb0].
simpl.
replace (x * 0) with 0.
reflexivity.
rewrite ->mult_0_r.
reflexivity.
simpl.

Qed.
*)


Theorem start_distribution3 : forall a b :nat,  (a*S(b)) = a+a*b.
Proof.
intros.
simpl.
induction a as [|x IHa0].
simpl.     
reflexivity.
simpl.
induction b as [|y IHb0].
simpl.
rewrite <- mult_1_elm2.
rewrite <- mult_1_elm.
replace (x *0) with 0.
replace (x+0) with x.
rewrite -> mult_1_elm.
reflexivity.
rewrite <- plus_n_0.
reflexivity.
auto.
intros.
replace (x * S (S y)) with (x + x * (S y)).
apply remove_plus2.
rewrite plus_swap.
reflexivity.
Qed.


Theorem start_distribution2 : forall a b : nat, (S(a))*(S(b)) = a*b+a+b+1.
Proof.
intros.
simpl.
set (b + a * (S b)).
simpl.
rewrite -> s_b_eq_b_p_1.
unfold n.
rewrite start_distribution3.
rewrite ->plus_swap.
rewrite <-plus_swap.
replace (b + (a + a*b)) with (a*b+a+b).
reflexivity.
set (a + a *b).
set (a*b+a).
rewrite -> plus_comm.
unfold n0.
unfold n1.
set (a*b).
rewrite -> plus_swap.
rewrite <- plus_swap.
replace (n2 + a) with (a + n2).
reflexivity.
rewrite <- plus_comm.
reflexivity.
Qed.


Theorem mult_comm3 : forall m n : nat,  m * n = n *m.
Proof.
intros.
induction m as [| x0 IHm0 ].
simpl.
rewrite -> mult_0_elm.
reflexivity.
induction n as [| y0 IHn0 ].
rewrite -> mult_0_elm.
simpl.
reflexivity.
simpl.
rewrite -> IHm0.
simpl.
rewrite -> start_distribution3.
rewrite -> plus_swap.
reflexivity.
Qed.

Theorem mult_comm4 : forall m n : nat,  m * n = n *m.
Proof.
intros.
induction m as [| x0 IHm0 ].
simpl.
rewrite -> mult_0_elm.
reflexivity.
simpl.
rewrite start_distribution3.
rewrite IHm0.
simpl.
reflexivity.
Qed.

(*
Inductive  binary_number : Type :=
  | Zero : binary_number
  | Twice : binary_number -> binary_number
  | MoreThanTwice : binary_number -> binary_number.

Check binary_number_ind.

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

Fixpoint nat_to_bin(n : nat) : binary_number :=
  match n with
 | 0 => Zero
 | S n1 => incr(nat_to_bin(n1))
  end.

Fixpoint normalize(n : binary_number) : binary_number :=
  match n with
    | Zero => Zero
    | MoreThanTwice x => MoreThanTwice (normalize (x))
    | Twice x => match normalize(x) with
                   | Zero => Zero
                   | _ =>  Twice (normalize(x))
                 end

  end.

(* Fixpoint normalize2(n : binary_number) : binary_number := *)
(*   match n with *)
(*     | Zero => Zero *)
(*     | Twice x => ( if (normalize(x) = Zero) then *)
(*                    Zero *)
(*                  else *)
(*                    (Twice normalize(x)) *)
(*                  ) *)
(*     | MoreThanTwice x => MoreThanTwice (normalize (x)) *)
(*   end. *)


Definition z := (MoreThanTwice(Twice(MoreThanTwice(Twice((Twice(Twice((Zero))))))))).

Definition zn := normalize(z).

Print zn.
Compute zn.
Definition z1 := bin_to_nat(z).

Definition z2 := bin_to_nat(normalize(z)).
  
Print z1.
Print z2.

Compute(bin_to_nat(z)).
Compute(bin_to_nat(normalize(z))).


Theorem normalize_Id : forall n : binary_number,
                         (normalize(normalize(n)) = normalize(n)).
Proof.
intros.
simpl.
induction n.
simpl.
reflexivity.
simpl.
admit.
admit.
Qed.


Example test_normalize : nat_to_bin(bin_to_nat(normalize(z))) = normalize(z).
Proof.
simpl.
unfold z.
reflexivity.
Qed.


Definition z3 := (Twice (Twice(Zero))).

Example test_normalize3 : nat_to_bin(bin_to_nat(normalize(z3))) = normalize(z3).
Proof.
simpl.
reflexivity.
Qed.

Check z.

Definition v := (Twice(Zero)).
Definition vn := (normalize(v)).
Compute v.
Compute vn.

Definition v2 := (Twice(Twice(MoreThanTwice(Zero)))).
Definition v2n := (normalize(v2)).
Compute v2.
Compute v2n.

Definition w := bin_to_nat(v).
Definition zn2 := normalize(z).
Print v.
Print z.
Print zn.
Compute z.
Compute zn.

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

Theorem bin_to_nat_pres_incr : forall n : binary_number, bin_to_nat(n) = (bin_to_nat(n)).
Proof.
intros.
induction n as [|n1 IHn1|n2 IHn2].
simpl.
reflexivity.
simpl.
reflexivity.
simpl.
reflexivity.
Qed.


Theorem toto : forall n : binary_number, nat_to_bin(bin_to_nat(normalize(n))) = normalize(n) -> Twice(nat_to_bin(bin_to_nat(normalize(n)))) = Twice((normalize(n))).
Proof.
intros.
induction n as [| m IHm0 | n1 IHm1 ].
simpl.
reflexivity.
destruct (normalize (Twice m)).
simpl.
reflexivity.
rewrite -> H.
reflexivity.
rewrite -> H.
simpl.
reflexivity.
rewrite -> H.
reflexivity.
Qed.


(*Theorem forall n : binary_number, normalize(n) *)
(*
Theorem incr_bin_to_nat_pres : forall n : binary_number, nat_to_bin(bin_to_nat(normalize(n)))= normalize(n).
Proof.
intros.
induction n as [| m IHm0 | n1 IHm1 ].
replace (normalize Zero) with (Zero).
simpl.
reflexivity.
simpl.
reflexivity.
simpl.
Qed.

*)
*)

End MyInductions.
