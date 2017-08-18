
Inductive bool : Type :=
  | true : bool
  | false : bool.

Definition negb (b:bool) : bool :=
  match b with 
      | true => false 
      | false => true
  end.

Definition andb (b1:bool) (b2:bool) : bool := 
  match b1 with
      | true => b2
      | false => false
  end.

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
   | true => true
   | false => b2
end.  

Example test_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.

Example test_orb2: (orb false false) = false.
Proof. simpl. reflexivity. Qed.

Example test_orb3: (orb false true) = true.
Proof. simpl. reflexivity. Qed.

Example test_orb4: (orb true true) = true.
Proof. simpl. reflexivity. Qed.

Infix "&&" := andb.
Infix "||" := orb.

Example test_orb5: false || false || true = true.
Proof. simpl. reflexivity. Qed.

Example test_negb: (negb true) = false.
Proof. simpl. reflexivity. Qed.

Definition nandb (b1:bool) (b2:bool) : bool :=
   match b1 with
       | true => (negb b2)
       | false => true
   end.

Example test_nandb1 : (nandb true false) = true.
Proof. simpl. reflexivity. Qed.

Example test_nandb2 : (nandb false false) = true.
Proof. simpl. reflexivity. Qed.

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  andb (andb (b1) (b2)) b3.

Example test_andb31: (andb3 true true true) = true.
Proof. unfold andb3. simpl. reflexivity. Qed.

Example test_andb32: (andb3 false true true) = false.
Proof. unfold andb3. simpl. reflexivity. Qed.

Example test_andb33: (andb3 true false true ) = false.
Proof. unfold andb3. simpl. reflexivity. Qed.

Example test_andb34: (andb3 true true false) = false.
Proof. unfold andb3. simpl. reflexivity. Qed.

Check true.
Check (negb true).

Module Playground1.

Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

Definition pred (n : nat) : nat :=
  match n with 
      | O => O
      | S n' => n'
  end.

End Playground1.

Definition minustwo (n : nat) : nat :=
  match n with
      | O => O
      | S O => O
      | S (S n') => n'
end.

Check (S (S (S (S O)))).

Fixpoint evenb (n:nat) : bool :=
  match n with
      | O => true
      | S O => false
      | S (S n') => evenb n'
end.

Definition oddb (n:nat) : bool := negb (evenb n).

Example test_oddb1 : oddb 1 = true.
Proof. simpl. reflexivity. Qed.

Example test_oddb4 : oddb 4 = false.
Proof. simpl. reflexivity. Qed.

Module Playground2.

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
      | O => m
      | S n' => S (plus n' m)
end.

Compute (plus 3 2).

Fixpoint mult (n m : nat) : nat :=
match n with
| O => O
| S n' => plus m (mult n' m)
end.

Example test_mult1 : (mult 3 3 ) = 9.
Proof. simpl. reflexivity. Qed.


Fixpoint minus (n m : nat) : nat :=
match n, m with
| O, _ => O
| S _, O => n
| S n', S m' => minus n' m'
end.

End Playground2.

Fixpoint exp (base power : nat) : nat :=
  match power with
      | O => S O
      | S p => mult base (exp base p)
  end.

Fixpoint factorial (n:nat) : nat :=
  match n with
      | O => 1
      | S n' => n * factorial(n')
  end.

Example test_fact3: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.

Example test_fact5: factorial 5 = (mult 10 12).
Proof. simpl. reflexivity. Qed.


Notation "x + y" := (plus x y)
                         (at level 50, left associativity)
                         : nat_scope.
Notation "x - y" := (minus x y)
                      (at level 50, left associativity)
                      : nat_scope.

Notation "x * y" := (mult x y)
                      (at level 40, left associativity)
                      : nat_scope.

(* return true if n and m are equal *)
Fixpoint beq_nat (n m : nat) : bool :=
  match n with 
      | O => match m with
               | O => true
               | S m' => false
             end
     | S n' => match m with
                   | O => false
                   | S m' => beq_nat n' m'
               end
  end.

Fixpoint leb (n m : nat) : bool :=
  match n with
      | O => true
      | S n' => 
        match m with
            | O => false
            | S m' => leb n' m'
        end
 end.

Example test_leb1 : (leb 2 2) = true.
Proof. simpl. reflexivity. Qed.

Example test_leb2 : (leb 2 4) = true.
Proof. simpl. reflexivity. Qed.

Example test_leb3 : (leb 4 2) = false.
Proof. simpl. reflexivity. Qed.

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

Theorem plus_1_neq_0_firsttry : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
intros n.
destruct n as [| n'].
simpl.
reflexivity.
reflexivity.
Qed.

Theorem andb_commutative : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b.
- destruct c.
 + reflexivity.
 + reflexivity.
- destruct c.
 + reflexivity.
 + reflexivity.
Qed.

Theorem andb_commutative' : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b.
 { destruct c.
   { reflexivity. }
   { reflexivity. } }
 { destruct c.
   { reflexivity. }
   { reflexivity. } }
Qed.

Theorem andb3_exchange : forall b c d, andb (andb b c) d = andb (andb b d) c.
Proof.
  intros b c d. destruct b.
  - destruct c.
    { destruct d.
      - reflexivity.
      - reflexivity. }
    { destruct d.
      - reflexivity.
      - reflexivity. }
    - destruct c.
      { destruct d.
        - reflexivity.
        - reflexivity.
      }
      { destruct d.
        - reflexivity.
        - reflexivity.
      }
Qed.

Theorem identity_fn_applied_twice :
  forall f : bool -> bool,
    (forall x : bool, f x = x) -> forall b : bool, (f (f b) = b).
intros.
rewrite -> H.
apply H.
Qed.



Theorem andb_eq_orb :
  forall b c : bool,
  (andb b c = orb b c) -> b = c.
intro b.
destruct c.
destruct b.
simpl.
(*reflexivity.*)
intros.
auto.
intro.
intros.
auto.
destruct b.
intros.
auto.
intro.
auto.
Qed.


Print andb_eq_orb.

Inductive nat : Type := 
  | O : nat
  | S : nat -> nat.

Inductive binary_number : Type :=
  | Zero : binary_number
  | Twice : binary_number -> binary_number
  | OneMoreThanTwiceABinaryNumber : binary_number -> binary_number.

Definition incr( b:binary_number ) : binary_number := 
  match b with
      | Zero      => OneMoreThanTwiceABinaryNumber(Zero)
      | Twice n1  => OneMoreThanTwiceABinaryNumber(b)
      | OneMoreThanTwiceABinaryNumber n1 => match n1 with
                                                | Zero => Twice n1
                                                | Twice n2 => OneMoreThanTwiceABinaryNumber n1
                                                | OneMoreThanTwiceABinaryNumber n2 => Twice n1
                                            end
  end.

Fixpoint myeq_nat n m  :=
  match n, m with
    | O, O => true
    | O, S _ => false
    | S _, O => false
    | S n1, S m1 => myeq_nat n1 m1
  end.

Theorem myeq_nat_eq : forall n, (myeq_nat n n) = true.
Proof.
  induction n.
  simpl.
  reflexivity.
  simpl.
  assumption.
Qed.

Example test_incr1: incr(Zero) = OneMoreThanTwiceABinaryNumber(Zero).
Proof. simpl. reflexivity. Qed.

Example test_incr2: incr( OneMoreThanTwiceABinaryNumber(Zero)) = Twice(Zero).
Proof. simpl. reflexivity. Qed.

Example test_incr3: incr(Twice(Zero) ) = OneMoreThanTwiceABinaryNumber (Twice(Zero)).
Proof. simpl. reflexivity. Qed.




                                                                                