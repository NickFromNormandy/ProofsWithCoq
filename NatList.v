
Require Import Coq.Classes.SetoidClass.
Require Import MyInductions.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Peano_dec.


Module NatList.

Inductive natprod : Type :=
| pair : nat -> nat -> natprod.

Check (pair 3 5).

Definition fst(p : natprod) : nat :=
  match p with
      | pair x y => x
end.

Definition snd(p : natprod) : nat :=
  match p with
      | pair x y => y
end.

Compute (fst (pair 3 5)).

Notation "( x , y )" := (pair x y).

Compute (fst(3,5)).

Definition fst' (p : natprod) : nat :=
  match p with 
      | (x,y) => x
  end.

Definition snd' (p : natprod) : nat :=
  match p with
      | (x,y) => y
  end.

Definition swap_pair(p : natprod) : natprod :=
  match p with
      | (x,y) => (y,x)
  end.

Theorem surjective_pairing' : forall (n m : nat),
    (n,m) = (fst(n,m), snd(n,m)).
Proof.
reflexivity.
Qed.


Theorem surjective_pairing_stuck : forall (p : natprod), p = (fst p, snd p).
Proof.
  intros p.
  destruct p as [n m].
  simpl.
  reflexivity.
Qed.

Theorem snd_fst_is_swap : forall (p : natprod), (snd p, fst p) = swap_pair p.
Proof.
  intros p.
  destruct p as [n m].
  simpl.
  reflexivity.
Qed.

Theorem fst_swap_is_snd : forall (p : natprod), fst(swap_pair p) = snd p.
Proof.
  intros p.
  destruct p as [n m].
  simpl.
  reflexivity.
Qed.

Inductive natlist : Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

Definition mylist := cons 1 (cons 2 (cons 3 nil)).

Notation "x :: l" := (cons x l) (at level 60, right associativity).

Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Definition mylist1 := 1 :: (2 :: (3 :: nil)).
Definition mylist2 := 1 :: 2 :: 3 :: nil.
Definition mylist3 := [1;2;3].

Notation "x + y" := (plus x y)
                      (at level 50, left associativity).

Fixpoint repeat (n count : nat) : natlist :=
  match count with
      | 0 => nil
      | S count' => n :: (repeat n count')
  end.

Fixpoint length (l : natlist) : nat :=
  match l with
      | nil => 0
      | h :: t => S (length t)
end.

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
      | nil => l2
      | h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y)
                       (right associativity, at level 60).

Example test_app1: [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity. Qed.

Example test_app2: nil ++ [4;5] = [4;5].
Proof. reflexivity. Qed.

Example test_app3: [1;2;3] ++ nil = [1;2;3].
Proof. reflexivity. Qed.

Definition hd (default : nat) (l : natlist) : nat :=
  match l with
      | nil => default
      | h :: t => h
  end.

Definition tl (l:natlist) : natlist := 
  match l with
    | nil => nil
    | h :: t => t
  end.

Example test_hd1 : hd 0 [1;2;3] = 1.
Proof. reflexivity. Qed.

Example test_hd2 : hd 0 [] = 0.
Proof. reflexivity. Qed.

Example test_tl : tl [1;2;3] = [2;3].
Proof. reflexivity. Qed.

Fixpoint nonzeros (l : natlist) : natlist :=
  match l with
    |    nil => nil
    | h :: t => match h with
                  | 0 => (nonzeros t)
                  | _ => h::(nonzeros t)
                end
  end.


Example test_nonzeros: nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof. reflexivity. Qed.

Fixpoint odd(n : nat) :=
  match n with
    | 0 => false
    | 1 => true
    | S p => odd(p-1)
  end.

Check odd.

Example tst_odd : odd(31) = true.
Proof. simpl. reflexivity. Qed.

Fixpoint oddmembers (l : natlist) : natlist :=
  match l with
    | nil => nil
    | h :: t => match (odd h) with
                    | true => h::(oddmembers t)
                    | false => (oddmembers t)
                end
  end.

Example test_oddmembers : oddmembers([2;3;4;5;6;7;8;9;10;111;12;0;0;0;0;0;0;0]) = [3;5;7;9;111].
Proof. reflexivity. Qed.

Fixpoint countoddnumbers (l : natlist) : nat :=
  match l with
      | nil => 0
      | h :: t => match (odd h) with
                      | true => 1+(countoddnumbers t)
                      | false => (countoddnumbers t)
                  end
  end.

Example test_countoddnumbers : countoddnumbers [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed.

Example test_coundoddnumbers2 : countoddnumbers [0;2;4] = 0.
Proof. reflexivity. Qed.

Example test_countoddnumbers3 : countoddnumbers nil = 0.      
Proof. reflexivity. Qed.

Fixpoint alternate(l1 l2 : natlist) : natlist :=
  match l1 with
      | nil => l2
      | h1 :: t1 => match l2 with
                    | nil => l1
                    | h2 :: t2 => h1::h2::(alternate t1 t2)
                    end
  end.

Example test_alternate1:
  alternate [1;3;5] [2;4;6] = [1;2;3;4;5;6].
Proof. reflexivity. Qed.

Example test_aternate2:
  alternate [1] [4;5;6] = [1;4;5;6].
Proof. reflexivity. Qed.


Definition bag := natlist.

Check (1=1).

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

Fixpoint count (v : nat) (s:bag) : nat :=
  
  match s with
      | nil => 0
      | h1 :: t1 => (if (myeq_nat v h1) then
                      1+(count v t1)
                    else
                      (count v t1))
                    
  end.

Example test_count1: count 1 [1;2;3;4;1;4;1] = 3.
Proof. reflexivity. Qed.

Definition sum : bag -> bag -> bag := app.

Example test_sum1 : count 1 (sum [1;2;3] [1;4;1]) = 3.                                 
Proof. reflexivity. Qed.

Definition add (v:nat) (s:bag) : bag := (cons v s).

Example test_add1: count 1 (add 1 [1;4;1]) = 3.                                   
Proof. reflexivity. Qed.

Example test_add2 : count 5 (add 1 [1;4;1]) = 0.
Proof. reflexivity. Qed.

Definition member (v:nat) (s:bag) : bool := 
  match (myeq_nat (count v s) 0) with
    |      true => false
    |      false => true
  end.

Example test_member1 : member 1 [1;4;1] = true.
Proof. reflexivity. Qed.

Example test_member2 : member 2 [1;4;1] = false.
Proof. reflexivity. Qed.


Fixpoint remove (v:nat) (s:bag) : bag :=
 match s with
  |   [] => []
  |   h::t => if (myeq_nat v h) then
                (remove v t)
              else
                (h::remove v t)
 end.

Example test_remove1 : remove 1 [1;4;1] = [4].
Proof. reflexivity. Qed.

Theorem nat_p_1 : forall n : nat, S(n) <> 0.
Proof.
intros.
induction n.
auto.
auto.
Qed.

Theorem bag_theorem : forall n : nat, forall b : bag, ((count n (add n b)) <> 0).
Proof.
intros.
simpl.
induction b.
induction n.
simpl.
auto.
induction n.
replace (myeq_nat 1 1) with true.
simpl.
auto.
simpl.
reflexivity.
replace (myeq_nat (S (S n)) (S (S(n)))) with true.
induction n.
simpl.
auto.
set (count (S (S (S n))) []).
apply nat_p_1.
set (S (S n)).
simpl.
rewrite -> myeq_nat_eq.
reflexivity.
rewrite -> myeq_nat_eq.
set (count n (n0 :: b)).
apply nat_p_1.
Qed.

Theorem bag_theorem2 : forall n : nat, forall b : bag, ((count n (add n b)) = S(count n b)).
intros.
simpl.
rewrite -> myeq_nat_eq.
set (count n b).
reflexivity.
Qed.

Theorem nil_app : forall l : natlist, [] ++ l = l.
Proof. reflexivity. Qed.


Theorem tl_length_pred : forall l : natlist, pred (length l) = length(tl l).
Proof.
intros l.
destruct l as [|n l'].
reflexivity.
reflexivity.
Qed.

Theorem app_assoc : forall l1 l2 l3 : natlist,
                      (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
intros l1 l2 l3.
induction l1 as [|n l1' IHl1'].
reflexivity.
simpl. rewrite -> IHl1'. reflexivity. Qed.

Fixpoint rev (l : natlist) : natlist :=
  match l with
    | nil => nil
    | h :: t => rev t ++ [h]
  end.

Example test_rev1 : rev [1;2;3] = [3;2;1].
Proof. reflexivity. Qed.

Theorem rev_length_firsttry : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros.
  induction l as [|n l' IHl'].
  reflexivity.
  simpl.
  rewrite <- IHl'. 
Abort.

Theorem app_length : forall l1 l2 : natlist,
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
intros.
induction l1 as [|n l1' IHl1'].
reflexivity.
simpl.
rewrite -> IHl1'.
reflexivity.
Qed.

Theorem rev_length : forall l : natlist, length (rev l) = length l.
Proof.
intros l.
induction l as [|n l' IHl'].
simpl.
reflexivity.
simpl.
rewrite -> app_length, plus_comm.
rewrite -> IHl'.
reflexivity.
Qed.

Theorem app_nil_r : forall l : natlist, l ++ [] = l.
Proof.
intros.
induction l.
simpl.
reflexivity.
replace ((n::l) ++ []) with (n::(l++[])).
rewrite ->IHl.
reflexivity.
simpl.
reflexivity.
Qed.

Theorem rev_involutive : forall l : natlist,
 rev (rev l) = l.
Proof.
intros.
induction l as [|n l' IHl'].
reflexivity.
simpl.
replace (rev ( rev l' ++ [n])) with (n::(rev (rev l'))).
rewrite -> IHl'.
reflexivity.
set (rev l').
induction n0.
reflexivity.
simpl.
rewrite <- IHn0.
simpl.
reflexivity.
Qed.

Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist, l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  intros.
  induction l1.
  simpl.
  induction l2.
  simpl.
  reflexivity.
  rewrite <- app_assoc.
  reflexivity.
  set (l1 ++ l2).
  set (n::l1).
  replace (((n1 ++ l2) ++ l3 ) ++ l4) with (n1 ++ (l2 ++ l3 ++ l4)).
  reflexivity.
  rewrite -> app_assoc.
  unfold n1.
  set (l3 ++ l4).
  rewrite -> app_assoc.
  reflexivity.
Qed.

Lemma nonzeros_app : forall l1 l2 : natlist, nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  intros.
  induction l1.
  reflexivity.
  induction l2.
  rewrite -> app_nil_r.
  replace (nonzeros []) with ([]).
  replace (nonzeros (n::l1) ++ []) with (nonzeros(n::l1)).
  reflexivity.
  rewrite -> app_nil_r.
  reflexivity.
  reflexivity.
  induction n.
  induction n0.
  simpl.
  rewrite ->IHl1.
  simpl.
  reflexivity.
  simpl.
  rewrite ->IHl1.
  simpl.
  reflexivity.
  simpl.
  induction n0.
  rewrite ->IHl1.
  simpl.
  reflexivity.
  rewrite ->IHl1.
  simpl.
  reflexivity.
Qed.

Fixpoint beq_natlist (l1 l2 : natlist) : bool :=
  match l1 with
|      [] => match l2 with 
               |  [] => true 
               | h::t => false
             end
|       h1::t1 => match l2 with
                 | [] => false
                 | h2::t2 => (if (myeq_nat h1 h2) then (beq_natlist t1 t2) else false)
                  end
  end.                   

Example test_beq_natlist1 : (beq_natlist nil nil = true).
Proof. reflexivity. Qed.

Example test_beq_natlist2 : (beq_natlist [1;2;3] [1;2;3] = true).
Proof. reflexivity. Qed.

Example test_beq_natlist3 : (beq_natlist [1;2;3] [1;2;4] = false).
Proof. reflexivity. Qed.

Theorem beq_natlist_refl : forall l : natlist, true = beq_natlist l l.
Proof.
  intros.
  induction l.
  reflexivity.
  induction n.
  simpl.
  assumption.
  simpl.
  replace (myeq_nat n n) with true.
  assumption.
  rewrite -> myeq_nat_eq.
  reflexivity.
Qed.


(*SearchAbout rev.*)

Theorem count_member_nonzero : forall (s : bag), leb 1 (count 1 (1 :: s)) = true.
Proof.
  intros.
  induction s.
  simpl.
  reflexivity.
  reflexivity.
Qed.

Theorem ble_n_Sn : forall n, leb n (S n) = true.
Proof.
  intros.
  induction n.
  simpl.
  reflexivity.
  simpl.
  assumption.
Qed.

Fixpoint remove_one (v : nat) (s : bag) : bag :=
  match s with
|      [] => []
|      h::t => (if (myeq_nat v h) then t else h::(remove_one v (t)) )
  end.

Example test_remove_one1 : count 5 (remove_one 5 [2;1;5;4;1]) = 0.
Proof.
  reflexivity.
Qed.

Example test_remove_one2 : count 5 (remove_one 5 [2;1;4;1]) = 0.
Proof.
  reflexivity.
Qed.


Theorem remove_decreases_count : forall s : bag, leb (count 0 (remove_one 0 s)) (count 0 s) = true.
Proof.
  intros.
  induction s.
  reflexivity.
  induction n.  
  simpl.
  set (count 0 s).
  rewrite -> ble_n_Sn.
  reflexivity.
  simpl.
  assumption.
Qed.

Inductive natoption : Type :=
  | Some : nat -> natoption
  | None : natoption.

Fixpoint nth_error (l : natlist) (n : nat) : natoption :=
  match l with
    | nil => None
    | (aa :: t) => (match myeq_nat n 0 with
                   | true => Some aa
                   | false => nth_error t (pred n)
               end)
  end.

Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.

Example test_nth_error2 : nth_error [4;5;6;7] 3 = Some 7.
Proof. reflexivity. Qed.

Example test_nth_error3 : nth_error [4;5;6;7] 9 = None.
Proof. reflexivity. Qed.

End NatList.