Require Import Coq.Classes.SetoidClass.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Peano_dec.
Require Import NatList.
Require Import MyInductions.

Module PartialMap.


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

Inductive id : Type :=
  | Id : nat -> id.

Definition beq_id x1 x2 :=
  match x1, x2 with
    | Id n1, Id n2 => myeq_nat n1 n2
  end.

Check beq_id.

Theorem beq_id_refl : forall x, true = beq_id x x.
Proof.
  intros.
  induction x.  
  simpl.
  induction n.
  simpl.
  reflexivity.
  simpl.
  assumption.
Qed.


Inductive partial_map : Type :=
 | empty : partial_map
| record : id -> nat -> partial_map -> partial_map.

Definition update(d : partial_map) (key : id) (value : nat) : partial_map :=
  record key value d.

Fixpoint find (key : id) (d : partial_map) : NatList.natoption :=
  match d with
    |empty => NatList.None
    |record k v d' => if beq_id key k then NatList.Some v else find key d'
  end.

Theorem update_eq : 
  forall (d : partial_map) (k : id) (v : nat),
    find k (update d k v) = NatList.Some v.
  Proof.
    intros.
    induction d.
    simpl.
    rewrite <- beq_id_refl.
    reflexivity.
    simpl.
    rewrite <- beq_id_refl.
    reflexivity.
  Qed.

Theorem update_neq :
  forall (d : partial_map) (m n : id) (o : nat), beq_id m n = false -> find m (update d n o) = find m d.
Proof.
  intros.
  simpl.
  rewrite ->H.
  reflexivity.
Qed.

Inductive list (X : Type) : Type :=
  | nil : list X
  | cons : X -> list X -> list X.

Print nat.
Check list.

Check nil.

Check (cons nat 2 (cons nat 1 (nil nat))).

Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
  match count with
| 0 => nil X
| S count' => cons X x (repeat X x count')
  end.

Example test_repeat1 : repeat nat 4 2 = cons nat 4 (cons nat 4 (nil nat)).
Proof.
  reflexivity.
Qed.

Example test_repeat2 : repeat bool false 1 = cons bool false (nil bool).
Proof.
  reflexivity.
Qed.

Module MumbleGrumble.

Inductive mumble : Type :=
  | a : mumble
  | b : mumble -> nat -> mumble
  | c : mumble.

Inductive grumble (X:Type) : Type :=
  | d : mumble -> grumble X
  | e : X -> grumble X.

Definition toto := (d mumble (b a 5)).

Check toto.

End MumbleGrumble.

Fixpoint repeat' X x count : list X :=
  match count with
| 0 => nil X
| S count' => cons X x (repeat' X x count')
  end.

Check repeat'.

Arguments nil {X}.
Arguments cons {X} _ _.
Arguments repeat {X} x count.

Inductive list' {X:Type} : Type :=
  | nil' : list'
  | cons' : X -> list' -> list'.

Fixpoint app {X: Type} (l1 l2 : list X) : (list X) :=
  match l1 with
    | nil => l2
    | cons h t => cons h (app t l2)
  end.

Fixpoint rev {X: Type} (l : list X) : list X :=
  match l with
      | nil => nil
      | cons h t => app (rev t) (cons h nil)
  end.

Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
    | nil => 0
    | cons _ l' => S (length l')
  end.

Fail Definition mynil := nil.

Check @nil.
Definition mynil' := @nil nat.

Notation "x :: y" := (cons x y) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation " x ++ y" := (app x y) (at level 60, right associativity).

Definition list123''' := [1;2;3].
Example test_rev1 : rev (cons 1 (cons 2 nil)) = (cons 2 (cons 1 nil)).
Proof. reflexivity. Qed.

Definition doit3times {X:Type} (f:X->X) (n:X) : X :=
  f (f (f n)).

Check @doit3times.

Theorem app_nil_r : forall (X:Type), forall l : list X, l ++ [] = l.
Proof.
  intros.
  induction l.
  intros.
  simpl.
  reflexivity.
  simpl.
  rewrite ->IHl.
  reflexivity.
Qed.

Theorem app_assoc : forall A (l m n : list A), l ++ m ++ n = (l ++ m) ++ n.
Proof.
  intros.
  induction l.
  simpl.
  reflexivity.
  simpl.
  rewrite ->IHl.
  reflexivity.
Qed.

Lemma app_length : forall (X : Type) (l1 l2 : list X), length(l1 ++ l2) = length l1 + length l2.
Proof.
  intros.
  induction l1.
  simpl.
  reflexivity.
  simpl.
  rewrite ->IHl1.
  reflexivity.
Qed.

Theorem rev_app_distr : forall (X : Type) (l1 l2 : list X), rev(l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros.
  induction l1.
  simpl.
  rewrite -> app_nil_r.
  reflexivity.
  simpl.
  rewrite -> IHl1.
  rewrite <- app_assoc.
  reflexivity.
Qed.

Theorem rev_involutive : forall (X : Type) (l : list X), rev (rev l) = l.
Proof.
  intros.
  induction l.
  simpl.
  reflexivity.
  simpl.
  replace ([x]) with (rev [x]).
  set (rev l).
  set (rev [x]).
  rewrite ->rev_app_distr.
  unfold l1.  
  unfold l0.
  simpl.
  rewrite ->IHl.
  reflexivity.
  simpl.
  reflexivity.
Qed.

(* Polymorphic Pairs *)

Inductive prod (X Y : Type) : Type :=
| pair : X -> Y -> prod X Y.

Arguments pair {X} {Y} _ _.

Notation "( x , y )" := (pair x y).
Notation "X * Y" := (prod X Y) : type_scope.

Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with
    | (x, y) => x
  end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with
    | (x, y) => y
  end.

Fixpoint combine { X Y : Type } (lx : list X) (ly : list Y) : list (X * Y) :=
  match lx, ly with
| [], _ => []
| _, [] => []
| x :: tx, y :: ty => (x, y) :: (combine tx ty)
  end.

Check @combine.

Compute (combine [1;2] [false;false;true;true]).

Fixpoint first_on_list { X Y : Type } (lx : list ( X * Y )) : list (X) :=
  match lx with
    | [] => []
    | x::t => (fst x)::(first_on_list t)
  end.

Fixpoint snd_on_list { X Y : Type } (lx : list ( X * Y )) : list (Y) :=
  match lx with
    | [] => []
    | x::t => (snd x)::(snd_on_list t)
  end.
  

Fixpoint split {X Y : Type} (l : list (X * Y)) : (list X) * (list Y) :=
  (first_on_list l, snd_on_list l).

Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof.
  reflexivity.
Qed.

Check @split.

(* Polymorphic Options *)

Inductive option2 ( X : Type ) : Type :=
  | Some2 : X -> option2 X
  | None2 : option2 X.

Arguments Some2 {X} _.
Arguments None2 {X}.


Fixpoint nth_error2 {X : Type } (l : list X) (n : nat) : option2 X :=
  match l with
    | [] => None2
    | a :: l2 => if myeq_nat n 0 then Some2 a else nth_error2 l2 (n-1)
  end.

Example test_nth_error1 : nth_error2 [4;5;6;7] 0 = Some2 4.
Proof.
  reflexivity.
Qed.

Example test_nth_error2 : nth_error2 [[1];[2]] 1 = Some2 [2].
Proof.
  simpl.
  reflexivity.
Qed.

Fixpoint evenb (n:nat) : bool :=
  match n with
      | O => true
      | S O => false
      | S (S n') => evenb n'
  end.

Definition oddb (n:nat) := negb (evenb (n)).

      

Fixpoint filter { X : Type} (test : X -> bool) (l:list X) : (list X) :=
  match l with
    | [] => []
    | h::t => if test h then h :: (filter test t) else filter test t
  end.

Example test_filter1 : filter evenb [1;2;3;4] = [2;4].
Proof.
  reflexivity.
Qed.

Definition length_is_1 { X : Type } (l : list X) : bool :=
  myeq_nat (length l) 1.

Example test_filter2 : filter length_is_1 [ [1;2];[3];[4];[5;6;7];[];[8]] = [[3];[4];[8]].
Proof.
  reflexivity.
Qed.

Definition countoddmembers' (l : list nat) : nat := length (filter oddb l).

Example test_countoddmembers'1 : countoddmembers' [1;0;3;1;4;5] = 4.
Proof.
  reflexivity.
Qed.

Example test_countoddmembers'2: countoddmembers' [0;2;4] = 0.
Proof.
  reflexivity.
Qed.

Example test_countoddmembers'3: countoddmembers' nil = 0.
Proof.
  reflexivity.
Qed.

Example test_anon_fun':
  doit3times (fun n => n * n) 2 = 256.
Proof.
  reflexivity.
Qed.

Example test_filter2' : filter (fun l => NatList.myeq_nat (length l) 1) [[1;2];[3];[4];[5;6;7];[];[8]] = [[3];[4];[8]].
Proof.
  reflexivity.
Qed.

Definition filter_event_gt7 ( l : list nat) : list nat := 
  filter (fun h 
          => 
             if ( (oddb h) ) then true else false
            
         ) l.

Definition partition { X : Type } (test : X -> bool) (l : list X) : list X * list X :=
  ((filter (fun h => (test h)) l), (filter (fun h => (negb (test h))) l)).


Example test_partition1: partition oddb [1;2;3;4;5] = ([1;3;5], [2;4]).
Proof.
  reflexivity.
Qed.

Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
Proof.
  reflexivity.
Qed.

Fixpoint map {X Y : Type} (f: X -> Y) (l:list X) : (list Y) :=
  match l with
    | [] => []
    | h :: t => (f h) :: (map f t)
  end.

Theorem map_app_distr :  forall (X Y : Type) (f : X -> Y) (l1 l2 : list X), map f (l1 ++ l2) = map f l1 ++ map f l2.
Proof.
  intros.
  induction l1.
  simpl.
  reflexivity.
  replace (x::l1) with ([x]++l1).
  rewrite <- app_assoc.
  simpl.
  rewrite <- IHl1.
  reflexivity.
  simpl.
  reflexivity.
Qed.

Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X), map f (rev l) = rev (map f l).
Proof.
  intros.  
  induction l.
  simpl.
  reflexivity.
  replace ( x :: l) with ([x]++l).
  rewrite -> rev_app_distr.
  rewrite -> map_app_distr.
  simpl.
  rewrite <-IHl.
  reflexivity.
  simpl.
  reflexivity.
Qed.

Fixpoint flat_map {X Y : Type} (f: X -> list Y) (l : list X) : (list Y) :=
  match l with
    | [] => []
    | h::t => (let r := (f h) in
              (r ++ (flat_map f t)))
  end.

Example test_flat_map1 : flat_map (fun n => [n;n;n]) [1;5;4] = [1;1;1;5;5;5;4;4;4].
Proof.
  reflexivity.
Qed.

Definition option_map {X Y : Type} (f : X -> Y) (xo : option X) : option Y :=
  match xo with
      | None => None
      | Some x => Some (f x)
  end.

Fixpoint fold {X Y : Type} (f : X -> Y -> Y) (l : list X) (b : Y) : Y :=
  match l with
    | nil => b
    | h :: t => f h (fold f t b)
  end.

Compute fold plus [1;2;3;4] 0.


Example fold_example1 : fold mult [1;2;3;4] 1 = 24.
Proof.
  reflexivity.
Qed.

Definition constfun {X : Type} (x : X) : nat -> X := fun (k : nat) => x.

Definition ftrue := constfun true.
    
Example constfun_example1 : ftrue 0 = true.
Proof.
  reflexivity.
Qed.

Example constfun_example2 : (constfun 5) 99 = 5.
Proof.
  reflexivity.
Qed.

Check plus.

Definition fold_length { X : Type } (l : list X) : nat := fold (fun _ n => S n) l 0.

Example test_fold_length1 : fold_length [4;7;0] = 3.
Proof.
  reflexivity.
Qed.

Theorem fold_length_app : forall X (l1 l2 : list X), 
                             fold_length (l1++l2) = fold_length (l1) + fold_length (l2).
Proof.
  intros.
  induction l1.
  simpl.
  reflexivity.
  replace (x::l1) with ([x]++l1).
  rewrite <- app_assoc.
  unfold fold_length in IHl1.
  unfold fold_length.
  simpl.
  rewrite <-IHl1.
  reflexivity.
  simpl.
  reflexivity.
Qed.
  
Theorem fold_length_correct : forall X (l : list X), fold_length l = length l.
Proof.
  intros.
  induction l.
  simpl.
  unfold fold_length.
  simpl.
  reflexivity.
  replace (x::l) with ([x]++l).
  rewrite -> app_length.
  rewrite -> fold_length_app.
  rewrite -> IHl.
  replace (length [x]) with 1.
  replace (fold_length [x]) with 1.
  reflexivity.
  unfold fold_length.
  unfold fold.
  reflexivity.
  simpl.
  reflexivity.
  simpl.
  reflexivity.
Qed.

Definition toto := [1;2;3].

(*Definition fold_map {X Y : Type} (f : X -> Y) (l : list X) : list Y := *)
Theorem silly1 : forall (n m o p : nat), (n = m) -> ([n;o] = [n;p]) -> ([n;o] = [m;p]).
Proof.
  intros.
  rewrite <- H.
  apply H0.
Qed.

Theorem silly2 : forall (n m o p : nat), n = m -> (forall ( q r : nat), q = r -> [q;o] = [r;p]) -> [n;o] = [m;p].
Proof.
  intros.
  apply H0.
  apply H.
Qed.

Theorem silly2a : forall (n m : nat), (n,n) = (m,m) -> (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) -> [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2.
  apply eq1.
Qed.

(* Logical Connectives *)

Example and_example : 3 + 4 = 7 /\ 2 * 2 =4.
Proof.
  split.
  reflexivity.
  reflexivity.
Qed.

Lemma and_intro : forall A B : Prop, A -> B -> A /\ B.
Proof.
  intros A B HA HB. split.
  - apply HA.
  - apply HB.
Qed.

Theorem plus_0_n2 : forall n : nat, n + 0 = n.
Proof.
  intros.
  induction n.
  simpl.
  reflexivity.
  simpl.
  rewrite ->IHn.
  reflexivity.
Qed.


Theorem a_n_0 : forall a : nat, S a <> 0.
Proof.
  auto.
Qed.

Theorem a_p_b : forall a b : nat, a + S b <> 0.
Proof.
  intros.
  induction a.
  simpl.
  auto.
  simpl.
  set (a + S b).
  apply a_n_0.
Qed.

Theorem and_exercise : forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros.
  split.
  destruct m.
  rewrite <-H.
  replace (n + 0) with n.
  reflexivity.
  rewrite -> plus_0_n2.
  reflexivity.
  absurd (n + S m = 0).
  apply a_p_b.
  assumption.
  destruct n.
  rewrite <- H.
  simpl.
  reflexivity.
  absurd (S n + m = 0).
  set (S n).
  rewrite <- MyInductions.plus_comm.
  unfold n0.
  apply a_p_b.
  assumption.
Qed.

Lemma proj2 : forall P Q : Prop, P /\ Q -> P.
Proof.
  intros P Q [HP HQ].
  apply HP.
Qed.


Theorem and_commut : forall P Q : Prop, P /\ Q -> Q /\ P.
Proof.
  intros P Q [HP HQ].
  split.
  apply HQ.
  apply HP.
Qed.

Theorem  and_assoc : forall P Q R : Prop, P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]].
  split.
  split.
  assumption.
  assumption.
  assumption.
Qed.

Theorem mult_0_r : forall n : nat, n * 0 = 0.
Proof.
  intros n. induction n as [|n' IHn'].
  reflexivity.
  simpl. 
  assumption. 
Qed.

Theorem mult_0_elm : forall n : nat, n * 0 = 0.
Proof.
  auto.
Qed.

Lemma or_example : forall n m : nat, n = 0 \/ m = 0 -> n*m = 0.
Proof.
  intros n m [Hn | Hm].
  rewrite Hn. 
  reflexivity.
  rewrite Hm.
  rewrite mult_0_elm.
  reflexivity.
Qed.

Lemma or_intro : forall A B : Prop, A -> A \/ B.
Proof.
  intros A B HA.
  left.
  apply HA.
Qed.

Lemma zero_or_succ : forall n : nat, n = 0 \/ n = S (pred n).
Proof.
  intros [|n].
  - left. reflexivity.
  - right. reflexivity.
Qed.

    
Lemma toto100 : forall n, ((0 = (S n)) <-> False).
Proof.
  intros.
  split.
  intro.
  inversion H.
  intro.
  contradiction.
Qed.



  

Lemma mult_eq_0 : forall n m, n *m = 0 -> n = 0 \/ m = 0.
Proof.
  intros.
  induction n.
  left.
  reflexivity.
  right.
  admit.
Qed.

Theorem or_commut : forall P Q : Prop, P \/ Q -> Q \/ P.
Proof.
  intros.
  destruct H as [H1 | H2].
  right.
  assumption.
  left.
  assumption.
Qed.

Fact not_implies_out_not : forall (P:Prop), ~P -> (forall (Q:Prop), P -> Q).
Proof.
  intros.
  elim H.
  assumption.
Qed.

Theorem zeo_not_one : ~(0 = 1).
Proof.
  intros contra.
  inversion contra.
Qed.

Check (0 <> 1).  

Theorem zero_not_one : 0 <> 1.
Proof.
  intros H.
  inversion H.
Qed.

Theorem not_False :
  not False.
Proof.
  unfold not.
  intros H.
  destruct H.
Qed.

Theorem contradiction_implies_anything : forall P Q : Prop, (P /\ ~P) -> Q.
Proof.
  intros P Q [HP HNA].
  unfold not in HNA.
  apply HNA in HP.
  destruct HP.
Qed.

Theorem double_neg : forall P : Prop,
    P -> ~~P.
Proof.
  intros P H.
  unfold not.
  intros G.
  apply G.
  apply H.
Qed.

Theorem contrapositive : forall (P Q : Prop), (P -> Q) -> (~Q -> ~P).
Proof.
  intros A B C.
  unfold not.  
  intro D.
  intro E.
  apply D.
  apply C.
  apply E.
Qed.

Theorem not_both_true_and_false : forall P : Prop, ~( P /\ ~P).
Proof.
  unfold not.
  intro H.
  intro G.
  apply G.
  apply G.
Qed.

Theorem ex_falso_quodlibet : forall (P:Prop), False -> P.
Proof.
  intros P contra.
  destruct contra.
Qed.

Lemma True_is_true : True.
  Proof.
    apply I.
  Qed.

Theorem iff_sym : forall P Q : Prop,
      (P <-> Q) -> (Q <-> P).
Proof.
  intros P Q [HAB HBA].
  split.
  apply HBA.
  apply HAB.
Qed.

Lemma not_true_iff_false : forall b, b<> true <-> b = false.
Proof.
  intros b. split.
  apply not_true_is_false.
  intros H.  rewrite H. intros H'. inversion H'.
Qed.

Theorem iff_refl : forall P : Prop, P <-> P.
Proof.
  intro P.
  split.
  intros.
  apply H.
  intros.
  apply H.
Qed.

Theorem iff_trans : forall P Q R : Prop, (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  intros.
  split.
  intros.
  apply H0.
  apply H.
  assumption.
  intros.
  apply H.
  apply H0.
  apply H1.
Qed.

Theorem or_distributes_over_and : forall P Q R : Prop, P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros.
  split.
  intro.
  elim H.
  intro.
  split.
  left.
  apply H0.
  left.
  apply H0.
  elim H.
  intro.
  intro.
  split.
  left.
  apply H0.
  left.
  apply H0.
  intro.
  intro.  
  split.
  right.
  elim H1.
  intros.
  apply H2.
  right.
  elim H1.
  intros.
  apply H3.
  intros.
  destruct H as [H1 H2].
  elim H1.
  elim H2.
  intros.
  left.
  apply H0.
  intros.
  left.
  apply H0.
  intros.
  destruct H2 as [H3 | H4].
  left.
  apply H3.
  right.
  split.
  apply H.
  apply H4.
Qed.

Lemma four_is_even : exists n : nat, 4 = n + n.
Proof.
  exists 2. 
  reflexivity.
Qed.

Theorem exists_example_2 : forall n, (exists m, n = 4 +m) -> (exists o, n = 2 + o).
Proof.
  intros n [m Hm].
  exists (2 + m).
  apply Hm.
Qed.

Theorem dist_not_exists : 
  forall (X : Type) (P : X -> Prop), (forall x, P x) -> ~ (exists x, ~P x).
  intros.
  unfold not.  
  intros.
  destruct H0 as [x G].
  apply G.
  apply H.
Qed.

Theorem dist_exists_or : 
  forall (X : Type) (P Q : X -> Prop), (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
  intros.
  split.
  intros.
  left.
  
End PartialMap.


(* MAP *)
 

