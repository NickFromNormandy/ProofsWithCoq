Require Import Coq.Classes.SetoidClass.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Peano_dec.
Require Import NatList.
Require Import MyInductions.
Require Setoid.
(*Require PeanoNat Le Gt Minus Bool Lt.*)
Require Init.Datatypes.
Require Import PartialMap.


Open Scope list_scope.


Module ProgrammingWithPropositions.

Fixpoint myeq_nat n m  :=
  match n, m with
    | O, O => true
    | O, S _ => false
    | S _, O => false
    | S n1, S m1 => myeq_nat n1 m1
  end.

Fixpoint In {A : Type} (x : A) (l : PartialMap.list A)  :=
  match l with
  | PartialMap.nil => False
  | (PartialMap.cons x' l') => (x' = x) \/ (In x l')
  end.

Definition l := (PartialMap.cons 2 (PartialMap.cons 4 PartialMap.nil)).

Example In_Example_1 : In 4 l.
Proof.
  simpl.
  right.
  left.
  reflexivity.
Qed.

Check l.

Example In_example_2 : forall n, In n l -> exists n', n = 2* n'.
Proof.
  simpl.
  intros n [H | [H | []]].
  - exists 1. rewrite <- H. reflexivity.
  - exists 2. rewrite <- H. reflexivity.
Qed.

Lemma In_map :
  forall (A B : Type) (f : A -> B) (l : PartialMap.list A) ( x : A),
    In x l -> In (f x) (PartialMap.map f l).
Proof.
  intros A B f l x.
  induction l as [|x' l' IHl'].
  - simpl. intros. assumption.
  - simpl. intros [H | H].
    + rewrite H. left. reflexivity.
    + right. apply IHl'. apply H.
Qed.

Lemma In_map_iff : forall (A B : Type) ( f : A -> B) (l : PartialMap.list A) (y : B),
    In y (PartialMap.map f l) <-> exists x, f x = y /\ In x l.
Proof.
  intros.
  