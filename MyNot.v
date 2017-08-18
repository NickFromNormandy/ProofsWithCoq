
(*
Require Import Coq.Classes.SetoidClass.
(*Require Import MyInductions.*)
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Peano_dec.
(*Require Import Basic.*)

Require Import NatList.

Module MyNot.

Definition not (P:Prop) := P -> False.

(*Notation "¬ x" := (not x) : type_scope. *)

Check not.

Theorem ex_falso_quodlibet : forall (P:Prop), False -> P.
Proof.
  intros P.
  contradiction.

Qed.

Fact not_implies_our_not : forall (P : Prop), not( P) -> (forall (Q:Prop), P -> Q).
Proof.
  

End MyNot.

*)
