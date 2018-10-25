Set Warnings "-notation-overridden,-parsing".
Require Export ProofObjects.

Check nat_ind.

Theorem mult_0_r' : forall n : nat,
  n * 0 = 0.
Proof.
  apply nat_ind.
  - reflexivity.
  - simpl. intros n' IHn'. rewrite -> IHn'.
    reflexivity.
Qed.

Theorem plus_one_r' : forall n : nat,
  n + 1 = S n.
Proof.
  apply nat_ind.
  - reflexivity.
  - simpl. intros n' IHn'. rewrite -> IHn'.
    reflexivity.
Qed.

Inductive yesno : Type :=
  | yes : yesno
  | no : yesno.

Check yesno_ind.

Inductive rgb : Type :=
  | red : rgb
  | green : rgb
  | blue : rgb.

(* rgb_ind : forall P : rgb -> Prop, P red
  -> P green -> P blue -> forall r : rgb, P r *)

Check rgb_ind.

Inductive natlist : Type :=
  | nnil : natlist
  | ncons : nat -> natlist -> natlist.

Check natlist_ind.

Inductive natlist1 : Type :=
  | nnil1 : natlist1
  | nsnoc1 : natlist1 -> nat -> natlist1.

(* natlist1_ind : forall P : natlist1 -> Prop,
    P nnil1 -> (forall (n : natlist1) (n0 : nat),
    P n -> P (nsnoc n n0) -> forall n : natlist1, P n *)

Check natlist1_ind.

Inductive byntree : Type :=
  | bempty : byntree
  | bleaf : yesno -> byntree
  | nbranch : yesno -> byntree -> byntree -> byntree.

(* byntree_ind : forall P : byntree -> Prop,
    P bempty -> forall y : yesno, P (bleaf y) ->
    (forall y : yesno, b : byntree, b0 : byntree -> 
    P (nbranch y b b0)) -> forall b : byntree, P b *)

Check byntree_ind.

Inductive ExSet : Type :=
  | con1 : bool -> ExSet
  | con2 : nat -> ExSet -> ExSet.

Check ExSet_ind.


Inductive tree (X : Type) : Type :=
  | leaf : X -> tree X
  | node : tree X -> tree X -> tree X.

(* forall (X : Type) (P : tree X -> Prop),
    forall (x : X), P (leaf X x) ->
    forall (x : X) (t t0 : tree X), P t, P t0
    -> P (node t t0) -> forall t : tree X, P t *)

Check tree_ind.


Inductive mytype (X : Type) : Type :=
  | constr1 : X -> mytype X
  | constr2 : nat -> mytype X
  | constr3 : mytype X -> nat -> mytype X.

Check mytype_ind.

Inductive foo (X Y : Type) : Type :=
  | bar : X -> foo X Y
  | baz : Y -> foo X Y
  | quux : (nat -> foo X Y) -> foo X Y.

Check foo_ind.

Definition P_m0r (n:nat) : Prop :=
  n * 0 = 0.

Definition P_m0r' : nat -> Prop :=
  fun n => n * 0 = 0.

Theorem mult_0_r'' : forall n : nat,
  P_m0r n.
Proof.
  apply nat_ind.
  - reflexivity.
  - intros n IHn.
    unfold P_m0r in IHn. unfold P_m0r.
    simpl. apply IHn. Qed.

Theorem plus_comm' : forall n m : nat,
  n + m = m + n.
Proof.
  induction n as [|n'].
  - intros m. rewrite <- plus_n_O. reflexivity.
  - intros m. simpl. rewrite -> IHn'.
    rewrite <- plus_n_Sm. reflexivity. Qed.

Theorem plus_comm'' : forall n m : nat,
  n + m = m + n.
Proof.
  induction m as [|m'].
  - rewrite <- plus_n_O. reflexivity.
  - simpl. rewrite <- IHm'.
    rewrite <- plus_n_Sm. reflexivity. Qed.

Check ev_ind.


Inductive le (n:nat) : nat -> Prop :=
  | le_n : le n n
  | le_S : forall m, (le n m) -> (le n (S m)).

Notation "m <= n" := (le m n).

Check le_ind.


