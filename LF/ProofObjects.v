Set Warnings "-notation-overridden,-parsing".
Require Export IndProp.
Require Export Logic.
Require Coq.omega.Omega.

Print ev.

Check ev_SS.

Theorem ev_4 : ev 4.
Proof.
  apply ev_SS. apply ev_SS. apply ev_0. Qed.

Print ev_4.

Check (ev_SS 2 (ev_SS 0 ev_0)).

Theorem ev_4' : ev 4.
Proof.
  apply (ev_SS 2 (ev_SS 0 ev_0)).
Qed.

Theorem ev_4'' : ev 4.
Proof.
  Show Proof.
  apply ev_SS.
  Show Proof.
  apply ev_SS.
  Show Proof.
  apply ev_0.
  Show Proof.
Qed.

Definition ev_4''' : ev 4 :=
  ev_SS 2 (ev_SS 0 ev_0).

Print ev_4.

Print ev_4'.

Print ev_4''.

Print ev_4'''.

Theorem ev_8 : ev 8.
Proof.
  repeat apply ev_SS. apply ev_0.
Qed.

Definition ev_8' : ev 8 :=
  ev_SS 6 (ev_SS 4 (ev_SS 2 (ev_SS 0 ev_0))).

Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
  intros n H. simpl.
  apply ev_SS.
  apply ev_SS.
  apply H.
Qed.


Definition ev_plus4' : forall n, ev n -> ev (4 + n) :=
  fun (n : nat) => fun (H : ev n) =>
    ev_SS (S (S n)) (ev_SS n H).

Definition ev_plus4'' (n : nat) (H : ev n)
  : ev (4 + n) :=
  ev_SS (S (S n)) (ev_SS n H).

Check ev_plus4''.


Definition ev_plus2 : Prop :=
  forall n, forall (E : ev n), ev (n + 2).

Definition ev_plus2' : Prop :=
  forall n, forall (_ : ev n), ev (n + 2).

Definition ev_plus2'' : Prop :=
  forall n, ev n -> ev (n + 2).

Definition add1 : nat -> nat.
intro n.
Show Proof.
apply S.
Show Proof.
apply n.
Defined.

Print add1.

Compute add1 2.

Module Props.

Module And.

Inductive and (P Q : Prop) : Prop :=
  | conj : P -> Q -> and P Q.

End And.

Print prod.


Lemma and_comm : forall P Q : Prop, P /\ Q <-> Q /\ P.
Proof.
  intros P Q. split.
  - intros [HP HQ]. split.
    + apply HQ.
    + apply HP.
  - intros [HP HQ]. split.
    + apply HQ.
    + apply HP.
Qed.

Definition and_comm'_aux P Q (H : P /\ Q) :=
  match H with
  | conj HP HQ => conj HQ HP
  end.

Definition and_comm' P Q : P /\ Q <-> Q /\ P :=
  conj (and_comm'_aux P Q) (and_comm'_aux Q P).

Definition conj_fact_aux P R (H : P /\ R) :=
  match H with
  | conj HP HQ => conj HP HQ
  end.

Definition conj_fact : 
  forall P Q R, P /\ Q -> Q /\ R -> P /\ R := 
  fun P => fun Q => fun R => fun PQ => fun QR =>
   match PQ with
   | conj P Q => match QR with
                  | conj Q R => conj P R
                  end
   end.

Module Or.

Inductive or (P Q : Prop) : Prop :=
  | or_introl : P -> or P Q
  | or_intror : Q -> or P Q.

End Or.

Definition or_comm : forall P Q, P \/ Q -> Q \/ P :=
  fun _ => fun _ => fun PQ => 
      match PQ with
      | or_introl P => or_intror P
      | or_intror Q => or_introl Q
      end.

Module Ex.

Inductive ex { A : Type } (P : A -> Prop) : Prop :=
  | ex_intro : forall x : A, P x -> ex P.

End Ex.

Check ex (fun n => ev n).

Definition some_nat_is_even : exists n, ev n :=
  ex_intro ev 4 (ev_SS 2 (ev_SS 0 ev_0)).

Definition ex_ev_Sn : ex (fun n => ev (S n)) :=
  ex_intro (fun n => ev (S n)) 1 (ev_SS 0 ev_0).

Inductive True : Prop :=
  | I : True.

Inductive False : Prop :=.

End Props.

Module MyEquality.

Inductive eq { X : Type } : X -> X -> Prop :=
  | eq_refl : forall x, eq x x.

Notation "x = y" := (eq x y)
                    (at level 70, no associativity)
                    : type_scope.


Lemma four : 2 + 2 = 1 + 3.
Proof.
  apply eq_refl.
Qed.

Definition four' : 2 + 2 = 1 + 3 :=
  eq_refl 4.

Definition singleton : forall (X : Type) (x : X),
  [] ++ [x] = x :: [] :=
  fun (X : Type) (x : X) => eq_refl [x].

End MyEquality.

Lemma equality__leibniz_equality :
  forall (X : Type) (x y : X),
  x = y -> forall P : X -> Prop, P x -> P y.
Proof.
  intros X x y H1 P H2. rewrite -> H1 in H2.
  apply H2.
Qed.


