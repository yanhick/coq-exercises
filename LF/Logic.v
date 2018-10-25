Set Warnings "-notation-overriden,-parsing".
Require Export MoreTactics.

Check 3 = 3.

Check forall n m : nat, n + m = m + n.

Check 2 = 2.

Check 3 = 4.

Theorem plus_2_2_is_4 : 2 + 2 = 4.
Proof. reflexivity. Qed.

Definition plus_fact : Prop := 2 + 2 = 4.
Check plus_fact.

Theorem plus_fact_is_true : plus_fact.
Proof. reflexivity. Qed.

Definition is_three (n : nat) : Prop := n = 3.
Check is_three.

Definition injective {A B} (f : A -> B) :=
  forall x y : A, f x = f y -> x = y.

Lemma succ_inj : injective S.
Proof.
  intros n m H. inversion H. reflexivity.
Qed.

Check @eq.

Example and_example : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  split.
  - reflexivity.
  - reflexivity.
Qed.

Lemma and_intro : forall A B : Prop, A -> B -> A /\ B.
Proof.
  intros A B HA HB. split.
  - apply HA.
  - apply HB.
Qed.

Example and_example' : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  apply and_intro.
  - reflexivity.
  - reflexivity.
Qed.

Example and_exercise : forall n m : nat,
  n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros n m H. split.
  - destruct n.
    + reflexivity.
    +  inversion H.
  - destruct m.
    + reflexivity.
    + rewrite plus_comm in H. inversion H.
Qed.

Lemma and_example2 : forall n m : nat,
  n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m H.
  destruct H as [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

Lemma and_example3 : forall n m : nat,
  n + m = 0 -> n * m = 0.
Proof.
  intros n m H.
  assert (H' : n = 0 /\ m = 0).
  { apply and_exercise. apply H. }
  destruct H' as [Hn Hm].
  rewrite Hn. rewrite Hm. reflexivity.
Qed.

Lemma proj1 : forall P Q : Prop,
  P /\ Q -> P.
Proof.
  intros P Q [HP HQ].
  apply HP. Qed.

Lemma proj2 : forall P Q : Prop,
  P /\ Q -> Q.
Proof.
  intros P Q [HP HQ].
  apply HQ. Qed.

Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  intros P Q [HP HQ].
  split.
  - apply HQ.
  - apply HP. Qed.

Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]]. split.
  - split.
    + apply HP.
    + apply HQ.
  - apply HR.
Qed.

Check and.

Lemma or_example : forall n m : nat,
  n = 0 \/ m = 0 -> n * m = 0.
Proof.
intros n m [Hn | Hm].
  - rewrite Hn. reflexivity.
  - rewrite Hm. rewrite <- mult_n_O.
    reflexivity.
Qed.

Lemma or_intro : forall A B : Prop,
  A -> A \/ B.
Proof.
  intros A B HA.
  left.
  apply HA.
Qed.

Lemma zero_or_succ : 
  forall n : nat, n = 0 \/ n = S (pred n).
Proof.
  intros [|n].
  - left. reflexivity.
  - right. reflexivity.
Qed.

Module MyNot.

Definition not (P: Prop) := P -> False.

Notation "¬ x" := (not x) (at level 50) : type_scope.

Check not.

End MyNot.

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  intros P contra.
  destruct contra.
Qed.



Fact not_implies_our_not : forall (P : Prop),
  ~ P -> (forall (Q : Prop), P -> Q).
Proof.
  intros P P' H1 H2.
  destruct P'.
  apply H2.
Qed.

Theorem zero_not_one : ~ (0 = 1).
Proof.
  intros contra. inversion contra.
Qed.

Check (0 <> 1).

Theorem zero_not_one' : 0 <> 1.
Proof.
  intros H. inversion H.
Qed.

Theorem not_False : ~ False.
Proof.
  unfold not. intros H. destruct H. Qed.

Theorem contradiction_implies_anything :
  forall P Q : Prop, (P /\ ~ P) -> Q.
Proof.
  intros P Q [HP HNA]. unfold not in HNA.
  apply HNA in HP. destruct HP. Qed.

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  intros P H. unfold not. intros G. apply G.
  apply H. Qed.

Theorem contrapositive : forall (P Q : Prop),
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q H1 H2 P'. unfold not in H2. apply H2 in H1.
  - inversion H1.
  - apply H2 in H1.
    + destruct H1.
    + destruct H2.
    apply H1. apply P'.
Qed.

Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof.
  intros P H. destruct H as [Hm Hn].
  destruct Hn. apply Hm.
Qed.

Theorem not_true_is_false : forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H.
  - unfold not in H.
    apply ex_falso_quodlibet.
    apply H. reflexivity.
  - reflexivity.
Qed.

Theorem not_true_is_false' : forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H.
  - unfold not in H.
    exfalso.
    apply H. reflexivity.
  - reflexivity.
Qed.

Lemma True_is_true : True.
Proof. apply I. Qed.

Module MyIff.

Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

Notation "P <-> Q" := (iff P Q) (at level 95, no associativity) : type_scope.

End MyIff.

Theorem iff_sym : forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
Proof.
  intros P Q [HAB HBA].
  split.
  - apply HBA.
  - apply HAB. Qed.

Lemma not_true_iff_false : forall b,
  b <> true <-> b = false.
Proof.
  intros b. split.
  - apply not_true_is_false.
  - intros H. rewrite H. intros H'. inversion H'.
Qed.

Theorem or_distributes_over_and : forall P Q R: Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R.
  split.
  - intros H. destruct H.
    + split. left. apply H. left. apply H.
    + inversion H. split.
      * right. apply H0.
      * right. apply H1.
  - intros H. inversion H as [[HP1 | HQ] [HP2 | HR]].
    left. apply HP1.
    left. apply HP1.
    left. apply HP2.
    right. split. apply HQ. apply HR.
Qed.

Require Import Coq.Setoids.Setoid.

Search mult.

Lemma mult_eq_0 : forall n m, 
  n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros [|n].
  - intros m H. left. reflexivity.
  - intros [|m].
    + intros H. rewrite mult_0_r in H. right. apply H.
    + intros H. inversion H.
Qed.

Theorem or_commut : forall P Q : Prop,
  P \/ Q -> Q \/ P.
Proof.
  intros P Q H. inversion H.
  - right. apply H0.
  - left. apply H0.
Qed.


Lemma mult_0 : forall n m, n * m = 0 <-> n = 0 \/ m = 0.
Proof.
  split.
  - apply mult_eq_0.
  - apply or_example.
Qed.

Lemma or_assoc : forall P Q R : Prop,
  P \/ ( Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros P Q R. split.
  - intros [H | [H | H]].
    + left. left. apply H.
    + left. right. apply H.
    + right. apply H.
  - intros [[H | H] | H].
    + left. apply H.
    + right. left. apply H.
    + right. right. apply H.
Qed.

Lemma mult_0_3 : forall n m p,
  n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
  intros n m p.
  rewrite mult_0. rewrite mult_0. rewrite or_assoc.
  reflexivity.
Qed.

Lemma apply_iff_example :
  forall n m : nat, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n m H. apply mult_0. apply H.
Qed.

Lemma four_is_even : exists n : nat, 4 = n + n.
Proof.
  exists 2. reflexivity.
Qed.

Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  intros n [m Hm].
  exists (2 + m).
  apply Hm. Qed.

Theorem dist_not_exists : 
  forall (X : Type) (P : X -> Prop),
  (forall x, P x) -> not ( exists x, not (P x)).
Proof.
  intros X P o [x E].
  unfold not in E.
  apply E. apply o.
Qed.

Theorem dist_exists_or : 
  forall (X : Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x)
  <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros X P Q. split.
  - intros [x E]. destruct E.
    + left. exists x. apply H.
    + right. exists x. apply H.
  - intros H. destruct H.
    + inversion H. exists x. left. apply H0.
    + inversion H. exists x. right. apply H0.
Qed.

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.

Example In_example_1 : In 4 [1; 2; 3; 4; 5].
Proof.
  simpl. right. right. right. left. reflexivity.
Qed.

Example In_example_2 :
  forall n, In n [2; 4] -> exists n', n = 2 * n'.
Proof.
  simpl.
  intros n [H | [H | []]].
  - exists 1. rewrite <- H. reflexivity.
  - exists 2. rewrite <- H. reflexivity.

Qed.

Check map.

Lemma In_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
  In x l -> In (f x) (map f l).
Proof.
  intros A B f l x.
  induction l as [|x' l' IHl'].
  - simpl. intros [].
  - simpl. intros [H | H].
    + rewrite H. left. reflexivity.
    + right. apply IHl'. apply H.
Qed.

Lemma In_map_iff : 
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
    In y (map f l) <-> exists x, f x = y /\ In x l.
Proof with intuition.
  intros A B f l y.
  induction l as [|y' l' IHl].
  - simpl. split.
    + intro H. inversion H.
    + intro H. inversion H as [Hm Hn]. apply Hn.
  - simpl. split.
    + intro H. destruct H.
      * exists y'. split. apply H. left. reflexivity.
      * inversion IHl. 
        destruct (H0 H). exists x. split. 
        destruct H2. apply H2. destruct H2. right. apply H3.
    + intro H. destruct H.
      * inversion IHl. inversion H. rewrite IHl. destruct H3.
        left. rewrite H3. apply H2.
        right. exists x. split. apply H2. apply H3.
Qed.


Lemma In_app_iff : forall A l l' (a : A),
  In a (l++l') <-> In a l \/ In a l'.
Proof.
  intros A l l' a.
  induction l as [|a' l'' IHl'].
  - simpl. split.
    + intros H. right. apply H.
    + intro H. destruct H.
      * inversion H.
      * apply H.
  - simpl. split.
    + intro H. destruct H. 
      * left. left. apply H.
      * rewrite <- or_assoc. right. apply IHl'.
        apply H.
    + intro H. destruct H.
      * destruct H.
        left. apply H.
        right. rewrite IHl'. left. apply H.
      * right. rewrite IHl'. right. apply H.
Qed.

Fixpoint All 
  {T : Type} (P : T -> Prop) (l : list T) : Prop :=
  match l with
  | [] => True
  | x :: xs => P x /\ All P xs
  end.


Lemma All_In : 
  forall T (P : T -> Prop) (l : list T),
  (forall x, In x l -> P x) <-> All P l.
Proof.
  intros T P l.
  induction l as [|h l' IHl].    
  - simpl. split.
    + intro H. reflexivity.
    + intros H h contra. inversion contra.
  - simpl. split.
    + intro H. rewrite <- IHl. split.
      * apply H. left. reflexivity.
      * intros H1 H2. apply H. right. apply H2.
    + intros H H1 H2. destruct H2.
      * rewrite <- H0. apply H.
      * rewrite <- IHl in H. apply H. apply H0.
Qed.

Definition combine_odd_even 
  (Podd Peven : nat -> Prop) : nat -> Prop :=
  (fun n => if oddb n then Podd n else Peven n).
  

Search oddb.
Search evenb.

Theorem combine_odd_even_intro :
  forall (Podd Peven : nat -> Prop) (n : nat),
          (oddb n = true -> Podd n) ->
          (oddb n = false -> Peven n) ->
          combine_odd_even Podd Peven n.
Proof.
  intros Podd Peven n H1 H2. 
  unfold combine_odd_even.
  induction n.
  - simpl. apply H2. unfold oddb. simpl. reflexivity.
  - destruct (oddb (S n)).
    + apply H1. reflexivity.
    + apply H2. reflexivity.
Qed.

Theorem combine_odd_even_elim_odd : 
  forall (Podd Peven : nat -> Prop) (n : nat),
          combine_odd_even Podd Peven n ->
          oddb n = true ->
          Podd n.
Proof.
  intros Podd Peven n H1 H2.
  unfold combine_odd_even in H1.
  rewrite H2 in H1. apply H1.
Qed.

Theorem combine_odd_even_elim_even :
  forall (Podd Peven : nat -> Prop) (n : nat),
          combine_odd_even Podd Peven n ->
          oddb n = false ->
          Peven n.
Proof.
  intros Podd Peven n H1 H2.
  unfold combine_odd_even in H1.
  rewrite H2 in H1. apply H1.
Qed.

Check plus_comm.

Lemma plus_comm3 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite plus_comm.
  rewrite plus_comm.
Abort.

Lemma plus_comm3_take2 : 
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite plus_comm.
  assert (H : y + z = z + y).
  { rewrite plus_comm. reflexivity. }
  rewrite H.
  reflexivity.
Qed.

Lemma plus_comm_take3 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite plus_comm.
  rewrite (plus_comm y z).
  reflexivity.
Qed.

Example lemma_application_ex :
  forall {n : nat} {ns : list nat},
        In n (map (fun m => m * 0) ns) ->
        n = 0.
Proof.
  intros n ns H.
  destruct (proj1 _ _ (In_map_iff _ _ _ _ _) H)
    as [m [Hm _]].
  rewrite mult_0_r in Hm. rewrite <- Hm. reflexivity.
Qed.

Example function_equality_ex1 : plus 3 = plus (pred 4).
Proof. reflexivity. Qed.

Example function_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
Abort.

Axiom functional_extensionality :
  forall {X Y : Type} {f g : X -> Y},
  (forall (x:X), f x = g x) -> f = g.

Example function_equality_ex2' :
  (fun x => plus x 1 ) = (fun x => plus 1 x).
Proof.
  apply functional_extensionality. intros x.
  apply plus_comm.
Qed.

Print Assumptions function_equality_ex2'.


Fixpoint rev_append {X} (l1 l2 : list X) : list X :=
  match l1 with
  | [] => l2
  | x :: l1' => rev_append l1' (x :: l2)
  end.

Definition tr_rev {X} (l : list X) : list X :=
  rev_append l [].

Search rev.

Search list.

Compute (rev_append [4;5;6] [3;2;1]).
Compute (rev_append [1;2;3;4;5;6] []).


Lemma rev_elem :
  forall (X : Type) (x : X) (xs : list X),
  rev_append xs [x] = rev_append (x :: xs) [].
Proof.
  intros X x xs. simpl. reflexivity.
Qed.

Lemma rev_elem_2 :
  forall (X : Type) (x : X) (xs : list X),
  rev_append xs [] ++ [x] = rev_append xs [x].
Proof.
  intros X x xs. induction xs as [| c xs' IHl].
  - reflexivity.
  - simpl. simpl in IHl. unfold rev_append.
Admitted.

Lemma rev_append_correct :
  forall (X : Type) (l : list X),
  rev_append l [] = rev l.
Proof.
  intros X l. induction l.
  - simpl. reflexivity.
  - simpl. rewrite <- IHl. rewrite <- rev_elem_2.
    reflexivity.
Qed.

Lemma rev_append_unit : 
  forall (X : Type) (l : list X),
  tr_rev l = rev_append l [].
Proof.
  intros X l. unfold tr_rev. reflexivity.
Qed.

Lemma tr_rev_correct : forall X, @tr_rev X = @rev X.
Proof.
   intro X. 
   apply functional_extensionality.
   intro l.
   induction l.
   - simpl. unfold tr_rev. simpl. reflexivity.
   - rewrite rev_append_unit.  rewrite <- rev_append_correct. reflexivity.
Qed.

Search negb.

Theorem evenb_double : forall k, evenb (double k) = true.
Proof.
  intros k. induction k as [|k' IHk'].
  - reflexivity.
  - simpl. apply IHk'.
Qed.

Theorem evenb_double_conv : forall n,
  exists k, n = if evenb n then double k
                           else S (double k).
Proof.
  intros n. induction n.
  - simpl. exists 0. simpl. reflexivity.
  - rewrite evenb_S.  destruct (evenb n).
    + simpl. destruct IHn.
      exists x. rewrite H. reflexivity.
    + simpl. destruct IHn. rewrite H. exists n.
      rewrite H. simpl.
Admitted.

Theorem event_bool_prop : forall n,
  evenb n = true <-> exists k, n = double k.
Proof.
  intros n. split.
  - intros H. destruct (evenb_double_conv n) as [k Hk].
    rewrite Hk. rewrite H. exists k. reflexivity.
  - intros [k Hk]. rewrite Hk. apply evenb_double.
Qed.

Fail Definition is_even_prime n :=
  if n = 2 then true else false.

Open Scope bool_scope.

Search andb.

Lemma andb_true_iff : forall b1 b2 : bool,
  b1 && b2 = true <-> b1 = true /\ b2 = true.
Proof.
  intros b1 b2. split.
  - intros H. apply andb_prop in H. apply H.
  - intro H. apply andb_true_intro in H. apply H.
Qed.

Search orb.

Check (orb true false).

Lemma orb_true_iff : forall b1 b2,
  orb b1 b2 = true <-> b1 = true \/ b2 = true.
Proof.
  intros b1 b2. split.
  - intros H. unfold orb in H. destruct b1.
    + left. reflexivity.
    + right. apply H.
  - intros H. unfold orb. destruct b1.
    + reflexivity.
    + destruct H.
      * destruct b2.
        reflexivity.
        apply H.
      * apply H.
Qed.

Lemma beq_nat_refl : forall n, true = beq_nat n n.
Proof.
  intro x; induction x; simpl in |- *; auto.
Qed.



Theorem beq_nat_true_iff : forall n1 n2 : nat,
  beq_nat n1 n2 = true <-> n1 = n2.
Proof.
  intros n1 n2. split.
  - apply beq_nat_true.
  - intros H. rewrite H. rewrite <- beq_nat_refl. reflexivity.
Qed.

Theorem beq_nat_false : forall (x y : nat),
 beq_nat x y = false -> x <> y.
Proof.
  intros n m H. induction n.
  - destruct m. 
    + inversion H.
    + unfold not. intro H1. apply beq_nat_true_iff in H1.
      inversion H1.
  - unfold not. intro H1. apply beq_nat_true_iff in H1.
    destruct (beq_nat (S n) m).
    + inversion H.
    + inversion H1.
Qed.

Search beq_nat.

Theorem beq_nat_false_iff : forall x y : nat,
  beq_nat x y = false <-> x <> y.
Proof.
  intros x y. split.
  - intros H H1. apply beq_nat_true_iff in H1.
    destruct (beq_nat x y).
    + inversion H.
    + inversion H1.
  - intro H. destruct (beq_nat x y).
    + unfold not in H. destruct H.
      apply beq_nat_true_iff.
Admitted.

Fixpoint beq_list {A :  Type} (beq : A -> A -> bool)
          (l1 l2 : list A) : bool :=
  match l1 with
  | [] => match l2 with
          | [] => true
          | _ => false
          end
  | (x :: xs) => match l2 with 
                 | [] => false
                 | (y :: ys) => 
                      if beq x y 
                      then beq_list beq xs ys
                      else false
                  end
  
  end.

Lemma list_append_not_same : forall A (x : A) (l : list A),
  l = x :: l -> False.
Proof.
  intros A x l.
  induction l.
  - intro H. discriminate.
  - intro H. unfold not in IHl. inversion H.
    apply IHl in H2. apply H2.
Qed.

Search list.

Lemma beq_list_true_iff : 
  forall A (beq : A -> A -> bool),
  (forall a1 a2, beq a1 a2 = true <-> a1 = a2) ->
  forall l1 l2, beq_list beq l1 l2 = true <-> l1 = l2.
Proof.
  intros A beq H l1 l2. split.
  - intro H1.
 induction l1.
    + induction l2.
      * reflexivity.
      * inversion H1.
    + induction l2 as [| y].
      * inversion H1.
      * inversion H1. destruct (H x y).
        destruct (beq x y).
Admitted.


Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
  | [] => true
  | x :: l' => andb (test x) (forallb test l')
  end.

Search forallb.
Search All.
Search In.

Theorem forallb_true_iff : forall X test (l : list X),
  forallb test l = true <-> All (fun x => test x = true) l.
Proof.
  intros X test l. split. induction l.
  - intro H. simpl. apply True_is_true.
  - intro H. rewrite <- All_In. intros H1 H2.
    inversion H2.
    + rewrite <- H0. destruct (test x).
      * reflexivity.
Admitted.

Definition excluded_middle := forall P : Prop,
  P \/ ~P.

Theorem restricted_excluded_middle : forall P b,
  (P <-> b = true) -> P \/ ~P.
Proof.
  intros P [] H.
  - left. rewrite H. reflexivity.
  - right. rewrite H. intros contra. inversion contra.
Qed.

Theorem restricted_excluded_middle_eq : forall (n m : nat),
  n = m \/ n <> m.
Proof.
  intros n m.
  apply (restricted_excluded_middle (n = m) (beq_nat n m)).
  symmetry.
  apply beq_nat_true_iff.
Qed.

Theorem excluded_middle_irrefutable : forall (P : Prop),
  ~ ~ (P \/ ~P).
Proof.
  intros P H. unfold not in H. apply H. right. intro H1.
  destruct H. left. apply H1.
Qed.

Theorem not_exists_dist :
  excluded_middle -> forall (X : Type) (P : X -> Prop),
    ~ (exists x, ~ (P x)) -> (forall x, P x).
Proof.
  intros excluded_middle X P H x.
  unfold not in H. simpl. destruct (excluded_middle (P x)).
  - apply H0.
  - unfold not in H0. destruct H. exists x. apply H0.
Qed.






