Set Warnings "-notation-overriden,-parsing".
Require Export Lists.
Require Export Poly.



Arguments nil {X}.
Arguments cons {X} _ _.
Arguments repeat {X} x count.

Fixpoint app {X : Type} (l1 l2 : list X) : (list X) :=
  match l1 with
  | nil => l2
  | cons h t => cons h (app t l2)
  end.

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).


Theorem silly1 : forall (m n o p : nat),
  n = m -> [n;o] = [n;p] -> [n;o] = [m;p].
  Proof.
    intros n m o p eq1 eq2.
    rewrite <- eq1.
    apply eq2. Qed.


Theorem silly2 : forall (n m o p : nat),
  n = m -> 
  (forall (q r : nat), q = r -> [q;o] = [r;p]) ->
  [n;o] = [m;p].
  Proof.
    intros n m o p eq1 eq2.
    apply eq2. apply eq1. Qed.

Theorem silly2a : forall (n m : nat),
  (n,n) = (m,m) ->
  (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
  [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2. apply eq1. Qed.

Definition oddb (n:nat) : bool   :=   negb (evenb n).

Theorem silly_ex : 
  (forall n, evenb n = true -> oddb (S n) = true) ->
  evenb 3 = true -> oddb 4 = true.
Proof.
  intros n eq1.
  apply eq1. Qed.

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


Theorem silly3_firsttry : forall (n : nat),
  true = beq_nat n 5 ->
  beq_nat (S (S n)) 7 = true.
Proof.
  intros n H.
  symmetry.
  simpl.
  apply H. Qed.



Fixpoint rev {X:Type} (l:list X) : list X :=
  match l with
  | nil => nil
  | cons h t => app (rev t) (cons h nil)
  end.

Search list.

Theorem app_nil_r : forall (X:Type), forall l:list X,
  l ++ [] = l.
Proof.
  intros X l.
  induction l as [| l' c IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem app_assoc : forall A (l m n:list A),
  l ++ m ++ n = (l ++ m) ++ n.
Proof.
  intros A l m n.
  induction l as [| l' c IHn'].
  - reflexivity.
  - simpl. rewrite <- IHn'. reflexivity.
Qed.

Theorem rev_app_distr : forall (X : Type), forall l1 l2 : list X,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros X l1 l2. induction l1 as [| l1' c IHn'].
  - simpl. rewrite -> app_nil_r. reflexivity.
  - simpl. rewrite -> IHn'. rewrite <- app_assoc. reflexivity.
Qed.

Theorem rev_involutive : forall X : Type, forall l : list X,
  rev (rev l) = l.
Proof.
  intros X l.
  induction l as [| l' c IHn'].
  - reflexivity.
  - simpl. rewrite -> rev_app_distr. simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem rev_exercise1 : forall (l l' : list nat),
  l = rev l' -> l' = rev l.
Proof.
  intros l l' H.
  symmetry.
  rewrite <- rev_involutive.
  rewrite <- H. reflexivity. Qed.




Example trans_eq_example : forall (a b c d e f : nat),
  [a;b] = [c;d] -> [c;d] = [e;f] -> [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  rewrite -> eq1. rewrite -> eq2. reflexivity. Qed.

Theorem trans_eq : forall (X:Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2. rewrite -> eq1. rewrite -> eq2.
  reflexivity. Qed.

Example trans_eq_example' : forall (a b c d e f : nat),
  [a;b] = [c;d] ->
  [c;d] = [e;f] ->
  [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  apply trans_eq with (m:=[c;d]).
  apply eq1. apply eq2. Qed.

Definition minustwo (n : nat) : nat :=
  match n with
  | O => 0
  | S 0 => 0
  | S (S n') => n'
  end.

Example trans_eq_exercise : forall (n m o p : nat),
  m = (minustwo o) ->
  (n + p) = m ->
  (n + p) = (minustwo o).
Proof.
  intros n m o p H1 H2. 
  rewrite -> H2.
  rewrite <- H1.
  reflexivity.
Qed.

Theorem S_injective : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H.
  inversion H.
  reflexivity.
Qed.

Theorem inversion_ex1 : forall (n m o : nat),
  [n; m] = [o; o] ->
  [n] = [m].
Proof.
  intros n m o H. inversion H. reflexivity. Qed.

Theorem inversion_ex2 : forall (n m : nat),
  [n] = [m] ->
  n = m.
Proof.
  intros n m H. inversion H as [Hnm]. reflexivity. Qed.

Example inversion_ex3 : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j ->
  y :: l = x :: j ->
  x = y.
Proof.
  intros X x y z l j H1 H2.
  inversion H2.
  reflexivity.
Qed.


Theorem beq_nat_0_l : forall n,
   beq_nat 0 n = true -> n = 0.
Proof.
  intros n.
  destruct n as [| n'].
  - intros H. reflexivity.
  - simpl.
    intros H.
    inversion H. Qed.

Theorem inversion_ex4 : forall (n : nat),
  S n = O -> 2 + 2 = 5.
Proof.
  intros n contra. inversion contra. Qed.

Theorem inversion_ex5 : forall (n m : nat),
  false = true ->
  [n] = [m].
Proof.
  intros n m contra. inversion contra. Qed.

Example inversion_ex6 : forall (X : Type) (x y z : X)
  (l j : list X),
  x :: y :: l = [] ->
  y :: l = z :: j ->
  x = z.
Proof.
  intros X x y z l j H1 H2.
  inversion H1. Qed.


Theorem f_equal : forall (A B : Type) (f : A -> B)
  (x y : A), x = y -> f x = f y.
Proof.
  intros A B f x y eq. rewrite eq. reflexivity. Qed.


Theorem S_inj : forall (n m : nat) (b : bool),
  beq_nat (S n) (S m) = b ->
  beq_nat n m = b.
Proof.
  intros n m b H. simpl in H. apply H. Qed.

Theorem silly3' : forall (n : nat),
  (beq_nat n 5 = true -> beq_nat (S (S n)) 7 = true) ->
  true = beq_nat n 5 ->
  true = beq_nat (S (S n)) 7.
Proof.
  intros n eq H.
  symmetry in H. apply eq in H. symmetry in H.
  apply H. Qed.

Theorem plus_n_Sm : forall n m : nat, S (n + m) = n + (S m).
Proof.
  intros n m. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity. Qed.


Theorem plus_n_n_injective : forall n m,
  n + n = m + m ->
  n = m.
Proof.
  intros n. induction n as [| n'].
  - intros m H. destruct m as [|m'].
    reflexivity.
    inversion H.
  - intros m. destruct m as [|m'].
    intros. inversion H.
    intros eq. inversion eq.
    rewrite <- plus_n_Sm in H0. rewrite <- plus_n_Sm in H0.
    inversion H0. apply IHn' in H1. rewrite -> H1. reflexivity.
Qed.


Theorem double_injective_FAILED: forall n m,
  double n = double m -> n = m.
Proof.
  intros n m. induction n as [| n'].
  - simpl. intros eq. destruct m as [| m'].
    + reflexivity.
    + inversion eq.
  - intros eq. destruct m as [| m'].
    + inversion eq.
    + apply f_equal.
Abort.

Theorem double_injective : forall n m,
  double n = double m -> n = m.
Proof.
  intros n. induction n as [| n'].
  - simpl. intros m eq. destruct m as [| m'].
    + reflexivity.
    + inversion eq.
  - simpl.
    intros m eq. destruct m as [| m'].
    + simpl. inversion eq.
    + apply f_equal. apply IHn'. inversion eq. reflexivity. Qed.

Theorem beq_nat_true : forall n m,
  beq_nat n m = true -> n = m.
Proof.
  intros n. induction n as [| n'].
  - intros m H. destruct m as [| m'].
    + reflexivity.
    + inversion H.
  - intros m eq. destruct m as [| m'].
    + inversion eq.
    + apply f_equal. apply IHn'. inversion eq. reflexivity. Qed.

Theorem double_injective_take2_FAILED : forall n m,
  double n = double m -> n = m.
Proof.
  intros n m. induction m as [| m'].
  - simpl. intros eq. destruct n as [| n'].
    + reflexivity.
    + inversion eq.
  - intros eq. destruct n as [| n'].
    + inversion eq.
    + apply f_equal.
Abort.

Theorem double_injective_take2: forall n m,
  double n = double m -> n = m.
Proof.
  intros n m.
  generalize dependent n.
  induction m as [| m'].
  - simpl. intros n eq. destruct n as [| n'].
    + reflexivity.
    + inversion eq.
  - intros n eq. destruct n as [| n'].
    + inversion eq.
    + apply f_equal.
      apply IHm'. inversion eq. reflexivity. Qed.

Inductive id : Type :=
  | Id : nat -> id.

Definition beq_id (x1 x2 : id) :=
  match x1, x2 with
  | Id n1, Id n2 => beq_nat n1 n2
  end.

Theorem beq_id_true : forall x y,
  beq_id x y = true -> x = y.
Proof.
  intros [m] [n]. simpl. intros H.
  assert (H' : m = n). { apply beq_nat_true. apply H. }
  rewrite H'. reflexivity.
Qed.

Fixpoint nth_error {X : Type} (l : list X) (n : nat)
                   : option X :=
  match l with
  | [] => None
  | a :: l' => if beq_nat n O then Some a else nth_error l' (pred n)
  end.

Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil => 0
  | cons _ l' => S (length l')
  end.

Theorem nth_error_after_last: forall (n : nat) (X : Type) (l : list X),
  length l = n -> nth_error l n = None.
Proof.
  intros n X l.
  generalize dependent n.
  induction l as [| l'].
  - simpl. intros n eq. reflexivity.
  - intros n eq. simpl. destruct n as [| n'].
    + simpl. inversion eq.
    + simpl. apply IHl. inversion eq. reflexivity. Qed.


Definition square n := n * n.

  
Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  intros n m p.
  induction n.
  reflexivity.
  simpl.
  rewrite IHn.
  rewrite plus_assoc.
  reflexivity.
Qed.

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  intros n m p.
  induction n.
  reflexivity.
  simpl.
  rewrite IHn.
  rewrite mult_plus_distr_r.
  reflexivity.
Qed.

Theorem plus_swap : forall n m p : nat,
  n + (m + p) = m + (n + p).
  Proof.
    intros n m p.
    rewrite -> plus_assoc.
    Check plus_assoc.
    rewrite -> plus_assoc. 
    assert (H: n + m = m + n).
    rewrite plus_comm.
    reflexivity.
    rewrite H.
    reflexivity.
Qed.

Theorem mult_n_Sm : forall n m : nat, n * S m = n + n * m.
  Proof.
    intros n m.
    induction n.
    reflexivity.
    simpl.
    rewrite -> IHn.
    rewrite plus_swap.
    reflexivity.
Qed.

Theorem mult_comm : forall m n : nat,
 m * n = n * m.
  Proof.
    intros m n.
    induction n as [| n'].
    -
      rewrite mult_0_r.
      reflexivity.
    -
      simpl.
      rewrite <- IHn'.
      rewrite -> mult_n_Sm.
      reflexivity.
Qed.

Lemma square_mult : forall n m, square (n * m)
  = square n * square m.
Proof.
  intros n m.
  unfold square.
  rewrite mult_assoc.
  assert (H : n * m * n = n * n * m).
  { rewrite mult_comm. apply mult_assoc. }
  rewrite H. rewrite mult_assoc. reflexivity.
Qed.

Definition foo (x : nat) := 5.

Fact silly_fact1: forall m, foo m + 1 = foo (m + 1) + 1.
Proof.
  intros m.
  simpl.
  reflexivity.
Qed.

Definition bar x :=
  match x with
  | O => 5
  | S _ => 5
  end.

Fact silly_fact_2_FAILED : 
  forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  simpl.
Abort.

Fact silly_fact_2 : forall m,
  bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  destruct m.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Fact silly_fact_2' : forall m,
  bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  unfold bar.
  destruct m.
  - reflexivity.
  - reflexivity.
Qed.

Definition sillyfun (n : nat) : bool :=
  if beq_nat n 3 then false
  else if beq_nat n 5 then false
  else false.

Theorem sillyfun_false : forall (n : nat),
  sillyfun n = false.
Proof.
  intros n. unfold sillyfun.
  destruct (beq_nat n 3).
    - reflexivity.
    - destruct (beq_nat n 5).
      + reflexivity.
      + reflexivity. Qed.

Fixpoint split {X Y : Type} (l : list (X * Y))
  : (list X) * (list Y) :=
  match l with
  | [] => ([], [])
  | (x, y) :: t =>
    match split t with
    | (lx, ly) => (x :: lx, y :: ly)
    end
  end.

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
           : list (X*Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: (combine tx ty)
  end.


Theorem combine_split : forall X Y (l : list (X * Y))
  l1 l2, split l = (l1, l2) -> combine l1 l2 = l.
Proof.
  intros X Y l l1 l2 eq.
  induction l as [| l'].
  - simpl in eq. inversion eq. reflexivity.
  - destruct (combine l1 l2).
    +
Abort.

Definition sillyfun1 (n : nat) : bool :=
  if beq_nat n 3 then true
  else if beq_nat n 5 then true
  else false.

Theorem sillyfun1_odd_FAILED : forall (n : nat),
  sillyfun1 n = true -> oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (beq_nat n 3).
Abort.

Theorem sillyfun1_odd : forall (n : nat),
  sillyfun1 n = true -> oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (beq_nat n 3) eqn:Heqe3.
  - apply beq_nat_true in Heqe3.
    rewrite -> Heqe3. reflexivity.
  - destruct (beq_nat n 5) eqn:Heqe5.
    + apply beq_nat_true in Heqe5.
      rewrite -> Heqe5. reflexivity.
    + inversion eq. Qed.

Theorem bool_fn_applied_thrice :
  forall (f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Proof.
  intros f b. destruct b.
  - destruct (f true) eqn:ft.
    + rewrite ft. rewrite ft. reflexivity.
    + destruct (f false) eqn:ff.
      * rewrite ft. reflexivity.
      * rewrite ff. reflexivity.
  - destruct (f false) eqn:ff.
    + destruct (f true) eqn:ft.
      * rewrite ft. reflexivity.
      * rewrite ff. reflexivity.
    + rewrite ff. rewrite ff. reflexivity.
Qed.

Theorem beq_nat_sym : forall (n m : nat),
  beq_nat n m = beq_nat m n.
Proof.
  intros n.
  induction n as [| n'].
  - destruct m as [| m'].
    + reflexivity.
    + reflexivity.
  - destruct m as [| m'].
    + reflexivity.
    + apply IHn'.
Qed.


Theorem beq_nat_trans : forall n m p,
  beq_nat n m = true ->
  beq_nat m p = true ->
  beq_nat n p = true.
Proof.
  intros n m p H1 H2.
  generalize dependent n.
  induction m as [| m'].
  - simpl. intros n eq. destruct n as [| n'].
    + apply H2.
    + inversion eq.
  - intros n eq. destruct n as [| n'].
    + inversion eq.
    + rewrite <- eq. apply f_equal. destruct p as [| p'].
      * inversion H2.
      * simpl in H2. apply beq_nat_true in H2.
        simpl in eq. symmetry. apply f_equal. apply H2.
Qed.




