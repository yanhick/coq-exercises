Set Warnings "-notation-overridden,-parsing".
Require Export Logic.
Require Coq.omega.Omega.

Inductive ev : nat -> Prop :=
  | ev_0 : ev 0
  | ev_SS : forall n : nat, ev n -> ev (S (S n)).

Fail Inductive wrong_ev (n : nat) : Prop :=
  | wrong_ev_0 : wrong_ev 0
  | wrong_ev_SS : forall n, wrong_ev n -> wrong_ev (S (S n)).

Theorem ev_4 : ev 4.
Proof. apply ev_SS. apply ev_SS. apply ev_0. Qed.

Theorem ev_4' : ev 4.
Proof. apply (ev_SS 2 (ev_SS 0 ev_0)). Qed.

Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
  intros n. simpl. intros Hn.
  apply ev_SS. apply ev_SS. apply Hn.
Qed.

Theorem ev_double : forall n,
  ev (double n).
Proof.
  intros n. induction n.
  - simpl. apply ev_0.
  - simpl. apply ev_SS. apply IHn.
Qed.

Theorem ev_minus2 : forall n,
  ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  inversion E as [| n' E'].
  - simpl. apply ev_0.
  - simpl. apply E'. Qed.

Theorem ev_minus2' : forall n,
  ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  destruct E as [| n' E'].
  - simpl. apply ev_0.
  - simpl. apply E'.
Qed.

Theorem evSS_ev : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E.
  destruct E as [| n' E'].
Abort.

Theorem evSS_ev : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E.
  inversion E as [| n' E'].
  apply E'.
Qed.


Theorem one_not_even : ~ ev 1.
Proof.
  intros H. inversion H. Qed.

Theorem SSSSev_even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  intros n H. 
  inversion H as [| n' E' g].
  inversion E'.
  apply H1.
Qed.

Theorem even5_nonsense :
  ev 5 -> 2 + 2 = 9.
Proof.
  intros H. simpl. inversion H.
  inversion H1. inversion H3.
Qed.

Lemma ev_even_firsttry : forall n,
  ev n -> exists k, n = double k.
Proof.
  intros n E. inversion E as [| n' E'].
  - exists 0. reflexivity.
  - simpl.
    assert (I : (exists k', n' = double k') ->
                (exists k, S (S n') = double k)).
    { intros [k' Hk']. rewrite Hk'. exists (S k').
      reflexivity. }
    apply I.
Admitted.

Lemma ev_even : forall n,
  ev n -> exists k, n = double k.
Proof.
  intros n E.
  induction E as [| n' E' IH].
  - exists 0. reflexivity.
  - destruct IH as [k' Hk'].
    rewrite Hk'. exists (S k'). reflexivity.
Qed.

Theorem ev_even_iff : forall n,
  ev n <-> exists k, n = double k.
Proof.
  intros n. split.
  - apply ev_even.
  - intros [k Hk]. rewrite Hk. apply ev_double.
Qed.

Search plus.

Theorem ev_sum : forall n m, ev n -> ev m -> ev (n + m).
Proof.
  intros n m H1 H2.
  induction H1.
  - simpl. apply H2.
  - induction H2.
    + rewrite plus_comm. simpl.
      apply ev_SS. apply H1.
    + simpl. apply ev_SS. apply IHev.
Qed.

Theorem ev_ev__ev : forall n m,
  ev (n + m) -> ev n -> ev m.
Proof.
  intros n m H1 H2. induction H2.
  - simpl in H1. apply H1.
  - apply IHev. simpl in H1. apply evSS_ev in H1.
    apply H1.
Qed.

Search plus.

Theorem add_0_is_0 : forall (n m : nat),
  n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros n m H. induction n.
  - split.
    + reflexivity.
    + simpl in H. apply H.
  - split.
    + inversion H.
    + inversion H.
Qed.

Theorem ev_evSS : forall n,
  ev n -> ev (S (S n)).
Proof.
  intros n H.
  apply ev_SS.
  apply H.
Qed.

Theorem add_0_is_Z : forall n,
  n = 0 -> n + n = 0.
Proof.
  intros n H. induction n.
  - reflexivity.
  - inversion H.
Qed.

Search double.


Module Playground.

Inductive le : nat -> nat -> Prop :=
  | le_n : forall n, le n n
  | le_S : forall n m, (le n m) -> (le n (S m)).

Notation "m <= n" := (le m n).

Theorem test_le1 : 3 <= 3.
Proof.
  apply le_n. Qed.

Theorem test_le2 : 3 <= 6.
Proof.
  apply le_S. apply le_S. apply le_S. apply le_n. Qed.

Theorem test_le3 : (2 <= 1) -> 2 + 2 = 5.
Proof.
  intros H. inversion H. inversion H2. Qed.

End Playground.

Definition lt (n m : nat) := le (S n) m.

Notation "m < n" := (lt m n).

Inductive square_of : nat -> nat -> Prop :=
  | sq : forall n: nat, square_of n (n * n).

Theorem test_square_of : square_of 4 16.
Proof.
 apply sq. Qed.

Inductive next_nat : nat -> nat -> Prop :=
  | nn : forall n : nat, next_nat n (S n).

Inductive next_even : nat -> nat -> Prop :=
  | ne_1 : forall n, ev (S n) -> next_even n (S n)
  | ne_2 : forall n, ev (S (S n)) -> next_even n (S (S n)).

Inductive total_relation : nat -> nat -> Prop :=
  | tr : forall n m, total_relation n m.

Theorem test_total_relation : total_relation 1 1.
Proof.
  apply tr. Qed.

Inductive empty_relation : nat -> nat -> Prop :=
  | er : forall n, lt n n -> empty_relation n n.

Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  intros m n o Hmn Hno.
  induction Hno.
  - apply Hmn.
  - apply le_S in IHHno. apply IHHno.
Qed.

Theorem le_n_0 : forall n,
  n <= 0 -> n = 0.
Proof.
  intros n H. induction n.
  - reflexivity.
  - inversion H.
Qed.

Theorem O_le_n : forall n,
  0 <= n.
Proof.
  intros n. induction n.
  - apply le_n.
  - inversion IHn.
    + apply le_S. apply le_n.
    + apply le_S. apply le_S. apply H.
Qed.

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
  intros n m Hsnsm. inversion Hsnsm.
  - apply le_n.
  - apply (le_trans n (S n)).
    + apply le_S. apply le_n.
    + apply H0.
Qed.


Theorem le_plus_l : forall a b,
  a <= a + b.
Proof.
  intros a b. induction b.
  - rewrite plus_comm. simpl. apply le_n.
  - inversion IHb.
    + rewrite <- H. rewrite <- plus_n_Sm.
      rewrite <- H. apply le_S. apply le_n.
    + rewrite <- plus_n_Sm. rewrite <- H.
      apply le_S. apply le_S. apply H0.
Qed.

Theorem lt_1 : forall n m,
  S n < m -> n < m.
Proof.
  intros n m H. inversion H.
  - apply le_S. apply le_n.
  - apply le_S. apply le_S in H0. 
    apply Sn_le_Sm__n_le_m in H0.
    apply H0.
Qed.



Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m -> n1 < m /\ n2 < m.
Proof.
  intros n1 n2 m H.
  split.
  - induction n2.
    + rewrite plus_comm in H. simpl in H. apply H.
    + apply IHn2. rewrite <- plus_n_Sm in H.
      apply lt_1 in H. apply H.
  - induction n1.
    + simpl in H. apply H.
    + apply IHn1. 
      rewrite plus_comm in H. 
      rewrite <- plus_n_Sm in H.
      apply lt_1 in H. rewrite plus_comm in H.
      apply H.
Qed.

Theorem lt_S : forall n m,
  n < m -> n < S m.
Proof.
  intros n m H. inversion H.
  - apply le_S. apply le_n.
  - apply le_S. apply le_S in H0. 
    rewrite -> H1 in H0. rewrite -> H1.
    apply H0.
Qed.

Search leb.

Theorem leb_n_0 : forall n,
  leb n 0 = true <-> n = 0.
Proof.
  intros n.
  split.
  - intro H. induction n.
    + reflexivity.
    + inversion H.
  - intro H. induction n.
    + reflexivity.
    + simpl. inversion H.
Qed.

Theorem n_0 : forall n,
  n <= 0 <-> n = 0.
Proof.
  intros n. split.
  - intro H. induction n.
    + reflexivity.
    + inversion H.
  - intro H. induction n.
    + reflexivity.
    + inversion H.
Qed.

Theorem leb_complete : forall n m,
  leb n m = true -> n <= m.
Proof.
  intros n m H. induction m.
  - rewrite n_0. apply leb_n_0. apply H.
  -  apply le_S. apply IHm. inversion H.
Admitted.

Theorem leb_refl : forall n,
  leb n n = true.
Proof.
  intro n. induction n.
  - reflexivity.
  - simpl. apply IHn.
Qed.

Theorem leb_correct : forall n m,
  n <= m -> leb n m = true.
Proof.
  intros n m H. induction m.
  - rewrite leb_n_0. inversion H. reflexivity.
  - inversion H.
    + apply leb_refl.
    + Admitted.

Inductive reg_exp {T : Type} : Type :=
| EmptySet : reg_exp
| EmptyStr : reg_exp
| Char : T -> reg_exp
| App : reg_exp -> reg_exp -> reg_exp
| Union : reg_exp -> reg_exp -> reg_exp
| Star : reg_exp -> reg_exp.


Inductive exp_match {T} : list T -> reg_exp -> Prop :=
  | MEmpty : exp_match [] EmptyStr
  | MChar : forall x, exp_match [x] (Char x)
  | MApp : forall s1 re1 s2 re2,
            exp_match s1 re1 ->
            exp_match s2 re2 ->
            exp_match (s1 ++ s2) (App re1 re2)
  | MUnionL : forall s1 re1 re2,
                exp_match s1 re1 ->
                exp_match s1 (Union re1 re2)
  | MUnionR : forall re1 s2 re2,
                exp_match s2 re2 ->
                exp_match s2 (Union re1 re2)
  | MStar0 : forall re, exp_match [] (Star re)
  | MStarApp : forall s1 s2 re,
                exp_match s1 re ->
                exp_match s2 (Star re) ->
                exp_match (s1 ++ s2) (Star re).

Notation "s =~ re" := (exp_match s re) (at level 80).

Example reg_exp_ex1 : [1] =~ Char 1.
Proof.
  apply MChar.
Qed.

Example reg_exp_ex2 : [1; 2] =~ App (Char 1) (Char 2).
Proof.
  apply (MApp [1] _ [2]).
  - apply MChar.
  - apply MChar.
Qed.

Example reg_exp_ex3 : ~ ([1;2] =~ Char 1).
Proof.
  intros H. inversion H.
Qed.

Fixpoint reg_exp_of_list {T} (l : list T) :=
  match l with
  | [] => EmptyStr
  | x :: l' => App (Char x) (reg_exp_of_list l')
end.

Example reg_exp_ex4 : [1; 2; 3] =~ reg_exp_of_list [1; 2; 3].
Proof.
  simpl. apply (MApp [1]).
  { apply MChar. }
  apply (MApp [2]).
  { apply MChar. }
  apply (MApp [3]).
  { apply MChar. }
  apply MEmpty.
Qed.

Lemma MStar1 : forall T s (re : @reg_exp T),
  s =~ re -> s =~ Star re.
Proof.
  intros T s re H.
  rewrite <- (app_nil_r _ s).
  apply (MStarApp s [] re).
  - apply H.
  - apply MStar0.
Qed.

Lemma empty_is_empty : forall T (s : list T),
  ~ (s =~ EmptySet).
Proof.
  intros T s H. induction s.
  - inversion H.
  - inversion H.
Qed.

Lemma MUnion' : forall T (s : list T) (re1 re2 : @reg_exp T),
  s =~ re1 \/ s =~ re2 -> s =~ Union re1 re2.
Proof.
  intros T s re1 re2 H.
  inversion H.
  - apply MUnionL. apply H0.
  - apply MUnionR. apply H0.
Qed.

Search In.

Lemma head_same_concat : forall T (x : T) (xs : list T),
  x :: xs = [x] ++ xs.
Proof.
  intros T x xs. induction xs.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Lemma MStar' : forall T (ss : list (list T)) (re : reg_exp),
  (forall s, In s ss -> s =~ re) -> fold app ss [] =~ Star re.
Proof.
  intros T ss re H. induction ss.
  - apply MStar0.
  - rewrite -> head_same_concat. simpl. apply MStarApp.
    + apply H. simpl. left. reflexivity.
    + apply IHss. intros s H1. apply H. simpl. right. apply H1.
Qed.

Lemma reg_exp_of_list_match_itself : forall T (l : list T),
  l =~ reg_exp_of_list l.
Proof.
  intros T l. induction l.
  - simpl. apply MEmpty.
  - simpl. apply (MApp [x] _ l).
    + apply MChar.
    + apply IHl.
Qed.

Lemma reg_exp_of_list_spec : forall T (s1 s2 : list T),
  s1 = s2 <-> s1 =~ reg_exp_of_list s2.
Proof.
  split.
  - intro H. induction s2.
    + simpl. rewrite -> H. apply MEmpty.
    + simpl. induction s1.
      * rewrite -> H. apply (MApp [x] _ s2).
        apply MChar.
        apply reg_exp_of_list_match_itself.
      * rewrite -> H.
        apply (MApp [x] _ s2).
        apply MChar.
        apply reg_exp_of_list_match_itself.
  - generalize dependent s1. induction s2;
    intros.
    + inversion H. simpl. reflexivity.
    + inversion H. inversion H3. subst. simpl.
      simpl in H.  apply f_equal. apply IHs2.
      apply H4.
Qed.

Fixpoint re_chars {T} (re : reg_exp) : list T :=
  match re with
  | EmptySet => []
  | EmptyStr => []
  | Char x => [x]
  | App re1 re2 => re_chars re1 ++ re_chars re2
  | Union re1 re2 => re_chars re1 ++ re_chars re2
  | Star re => re_chars re
  end.

Theorem in_re_match : 
  forall T (s : list T) (re : reg_exp) (x : T),
  s =~ re -> In x s -> In x (re_chars re).
Proof.
  intros T s re x Hmatch Hin.
  induction Hmatch
    as [| x'
        | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
        | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2].
  - apply Hin.
  - apply Hin.
  - simpl. rewrite In_app_iff in *. 
    destruct Hin as [Hin | Hin].
    + left. apply (IH1 Hin).
    + right. apply (IH2 Hin).
  - simpl. rewrite In_app_iff.
    left. apply (IH Hin).
  - simpl. rewrite In_app_iff.
    right. apply (IH Hin).
  - destruct Hin.
  - simpl. rewrite In_app_iff in Hin.
    destruct Hin as [Hin | Hin].
    + apply (IH1 Hin).
    + apply (IH2 Hin).
Qed.

Fixpoint re_not_empty {T : Type} (re : @reg_exp T) : bool :=
  match re with
  | EmptySet => false
  | EmptyStr => true
  | Char x => true
  | App re1 re2 => andb (re_not_empty re1) (re_not_empty re2)
  | Union re1 re2 => orb (re_not_empty re1) (re_not_empty re2)
  | Star re => true
  end.

Search orb.

Lemma list_eq_concat_empty : forall T (l : list T),
  l = [] ++ l.
Proof.
  intros T l. reflexivity.
Qed.

Search andb.

Lemma re_not_empty_correct : forall T (re : @reg_exp T),
  (exists s, s =~ re) <-> re_not_empty re = true.
Proof.
  intros T re. split.
  - intro H. induction re.
    + inversion H. simpl. inversion H0.
    + reflexivity.
    + reflexivity.
    + simpl. apply andb_true_intro. split.
      * apply IHre1. inversion H. inversion H0. exists s1.
        apply H4.
      * apply IHre2. inversion H. inversion H0. exists s2.
        apply H5.
    + simpl. apply Bool.orb_true_intro. inversion H. inversion H0.
      * left. apply IHre1. exists x. apply H3.
      * right. apply IHre2. exists x. apply H3.
    + reflexivity.
  - intro H. induction re.
    + simpl. inversion H.
    + exists []. apply MEmpty.
    + exists [t]. apply MChar.
    + simpl in H. apply andb_true_iff in H. inversion H.
      apply IHre1 in H0. inversion H0.
      apply IHre2 in H1. inversion H1.
      exists (x ++ x0). apply (MApp x _ x0).
      * apply H2.
      * apply H3.
    + simpl in H. apply orb_true_iff in H. inversion H.
      * apply IHre1 in H0. inversion H0.
        exists x. apply MUnionL. apply H1.
      * apply IHre2 in H0. inversion H0.
        exists x. apply MUnionR. apply H1.
    + exists []. apply MStar0.
Qed.

Lemma star_app : forall T (s1 s2 : list T) (re : @reg_exp T),
  s1 =~ Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.
  induction H1
    as [| x' | s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
        | s1 re1 re2 Hmatch IH | re1 s2' re2 Hmatch IH
        | re'' | s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].
  - simpl. intros H. apply H.
  Abort.

Lemma star_app : forall T (s1 s2 : list T) (re re' : reg_exp),
  re' = Star re -> s1 =~ re' -> s2 =~ Star re -> s1 ++ s2 =~ Star re.
Abort.

Lemma star_app : forall T (s1 s2 : list T) (re : reg_exp),
  s1 =~ Star re -> s2 =~ Star re -> s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.
  remember (Star re) as re'.
  generalize dependent s2.
  induction H1
    as [| x' | s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
        | s1 re1 re2 Hmatch IH | re1 s2' re2 Hmatch IH
        | re'' | s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].
  - inversion Heqre'.
  - inversion Heqre'.
  - inversion Heqre'.
  - inversion Heqre'.
  - inversion Heqre'.
  - inversion Heqre'. intros s H. apply H.
  - inversion Heqre'. rewrite H0 in IH2, Hmatch1.
    intros s2 H1. rewrite <- app_assoc.
    apply MStarApp.
    + apply Hmatch1.
    + apply IH2.
      * reflexivity.
      * apply H1.
Qed.

Search app.

Lemma MStar'' : forall T (s : list T) (re : reg_exp),
  s =~ Star re ->  
  exists ss : list (list T), 
    s = fold app ss [] /\ forall s', In s' ss -> s' =~ re.
Proof.
  intros T s re H. remember (Star re). remember [s]. remember (App re re).
  induction H.
  - inversion Heqr.
  - inversion Heqr.
  - inversion Heqr.
  - inversion Heqr.
  - inversion Heqr.
  - inversion Heqr. exists []. split.
    + simpl. reflexivity.
    + intros s' H1. simpl in H1.
      inversion H1.
  - exists l. split.
    + rewrite -> Heql. simpl. simpl. 
      rewrite <- app_assoc. rewrite -> app_nil_r.
      reflexivity.
    + intros. rewrite -> Heql in H1. simpl in H1.
      inversion H1.
      * inversion Heqr. inversion H0.
        rewrite <- H2. rewrite <- H3. rewrite -> app_nil_r.
        rewrite -> H4 in H. apply H.
        rewrite <- H2.
Abort.

Module Pumping.
Import Coq.omega.Omega.

Fixpoint pumping_constant {T} (re : @reg_exp T) : nat :=
  match re with
  | EmptySet => 0
  | EmptyStr => 1
  | Char _ => 2
  | App re1 re2 =>
      pumping_constant re1 + pumping_constant re2 
  | Union re1 re2 =>
      pumping_constant re1 + pumping_constant re2
  | Star _ => 1
  end.

Fixpoint napp {T} (n : nat) (l : list T) : list T :=
  match n with
  | 0 => []
  | S n' => l ++ napp n' l
  end.

Lemma napp_plus : forall T (n m : nat) (l : list T),
  napp (n + m) l = napp n l ++ napp m l.
Proof.
  intros T n m l.
  induction n as [|n IHn].
  - reflexivity.
  - simpl. rewrite IHn, app_assoc. reflexivity.
Qed.

Lemma pumping : forall T (re : @reg_exp T) s,
  s =~ re -> 
  pumping_constant re <= length s ->
  exists s1 s2 s3, 
    s = s1 ++ s2 ++ s3 /\
    not (s2 = []) /\
    forall m, s1 ++ napp m s2 ++ s3 =~ re.
Proof.
  intros T re s Hmatch.
  induction Hmatch
    as [ | x | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
       | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
       | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2 ].
  - simpl. omega.
  - simpl. omega.
  - remember (App re1 re2). simpl. intro H. inversion H.
    +
Abort.

Theorem filter_not_empty_in : forall n l,
  filter (beq_nat n) l <> [] -> In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
  - simpl. intros H. apply H. reflexivity.
  - simpl. destruct (beq_nat n m) eqn:H.
    + intros _. rewrite beq_nat_true_iff in H. rewrite H.
      left. reflexivity.
    + intros H'. right. apply IHl'. apply H'.
Qed.

Inductive reflect (P : Prop) : bool -> Prop :=
  | ReflectT : P -> reflect P true
  | ReflectF : ~ P -> reflect P false.

Theorem iff_reflect : forall P b, (P <-> b = true) -> reflect P b.
Proof.
  intros P b H. destruct b.
  - apply ReflectT. rewrite H. reflexivity.
  - apply ReflectF. rewrite H. intros H'. inversion H'.
Qed.

Theorem reflect_iff : forall P b, reflect P b -> (P <-> b = true).
Proof.
  intros P b H. split.
  - intro P'. destruct b.
    + reflexivity.
    + inversion H. apply H0 in P'. inversion P'.
  - intros H'. inversion H.
    + apply H0.
    + symmetry in H1. rewrite -> H1 in H'. inversion H'.
Qed.

Lemma beq_natP : forall n m, reflect (n = m) (beq_nat n m).
Proof.
  intros n m. apply iff_reflect. rewrite beq_nat_true_iff. reflexivity.
Qed.

Theorem filter_not_empty_In' : forall n l,
  filter (beq_nat n) l <> [] -> In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
  - simpl. intros H. apply H. reflexivity.
  - simpl. destruct (beq_natP n m) as [H | H].
    + intros _. rewrite H. left. reflexivity.
    + intros H'. right. apply IHl'. apply H'.
Qed.

Fixpoint count n l :=
  match l with
  | [] => 0
  | m :: l' => (if beq_nat n m then 1 else 0) + count n l'
  end.

Search beq_nat.

Lemma is_in_rest : forall T (l : list T) (n x : T),
  In n (x :: l) -> n <> x -> In n l.
Proof.
  intros T l n x H1 H2.
  inversion H1.
  - rewrite -> H in H2. unfold not in H2.
    rewrite -> H in H1. simpl in H1.
    inversion H1.
    + apply H2 in H0. inversion H0.
    + apply H0.
  - apply H.
Qed.

Theorem beq_natP_practice : forall n l,
  count n l = 0 -> ~ ( In n l ).
Proof.
  intros n l H H'. induction l.
  - simpl in H. simpl in H'. apply H'.
  - destruct (beq_natP n x).
    + rewrite <- H0 in H'. simpl in H'. 
      rewrite <- H0 in H.
      simpl in H.
      rewrite Nat.eqb_refl in H. simpl in H.
      inversion H.
    + simpl in H.
      apply IHl.
      * rewrite <- Nat.eqb_neq in H0. 
        rewrite H0 in H.
        simpl in H. apply H.
      * apply is_in_rest in H'.
        apply H'. apply H0.
Qed.

Inductive nostutter {X:Type} : list X -> Prop :=
  | NoStutterNil : nostutter []
  | NoStutterSingleton : forall x, nostutter [x]
  | NoStutterCons : forall (x y : X) (l : list X),
      nostutter (y :: l) -> x <> y -> nostutter (x :: y :: l).

Example test_nostutter_1 : nostutter [3;1;4;1;5;6].
Proof.
  repeat apply NoStutterCons.
  apply NoStutterSingleton.
  apply beq_nat_false_iff;  auto.
  apply beq_nat_false_iff;  auto.
  apply beq_nat_false_iff;  auto.
  apply beq_nat_false_iff;  auto.
  apply beq_nat_false_iff;  auto.
Qed.

Example test_nostutter_2 : nostutter (@nil nat).
Proof.
  apply NoStutterNil. Qed.

Example test_nostutter_3 : nostutter [5].
Proof.
  apply NoStutterSingleton. Qed.

Example test_nostutter_4 : not (nostutter [3;1;1;4]).
Proof.
  intro.
  repeat match goal with
    h: nostutter _ |- _ => inversion h; clear h; subst
  end.
  contradiction H5. auto.
Qed.

End Pumping.



