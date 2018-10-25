 Set Warnings "-notation-overridden,-parsing".
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.
Import ListNotations.
Require Import Maps.
Require Import Imp.

Definition aequiv (a1 a2 : aexp) : Prop :=
  forall (st : state), aeval st a1 = aeval st a2.

Definition bequiv (b1 b2 : bexp) : Prop :=
  forall (st : state), beval st b1 = beval st b2.

Theorem aequiv_example: aequiv (X - X) 0.
Proof.
  intros st. simpl. omega.
Qed.

Theorem bequiv_example: bequiv (X - X = 0) true.
Proof.
  intros st. unfold beval.
  rewrite aequiv_example. reflexivity.
Qed.

Definition cequiv (c1 c2 : com) : Prop :=
  forall (st st' : state),
    (c1 / st \\ st') <-> (c2 / st \\ st').

Theorem skip_left : forall c,
  cequiv (SKIP;; c) c.
Proof.
  intros c st st'.
  split; intros H.
  - inversion H; subst.
    inversion H2. subst.
    assumption.
  - apply E_Seq with st.
    apply E_Skip.
    assumption.
Qed.

Theorem skip_right : forall c,
  cequiv (c ;; SKIP) c.
Proof.
  intros c st st'.
  split; intros H.
  - inversion H; subst.
    inversion H5. subst.
    assumption.
  - apply E_Seq with st'.
    assumption.
    apply E_Skip.
Qed.


Theorem IFB_true_simple : forall c1 c2,
  cequiv (IFB BTrue THEN c1 ELSE c2 FI)
  c1.
Proof.
  intros c1 c2.
  split; intros H.
  - inversion H; subst. assumption. inversion H5.
  - apply E_IfTrue. reflexivity. assumption. Qed.

Theorem IFB_true : forall b c1 c2,
  bequiv b BTrue ->
  cequiv 
    (IFB b THEN c1 ELSE c2 FI) c1.
Proof.
  intros b c1 c2 Hb.
  split; intros H.
  - inversion H; subst.
    + assumption.
    + unfold bequiv in Hb. simpl in Hb.
      rewrite Hb in H5.
      inversion H5.
  - apply E_IfTrue; try assumption.
    unfold bequiv in Hb. simpl in Hb.
    rewrite Hb. reflexivity. Qed.

Theorem IFB_false : forall b c1 c2,
  bequiv b BFalse ->
  cequiv (IFB b THEN c1 ELSE c2 FI)
  c2.
Proof.
  intros b c1 c2 Hb.
  split; intros H.
  - inversion H; subst.
    + unfold bequiv in Hb. simpl in Hb.
      rewrite Hb in H5. inversion H5.
    + assumption.
  - apply E_IfFalse; try assumption.
    unfold bequiv in Hb. simpl in Hb.
    rewrite Hb. reflexivity. Qed.

Search negb.

Theorem swap_if_branches : forall b e1 e2,
  cequiv
    (IFB b THEN e1 ELSE e2 FI)
    (IFB BNot b THEN e2 ELSE e1 FI).
Proof.
  intros b e1 e2.
  split; intros H.
  - inversion H; subst.
    + apply E_IfFalse.
      * simpl. rewrite H5. simpl. reflexivity.
      * assumption.
    + apply E_IfTrue.
      * simpl. rewrite H5. reflexivity.
      * assumption.
 - inversion H; subst.
    + apply E_IfFalse.
      * simpl in H5. 
        symmetry in H5. 
        apply negb_sym in H5. simpl in H5.
        assumption.
      * assumption.
    + apply E_IfTrue.
      simpl in H5.
      symmetry in H5. 
      apply negb_sym in H5. simpl in H5.
      assumption.
      * assumption.
Qed.

Theorem WHILE_false : forall b c,
  bequiv b BFalse ->
  cequiv
    (WHILE b DO c END)
    SKIP.
Proof.
  intros b c Hb. split; intros H.
  - inversion H; subst.
    + apply E_Skip.
    + rewrite Hb in H2. 
      inversion H2.
  - inversion H; subst.
    apply E_WhileFalse.
    rewrite Hb.
    reflexivity. Qed.

Lemma WHILE_true_nonterm : forall b c st st',
  bequiv b BTrue ->
  ~ ( ( WHILE b DO c END) / st \\ st' ).
Proof.
  intros b c st st' Hb.
  intros H.
  remember (WHILE b DO c END) as cw eqn:Heqcw.
  induction H;
  inversion Heqcw; subst; clear Heqcw.
  - unfold bequiv in Hb.
    rewrite Hb in H. inversion H.
  - apply IHceval2. reflexivity. Qed.

Theorem WHILE_true : forall b c,
  bequiv b true ->
    cequiv
      (WHILE b DO c END)
      (WHILE true DO SKIP END).
Proof.
  intros b c H. split.
  - intros H1. apply WHILE_true_nonterm in H1.
    + inversion H1.
    + assumption.
  - intros H1. apply WHILE_true_nonterm in H1.
    + inversion H1.
    + simpl. unfold bequiv. reflexivity.
Qed.

Theorem loop_unrolling : forall b c,
  cequiv
    (WHILE b DO c END)
    (IFB b THEN (c ;; WHILE b DO c END) ELSE SKIP FI).
Proof.
  intros b c st st'.
  split; intros Hce.
  - inversion Hce; subst.
    + apply E_IfFalse. assumption. apply E_Skip.
    + apply E_IfTrue. assumption.
      apply E_Seq with (st' := st'0). assumption. assumption.
  - inversion Hce; subst.
    + inversion H5; subst.
      apply E_WhileTrue with (st' := st'0).
      assumption. assumption. assumption.
    + inversion H5; subst. apply E_WhileFalse. assumption. Qed.

Theorem seq_assoc : forall c1 c2 c3,
  cequiv ((c1 ;; c2) ;; c3) (c1 ;; (c2 ;; c3)).
Proof.
  intros c1 c2 c3.
  split; intros H;
  inversion H; subst.
  - inversion H2; subst.
    eapply E_Seq.
    + apply H3.
    + eapply E_Seq.
      * apply H7.
      * apply H5.
  - inversion H5; subst.
    eapply E_Seq.
    + eapply E_Seq.
      * apply H2.
      * apply H3.
    + assumption.
Qed.

Theorem identity_assignment : forall (X : string),
  cequiv
    (X ::= X)
    SKIP.
Proof.
  intros. split; intro H.
  - inversion H; subst. simpl.
    replace (st & { X --> st X }) with st.
    + constructor.
    + apply functional_extensionality. intro.
      rewrite t_update_same; reflexivity.
  - replace st' with (st' & { X --> aeval st' X }).
    + inversion H. subst. apply E_Ass. reflexivity.
    + apply functional_extensionality. intro.
      rewrite t_update_same. reflexivity.
Qed.

Theorem assign_aequiv : forall (X : string) e,
  aequiv X e -> cequiv SKIP (X ::= e).
Proof.
  intros X e Ha.
  split; intros H.
  - replace st' with (st' & { X --> aeval st' X }).
    + inversion H. subst. rewrite -> Ha. apply E_Ass.
      reflexivity.
    + apply functional_extensionality. intro.
      rewrite t_update_same. reflexivity.
  - inversion H; subst. simpl.
    replace (st & {X --> aeval st e}) with st.
    + constructor.
    + apply functional_extensionality. intro.
      rewrite <- Ha.
      rewrite t_update_same. reflexivity.
Qed.

Lemma refl_aequiv : forall (a : aexp), aequiv a a.
Proof.
  intros a st. reflexivity. Qed.

Lemma sym_aequiv : forall (a1 a2 : aexp),
  aequiv a1 a2 -> aequiv a2 a1.
Proof.
  intros a1 a2 H. intros st. symmetry. apply H. Qed.

Lemma trans_aequiv : forall (a1 a2 a3 : aexp),
  aequiv a1 a2 -> aequiv a2 a3 -> aequiv a1 a3.
 Proof.
  unfold aequiv. intros a1 a2 a3 H12 H23 st.
  rewrite (H12 st). rewrite (H23 st). reflexivity. Qed.


Lemma refl_bequiv : forall (b : bexp), bequiv b b.
Proof.
  unfold bequiv. intros b st. reflexivity. Qed.

Lemma sym_bequiv : forall (b1 b2 : bexp),
  bequiv b1 b2 -> bequiv b2 b1.
Proof.
  unfold bequiv. intros b1 b2 H. intros st. symmetry. apply H. Qed.

Lemma trans_bequiv : forall (b1 b2 b3 : bexp),
  bequiv b1 b2 -> bequiv b2 b3 -> bequiv b1 b3.
Proof.
  unfold bequiv. intros b1 b2 b3 H12 H23 st.
  rewrite (H12 st). rewrite (H23 st). reflexivity. Qed.

Lemma refl_cequiv : forall (c : com), cequiv c c.
Proof.
  unfold cequiv. intros c st st'. apply iff_refl. Qed.

Lemma sym_cequiv : forall (c1 c2 : com),
  cequiv c1 c2 -> cequiv c2 c1.
Proof.
  unfold cequiv. intros c1 c2 H st st'.
  assert (c1 / st \\ st' <-> c2 / st \\ st') as H'.
  { (* Proof of assertion *) apply H. }
  apply iff_sym. assumption.
Qed.

Lemma iff_trans : forall (P1 P2 P3 : Prop),
  (P1 <-> P2) -> (P2 <-> P3) -> (P1 <-> P3).
Proof.
  intros P1 P2 P3 H12 H23.
  inversion H12. inversion H23.
  split; intros A.
    apply H1. apply H. apply A.
    apply H0. apply H2. apply A. Qed.

Lemma trans_cequiv : forall (c1 c2 c3 : com),
  cequiv c1 c2 -> cequiv c2 c3 -> cequiv c1 c3.
Proof.
  unfold cequiv. intros c1 c2 c3 H12 H23 st st'.
  apply iff_trans with (c2 / st \\ st'). apply H12. apply H23. Qed.


Theorem CAss_congruence : forall i a1 a1',
  aequiv a1 a1' ->
  cequiv (CAss i a1) (CAss i a1').
Proof.
  intros i a1 a2 Heqv st st'.
  split; intros Hceval.
  - inversion Hceval. subst. apply E_Ass.
    rewrite Heqv. reflexivity.
  - inversion Hceval. subst. apply E_Ass.
    rewrite Heqv. reflexivity. Qed.

Theorem CWhile_congruence : forall b1 b1' c1 c1',
  bequiv b1 b1' -> cequiv c1 c1' ->
  cequiv (WHILE b1 DO c1 END) (WHILE b1' DO c1' END).
Proof.
  unfold bequiv,cequiv.
  intros b1 b1' c1 c1' Hb1e Hc1e st st'.
  split; intros Hce.
  - remember (WHILE b1 DO c1 END) as cwhile
      eqn:Heqcwhile.
    induction Hce; inversion Heqcwhile; subst.
    + apply E_WhileFalse. rewrite <- Hb1e. apply H.
    + apply E_WhileTrue with (st' := st').
      * rewrite <- Hb1e. apply H.
      * apply (Hc1e st st'). apply Hce1.
      * apply IHHce2. reflexivity.
  - remember (WHILE b1' DO c1' END) as c'while
      eqn:Heqc'while.
    induction Hce; inversion Heqc'while; subst.
    + apply E_WhileFalse. rewrite -> Hb1e. apply H.
    + apply E_WhileTrue with (st' := st').
      * rewrite -> Hb1e. apply H.
      * apply (Hc1e st st'). apply Hce1.
      * apply IHHce2. reflexivity. Qed.

Theorem CSeq_congruence : forall c1 c1' c2 c2',
  cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv (c1;;c2) (c1';;c2').
Proof.
  unfold cequiv.
  intros c1 c1' c2 c2' H1 H2 st st'.
  split; intros Hce.
  - remember (c1;;c2) as cseq eqn:Heqcseq.
    induction Hce; inversion Heqcseq; subst.
    eapply E_Seq.
    + rewrite <- H1. apply Hce1.
    + rewrite <- H2. apply Hce2.
  - remember (c1';;c2') as cseq eqn:Heqcseq.
    induction Hce; inversion Heqcseq; subst.
    eapply E_Seq.
    + rewrite -> H1. apply Hce1.
    + rewrite -> H2. apply Hce2.
Qed.


Theorem CIf_congruence : forall b b' c1 c1' c2 c2',
  bequiv b b' -> cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv (IFB b THEN c1 ELSE c2 FI)
         (IFB b' THEN c1' ELSE c2' FI).
Proof.
  unfold cequiv.
  intros b b' c1 c1' c2 c2' H H1 H2 st st'.
  split; intros Hce.
  - remember (IFB b THEN c1 ELSE c2 FI) as cif eqn:Heqcif.
    induction Hce; inversion Heqcif; subst.
    + eapply E_IfTrue.
      * rewrite <- H. assumption.
      * rewrite <- H1. assumption.
    + apply E_IfFalse.
      * rewrite <- H. assumption.
      * rewrite <- H2. assumption.
  - remember (IFB b' THEN c1' ELSE c2' FI) as cif eqn:Heqcif.
    induction Hce; inversion Heqcif; subst.
    + apply E_IfTrue.
      * rewrite -> H. assumption.
      * rewrite -> H1. assumption.
    + apply E_IfFalse.
      * rewrite -> H. assumption.
      * rewrite -> H2. assumption.
Qed.

Definition atrans_sound (atrans : aexp -> aexp) : Prop :=
  forall (a : aexp),
    aequiv a (atrans a).

Definition btrans_sound (btrans : bexp -> bexp) : Prop :=
  forall (b : bexp),
    bequiv b (btrans b).

Definition ctrans_sound (ctrans : com -> com) : Prop :=
  forall (c : com),
    cequiv c (ctrans c).

Fixpoint fold_constants_aexp (a : aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | AId i => AId i
  | APlus a1 a2 =>
    match (fold_constants_aexp a1, fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 + n2)
    | (a1', a2') => APlus a1' a2'
    end
  | AMinus a1 a2 =>
    match (fold_constants_aexp a1, fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 - n2)
    | (a1', a2') => AMinus a1' a2'
    end
  | AMult a1 a2 =>
    match (fold_constants_aexp a1, fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 * n2)
    | (a1', a2') => AMult a1' a2'
    end
  end.

Local Open Scope aexp_scope.
Local Open Scope bexp_scope.

Example fold_aexp_ex1 : fold_constants_aexp ((1 + 2) * X) = (3 * X).
Proof. reflexivity. Qed.

Example fold_aexp_ex2 : fold_constants_aexp (X - ((0 * 6) + Y)) = (X - (0 + Y)).
Proof. reflexivity. Qed.

Fixpoint fold_constants_bexp (b : bexp) : bexp :=
  match b with
  | BTrue => BTrue
  | BFalse => BFalse
  | BEq a1 a2 =>
      match (fold_constants_aexp a1, fold_constants_aexp a2) with
      | (ANum n1, ANum n2) =>
          if beq_nat n1 n2 then BTrue else BFalse
      | (a1', a2') =>
          BEq a1' a2'
      end
  | BLe a1 a2 =>
      match (fold_constants_aexp a1, fold_constants_aexp a2) with
      | (ANum n1, ANum n2) =>
          if leb n1 n2 then BTrue else BFalse
      | (a1', a2') =>
          BLe a1' a2'
      end
  | BNot b1 =>
      match (fold_constants_bexp b1) with
      | BTrue => BFalse
      | BFalse => BTrue
      | b1' => BNot b1'
      end
  | BAnd b1 b2 =>
      match (fold_constants_bexp b1, fold_constants_bexp b2) with
      | (BTrue, BTrue) => BTrue
      | (BTrue, BFalse) => BFalse
      | (BFalse, BTrue) => BFalse
      | (BFalse, BFalse) => BFalse
      | (b1', b2') => BAnd b1' b2'
      end
  end.

Example fold_bexp_ex1 :
  fold_constants_bexp (true && ! (false && true)) = true.
Proof. reflexivity. Qed.

Example fold_bexp_ex2 :
  fold_constants_bexp ((X = Y) && (0 = (2 - (1 + 1)))) =
  ((X = Y) && true).
Proof. reflexivity. Qed.

Fixpoint fold_constants_com (c : com) : com :=
  match c with
  | SKIP =>
      SKIP
  | i ::= a =>
      CAss i (fold_constants_aexp a)
  | c1 ;; c2 =>
      (fold_constants_com c1) ;; (fold_constants_com c2)
  | IFB b THEN c1 ELSE c2 FI =>
      match fold_constants_bexp b with
      | BTrue => fold_constants_com c1
      | BFalse => fold_constants_com c2
      | b' => IFB b' THEN fold_constants_com c1
                     ELSE fold_constants_com c2 FI
      end
  | WHILE b DO c END =>
      match fold_constants_bexp b with
      | BTrue => WHILE BTrue DO SKIP END
      | BFalse => SKIP
      | b' => WHILE b' DO (fold_constants_com c) END
      end
  end.


Example fold_com_ex1 :
  fold_constants_com
    (* Original program: *)
    (X ::= 4 + 5;;
     Y ::= X - 3;;
     IFB (X - Y) = (2 + 4) THEN
       SKIP
     ELSE
       Y ::= 0
     FI;;
     IFB 0 ≤ (4 - (2 + 1))
     THEN
       Y ::= 0
     ELSE
       SKIP
     FI;;
     WHILE Y = 0 DO
       X ::= X + 1
     END)
  = (* After constant folding: *)
    (X ::= 9;;
     Y ::= X - 3;;
     IFB (X - Y) = 6 THEN
       SKIP
     ELSE
       Y ::= 0
     FI;;
     Y ::= 0;;
     WHILE Y = 0 DO
       X ::= X + 1
     END).
Proof. reflexivity. Qed.

Theorem fold_constants_aexp_sound :
  atrans_sound fold_constants_aexp.
Proof.
  unfold atrans_sound. intros a. unfold aequiv.
  intros st.
  induction a; simpl;
  try reflexivity;
  try (destruct (fold_constants_aexp a1);
       destruct (fold_constants_aexp a2);
       rewrite IHa1; rewrite IHa2; reflexivity).
Qed.

Theorem fold_constants_bexp_sound:
  btrans_sound fold_constants_bexp.
Proof.
  unfold btrans_sound. intros b. unfold bequiv. intros st.
  induction b;
    (* BTrue and BFalse are immediate *)
    try reflexivity.
  - (* BEq *)
    rename a into a1. rename a0 into a2. simpl.
    remember (fold_constants_aexp a1) as a1' eqn:Heqa1'.
    remember (fold_constants_aexp a2) as a2' eqn:Heqa2'.
    replace (aeval st a1) with (aeval st a1') by
       (subst a1'; rewrite <- fold_constants_aexp_sound; reflexivity).
    replace (aeval st a2) with (aeval st a2') by
       (subst a2'; rewrite <- fold_constants_aexp_sound; reflexivity).
    destruct a1'; destruct a2'; try reflexivity.
    (* The only interesting case is when both a1 and a2
       become constants after folding *)
      simpl. destruct (beq_nat n n0); reflexivity.
  - simpl. rename a into a1. rename a0 into a2.
    remember (fold_constants_aexp a1) as a1' eqn:Heqal'.
    remember (fold_constants_aexp a2) as a2' eqn:Heqal2'.
    replace (aeval st a1) with (aeval st a1') by
      (subst a1'; rewrite <- fold_constants_aexp_sound; reflexivity).
    replace (aeval st a2) with (aeval st a2') by
      (subst a2'; rewrite <- fold_constants_aexp_sound; reflexivity).
    destruct a1'; destruct a2'; try reflexivity.
      simpl. destruct (leb n n0); reflexivity.
  - (* BNot *)
    simpl. remember (fold_constants_bexp b) as b' eqn:Heqb'.
    rewrite IHb.
    destruct b'; reflexivity.
  - (* BAnd *)
    simpl.
    remember (fold_constants_bexp b1) as b1' eqn:Heqb1'.
    remember (fold_constants_bexp b2) as b2' eqn:Heqb2'.
    rewrite IHb1. rewrite IHb2.
    destruct b1'; destruct b2'; reflexivity.
Qed.

Theorem fold_constants_com_sound :
  ctrans_sound fold_constants_com.
Proof.
  unfold ctrans_sound. intros c.
  induction c; simpl.
  - apply refl_cequiv.
  - apply CAss_congruence.
              apply fold_constants_aexp_sound.
  - apply CSeq_congruence; assumption.
  - 
    assert (bequiv b (fold_constants_bexp b)). {
      apply fold_constants_bexp_sound. }
    destruct (fold_constants_bexp b) eqn:Heqb;
      try (apply CIf_congruence; assumption).
    +
      apply trans_cequiv with c1; try assumption.
      apply IFB_true. assumption.
    + 
      apply trans_cequiv with c2; try assumption.
      apply IFB_false; assumption.
  -  assert (bequiv b (fold_constants_bexp b)). {
      apply fold_constants_bexp_sound. }
       destruct (fold_constants_bexp b) eqn:Heqb;
         try (apply CWhile_congruence; assumption).
      + apply WHILE_true. assumption.
      + apply WHILE_false. assumption.
Qed.

Fixpoint optimize_0plus_aexp (e:aexp) : aexp :=
  match e with
  | ANum n =>
      ANum n
  | APlus (ANum 0) e2 =>
      optimize_0plus_aexp e2
  | APlus e1 e2 =>
      APlus (optimize_0plus_aexp e1) (optimize_0plus_aexp e2)
  | AMinus e1 e2 =>
      AMinus (optimize_0plus_aexp e1) (optimize_0plus_aexp e2)
  | AMult e1 e2 =>
      AMult (optimize_0plus_aexp e1) (optimize_0plus_aexp e2)
  | AId i => AId i
  end.

Theorem optimize_0plus_aexp_sound :
  atrans_sound optimize_0plus_aexp.
Proof.
  unfold atrans_sound. intros a. unfold aequiv.
  intros st.
  induction a; simpl; try reflexivity;
  try (destruct (optimize_0plus_aexp a1); 
       destruct (optimize_0plus_aexp a2);
       rewrite IHa1; rewrite IHa2; reflexivity).
  - destruct a1; 
    try destruct n; 
    try (simpl; rewrite IHa2; reflexivity);  
    try 
      (simpl; simpl in IHa1; simpl in IHa2;
      rewrite IHa2; rewrite IHa1; reflexivity).
Qed.

Fixpoint optimize_0plus_bexp (b : bexp) : bexp :=
   match b with
  | BTrue => BTrue
  | BFalse => BFalse
  | BEq a1 a2 => 
      BEq (optimize_0plus_aexp a1) (optimize_0plus_aexp a2)
  | BLe a1 a2 => BLe a1 a2
  | BNot b1 => BNot b1
  | BAnd b1 b2 => BAnd b1 b2
  end.

Theorem optimize_0plus_bexp_sound : 
  btrans_sound optimize_0plus_bexp.
Proof.
  unfold btrans_sound. intros b. unfold bequiv.
  intros st.
  induction b; simpl; try reflexivity.
  repeat rewrite <- optimize_0plus_aexp_sound.
  reflexivity.
Qed.

Fixpoint optimize_0plus_com (c : com) : com :=
  match c with
  | SKIP =>
      SKIP
  | i ::= a =>
      CAss i (optimize_0plus_aexp a)
  | c1 ;; c2 =>
      (optimize_0plus_com c1) ;; (optimize_0plus_com c2)
  | IFB b THEN c1 ELSE c2 FI =>
      match optimize_0plus_bexp b with
      | BTrue => optimize_0plus_com c1
      | BFalse => optimize_0plus_com c2
      | b' => IFB b' THEN optimize_0plus_com c1
                     ELSE optimize_0plus_com c2 FI
      end
  | WHILE b DO c END =>
      match optimize_0plus_bexp b with
      | BTrue => WHILE BTrue DO SKIP END
      | BFalse => SKIP
      | b' => WHILE b' DO (optimize_0plus_com c) END
      end
  end.

Theorem optimize_0plus_com_sound :
  ctrans_sound optimize_0plus_com.
Proof.
  unfold ctrans_sound. intros c.
  induction c; simpl.
  - apply refl_cequiv.
  - apply CAss_congruence.
              apply optimize_0plus_aexp_sound.
  - apply CSeq_congruence; assumption.
  - 
    assert (bequiv b (optimize_0plus_bexp b)). {
      apply optimize_0plus_bexp_sound. }
    destruct (optimize_0plus_bexp b) eqn:Heqb;
      try (apply CIf_congruence; assumption).
    +
      apply trans_cequiv with c1; try assumption.
      apply IFB_true. assumption.
    + 
      apply trans_cequiv with c2; try assumption.
      apply IFB_false; assumption.
  -  assert (bequiv b (optimize_0plus_bexp b)). {
      apply optimize_0plus_bexp_sound. }
       destruct (optimize_0plus_bexp b) eqn:Heqb;
         try (apply CWhile_congruence; assumption).
      + apply WHILE_true. assumption.
      + apply WHILE_false. assumption.
Qed.

Fixpoint fold_then_0plus (c : com) : com :=
  fold_constants_com c.

Theorem fold_then_0plus_sound : ctrans_sound fold_then_0plus.
Proof.
 unfold ctrans_sound. intros c. induction c; simpl. unfold fold_then_0plus. Admitted.


Fixpoint subst_aexp (i : string) (u : aexp) (a : aexp) : aexp :=
  match a with
  | ANum n =>
      ANum n
  | AId i' =>
      if beq_string i i' then u else AId i'
  | APlus a1 a2 =>
      APlus (subst_aexp i u a1) (subst_aexp i u a2)
  | AMinus a1 a2 =>
      AMinus (subst_aexp i u a1) (subst_aexp i u a2)
  | AMult a1 a2 =>
      AMult (subst_aexp i u a1) (subst_aexp i u a2)
  end.

Example subst_aexp_ex : 
  subst_aexp X (42 + 53) (Y + X) = (Y + (42 + 53)).
Proof. reflexivity. Qed.

Definition subst_equiv_property := forall i1 i2 a1 a2,
  cequiv (i1 ::= a1;; i2 ::= a2)
          (i1 ::= a1;; i2 ::= subst_aexp i1 a1 a2).

Theorem subst_inequiv : ~ subst_equiv_property.
Proof.
  unfold subst_equiv_property.
  intros Contra.
  remember (X ::= X + 1;; Y ::= X) as c1.
  remember (X ::= X + 1;; Y ::= X + 1) as c2.
  assert (cequiv c1 c2) by (subst; apply Contra).
  remember { X --> 1 ; Y --> 1 } as st1.
  remember { X --> 1 ; Y --> 2 } as st2.
  assert (H1: c1 / { --> 0 } \\ st1);
  assert (H2: c2 / { --> 0 } \\ st2);
  try (subst;
       apply E_Seq with (st' := { X --> 1 });
       apply E_Ass; reflexivity).
  apply H in H1.
  assert (Hcontra: st1 = st2)
    by (apply (ceval_deterministic c2 { --> 0 }); assumption).
  assert (Hcontra': st1 Y = st2 Y)
    by (rewrite Hcontra; reflexivity).
  subst. inversion Hcontra'. Qed.

Inductive var_not_used_in_aexp (X:string) : aexp -> Prop :=
  | VNUNum : forall n, var_not_used_in_aexp X (ANum n)
  | VNUId : forall Y, X <> Y -> var_not_used_in_aexp X (AId Y)
  | VNUPlus : forall a1 a2,
      var_not_used_in_aexp X a1 ->
      var_not_used_in_aexp X a2 ->
      var_not_used_in_aexp X (APlus a1 a2)
  | VNUMinus : forall a1 a2,
      var_not_used_in_aexp X a1 ->
      var_not_used_in_aexp X a2 ->
      var_not_used_in_aexp X (AMinus a1 a2)
  | VNUMult : forall a1 a2,
      var_not_used_in_aexp X a1 ->
      var_not_used_in_aexp X a2 ->
      var_not_used_in_aexp X (AMult a1 a2).

Search total_map.

Search beq_string.

Lemma aeval_weakening : forall i st a ni,
  var_not_used_in_aexp i a ->
  aeval (st & { i --> ni }) a = aeval st a.
Proof.
  intros i st a ni H. simpl.
  induction H.
  - simpl. reflexivity.
  - simpl. unfold not in H. 
    unfold t_update. apply beq_string_false_iff in H.
    rewrite -> H. reflexivity.
  - simpl. 
    rewrite -> IHvar_not_used_in_aexp1.
    rewrite -> IHvar_not_used_in_aexp2. reflexivity.
  - simpl.
    rewrite -> IHvar_not_used_in_aexp1.
    rewrite -> IHvar_not_used_in_aexp2. reflexivity.
  - simpl.
    rewrite -> IHvar_not_used_in_aexp1.
    rewrite -> IHvar_not_used_in_aexp2. reflexivity.
Qed.

Theorem no_var_subst_equiv : forall i a,
  var_not_used_in_aexp i a -> subst_equiv_property.
Proof.
  intros i a H. 
  unfold subst_equiv_property.
  induction H.
  - intros. unfold cequiv. intros. simpl. split.
    + intros. inversion H. subst.
  induction H; intros; unfold cequiv; intros; split; intros.
  - assumption. unfold subst_aexp. simpl. unfold cequiv.



