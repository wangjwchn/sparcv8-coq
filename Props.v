Require Import Asm.
Require Import Coqlib.
Require Import Maps.
Require Import Integers.
Require Import LibTactics.
Require Import Coq.omega.Omega.
Require Import math_sol.
Require Import int_auto.
Require Import Coq.Logic.FunctionalExtensionality.
Local Open Scope sparc_scope.
Local Open Scope Z_scope.
Import ListNotations.

Definition some_reg_eq: RegFile -> RegFile -> Prop :=
  fun R R' =>
    R#wim = R'#wim /\ R#trap = R'#trap /\ R#s = R'#s /\ R#annul = R'#annul /\ R#et = R'#et /\ R#pc = R'#pc /\ R#npc = R'#npc /\ R#r1 = R'#r1.


Lemma Hold_Sth_Replace:
   forall l R R',
      R' = replace l R ->
      some_reg_eq R R'.
Proof.
  intros.
  unfolds.
  splits;
  unfolds in H;
  rewrite H; clear H;
  destruct l; auto;
  destruct f; auto;
  destruct f; auto;
  destruct f; auto;
  destruct f; auto;
  destruct f; auto;
  destruct f; auto;
  destruct f; auto;
  destruct f; auto;
  destruct f; auto;
  destruct l; auto;
  destruct f; auto;
  destruct f; auto;
  destruct f; auto;
  destruct f; auto;
  destruct f; auto;
  destruct f; auto;
  destruct f; auto;
  destruct f; auto;
  destruct f; auto;
  destruct l; auto;
  destruct f; auto;
  destruct f; auto;
  destruct f; auto;
  destruct f; auto;
  destruct f; auto;
  destruct f; auto;
  destruct f; auto;
  destruct f; auto;
  destruct l; auto;
  destruct f; auto;
  auto;
  destruct f; auto;
  auto; auto; auto.
Qed.

Lemma UserMode_Replace:
    forall l R R',
      usr_mode_R R ->
      R' = replace l R ->
      usr_mode_R R'.
Proof.
  intros.
  assert (R#s = R'#s).
  apply (Hold_Sth_Replace l R R'); auto.
  unfolds. unfolds in H.
  unfolds. unfolds in H.
  rewrite H1 in H. auto.
Qed.

Lemma Hold_Sth_LeftWin:
   forall R R' F F' k,
      left_win k (R,F) = (R',F') ->
      some_reg_eq R R'.
Proof.
  intros.

  unfolds in H.
  remember (left_iter (Z.to_nat k) F (fench R)).
  destruct p.
  inverts H.

  unfolds. splits; unfolds; unfolds; simpl;
  apply (Hold_Sth_Replace f0 R (replace f0 R)); auto.

Qed.


Lemma Hold_Sth_RightWin:
   forall R R' F F' k,
      right_win k (R,F) = (R',F') ->
      some_reg_eq R R'.
Proof.
  intros.

  unfolds in H.
  remember (right_iter (Z.to_nat k) F (fench R)).
  destruct p.
  inverts H.

  unfolds. splits; unfolds; unfolds; simpl;
  apply (Hold_Sth_Replace f0 R (replace f0 R)); auto.

Qed.


Lemma Hold_Sth_SetWin:
   forall R R' F F' k,
      set_win k (R,F) = (R',F') ->
      some_reg_eq R R'.
Proof.
  intros.
  unfolds in H.

  destruct (Int.unsigned k >? Int.unsigned (get_R cwp R)).

  apply (Hold_Sth_LeftWin R R' F F' (Int.unsigned k -ᵢ (get_R cwp R))); iauto.

  destruct (Int.unsigned k <? Int.unsigned (get_R cwp R)).

  apply (Hold_Sth_RightWin R R' F F' (Int.unsigned (get_R cwp R) -ᵢ k)); iauto.

  inverts H. unfolds. splits; auto.
Qed.

Lemma UserMode_LeftWin:
  forall R R' F F' k,
    usr_mode_R R ->
    left_win k (R,F) = (R',F') ->
    usr_mode_R R'.
Proof.
  intros.
  unfolds in H0.
  remember (left_iter (Z.to_nat k) F (fench R)).
  destruct p.
  inverts H0.

  unfolds. unfolds.

  asserts_rewrite (get_R s (RegMap.set cwp (post_cwp k R) (replace f0 R)) = get_R s  (replace f0 R)).
  auto.
  asserts_rewrite (usr_mode_R (replace f0 R)). {
    apply (UserMode_Replace f0 R).
    apply H. auto.
  }
  auto.
Qed.


Lemma UserMode_RightWin:
  forall R R' F F' k,
    usr_mode_R R ->
    right_win k (R,F) = (R',F') ->
    usr_mode_R R'.
Proof.
  intros.
  unfolds in H0.
  remember (right_iter (Z.to_nat k) F (fench R)).
  destruct p.
  inverts H0.

  unfolds. unfolds.

  asserts_rewrite (get_R s (RegMap.set cwp (pre_cwp k R) (replace f0 R)) = get_R s  (replace f0 R)).
  auto.
  asserts_rewrite (usr_mode_R (replace f0 R)). {
    apply (UserMode_Replace f0 R).
    apply H. auto.
  }
  auto.
Qed.

Lemma UserMode_SetWin:
  forall R R' F F' w,
    usr_mode_R R ->
    set_win w (R,F) = (R',F') ->
    usr_mode_R R'.
Proof.
  intros.
  unfolds in H0.
  destruct (Int.unsigned w >? Int.unsigned (get_R cwp R)).

  remember (left_win (Int.unsigned w -ᵢ (get_R cwp R)) (R, F)).
  destruct r.
  inverts H0.
  symmetry in Heqr.
  apply (UserMode_LeftWin R R' F F'(Int.unsigned w -ᵢ (get_R cwp R)) H Heqr).

  destruct (Int.unsigned w <? Int.unsigned (get_R cwp R)).
  remember (right_win (Int.unsigned (get_R cwp R) -ᵢ w) (R, F)).
  destruct r.
  inverts H0.
  symmetry in Heqr.
  apply (UserMode_RightWin R R' F F'(Int.unsigned (get_R cwp R) -ᵢ w) H Heqr).

  inverts H0. auto.

Qed.

Lemma Hold_Sth_IncWin:
   forall R R' F F',
      inc_win (R,F) = Some (R',F') ->
      some_reg_eq R R'.
Proof.
  intros.
  unfolds in H.
  destruct (negb (win_masked (post_cwp 1 R) R)).

  remember (left_win 1 (R, F)).
  destruct r.
  inverts H.
  symmetry in Heqr.
  apply (Hold_Sth_LeftWin R R' F F' 1); auto.

  inverts H.
Qed.


Lemma Hold_Sth_DecWin:
   forall R R' F F',
      dec_win (R,F) = Some (R',F') ->
      some_reg_eq R R'.
Proof.
  intros.
  unfolds in H.
  destruct (negb (win_masked (pre_cwp 1 R) R)).

  remember (right_win 1 (R, F)).
  destruct r.
  inverts H.
  symmetry in Heqr.
  apply (Hold_Sth_RightWin R R' F F' 1); auto.

  inverts H.
Qed.


Lemma UserMode_IncWin:
  forall R R' F F',
    usr_mode_R R ->
    inc_win (R,F) = Some (R',F') ->
    usr_mode_R R'.
Proof.
  intros.
  unfolds in H0.
  destruct (negb (win_masked (post_cwp 1 R) R)).

  remember (left_win 1 (R, F)).
  destruct r.
  inverts H0.
  symmetry in Heqr.
  apply (UserMode_LeftWin R R' F F' 1); auto.

  inverts H0.
Qed.

Lemma UserMode_DecWin:
  forall R R' F F',
    usr_mode_R R ->
    dec_win (R,F) = Some (R',F') ->
    usr_mode_R R'.
Proof.
  intros.
  unfolds in H0.
  destruct (negb (win_masked (pre_cwp 1 R) R)).

  remember (right_win 1 (R, F)).
  destruct r.
  inverts H0.
  symmetry in Heqr.
  apply (UserMode_RightWin R R' F F' 1); auto.

  inverts H0.
Qed.

Lemma usr_mode_prop:
    forall R,
    usr_mode_R R ->
    R#s = $0.
Proof.
  intros.
  unfolds in H.
  unfolds in H.
  remember ((get_R s R) =ᵢ ($ 0)).
  destruct b.
  symmetry in Heqb.
  assert (if (get_R s R) =ᵢ ($ 0) then (get_R s R) = ($0) else (get_R s R) <> ($0) ). {
    apply Int.eq_spec.
  }
  rewrite Heqb in H0.
  auto.
  inverts H.
Qed.

Lemma UsrMode_R:
    forall i M M' R R',
    usr_mode_R R ->
    R__ (M,R) i (M',R') ->
    usr_mode_R R'.
Proof.
  intros.
  apply usr_mode_prop in H.
  inverts H0;
  unfolds; unfolds.

  asserts_rewrite (get_R s (next R) = get_R s R ). auto.
  rewrite H. auto.

  asserts_rewrite (get_R s (djmp w R) = get_R s R ). auto.
  rewrite H. auto.

  asserts_rewrite (get_R s (set_annul (next R)) = get_R s R ). auto.
  rewrite H. auto.

  asserts_rewrite (get_R s (set_annul (djmp w R)) = get_R s R ). auto.
  rewrite H. auto.

  asserts_rewrite (get_R s (djmp w R) = get_R s R ). auto.
  rewrite H. auto.

  asserts_rewrite (get_R s (djmp w (save_pc ri R)) = get_R s R ).
  destruct ri; auto.
  rewrite H. auto.

  asserts_rewrite (get_R s (next R # ri <- v) = get_R s R ).
  destruct ri; auto.
  rewrite H. auto.

  asserts_rewrite (get_R s (next R) = get_R s R ). auto.
  rewrite H. auto.

  asserts_rewrite (get_R s (next R) = get_R s R ). auto.
  rewrite H. auto.

  asserts_rewrite (get_R s (next R) = get_R s R ). auto.
  rewrite H. auto.

  asserts_rewrite (get_R s (set_user_trap (get_range 0 6 a) R) = get_R s R ). auto.
  rewrite H. auto.

  inverts H7. unfolds in H1.
  rewrite H in H1. inverts H1.

  asserts_rewrite (get_R s (next R # ri <- (get_R syb R)) = get_R s R).
  destruct ri; auto.
  rewrite H. auto.

  asserts_rewrite (get_R s (next R # rj <- ((get_R ri R) &ᵢ a)) = get_R s R ). 
  destruct rj; auto.
  rewrite H. auto.

  asserts_rewrite (get_R s (next R # rj <- ((get_R ri R) |ᵢ a)) = get_R s R ). 
  destruct rj; auto.
  rewrite H. auto.

  asserts_rewrite (get_R s (next R # rj <- ((get_R ri R) <<ᵢ (get_range 0 4 a))) = get_R s R ). 
  destruct rj; auto.
  rewrite H. auto.

  asserts_rewrite (get_R s (next R # rj <- ((get_R ri R) >>ᵢ (get_range 0 4 a))) = get_R s R ). 
  destruct rj; auto.
  rewrite H. auto.

Qed.

Lemma Determinacy_R:
    forall i M M1 M2 R R1 R2,
    R__ (M,R) i (M1,R1) ->
    R__ (M,R) i (M2,R2) ->
    M1 = M2 /\ R1 = R2.
Proof.
  intros.
  inverts H; inverts H0; fequals; try auto;
  try (inverts H4; fequals; auto);
  try (inverts H5; fequals; auto);
  try solve [rewrite H7 in H6; try inverts H6; fequals; auto];
  try solve [inverts H9; inverts H10; auto];
  try (rewrite H0 in H6; try inverts H6; fequals; auto);
  try solve [rewrite H9 in H11; try inverts H11; fequals; auto];
  try solve [try rewrite H9 in H8; try inverts H8; fequals; auto];
  try solve [inverts H7;fequals; auto].
Qed.

Lemma trap_has_trap:
  forall i Q Q',
    unexpected_trap i Q = Some Q' ->
    no_trap_Q Q' ->
    False.
Proof.
  intros.
  unfolds in H.
  destruct (trap_type i Q).
  destruct Q.
  inverts H.
  unfolds in H0.
  unfolds in H0.
  unfolds in H0.
  unfold set_trap in H0.
  unfold get_R in H0.

  assert ((RegMap.set tt w r) # trap <- ($ 1) trap = ($ 1)). {
    apply RegMap.gss.
  }
  rewrite H in H0.
  rewrite Int.eq_true in H0.
  inverts H0.

  destruct Q.
  inverts H.
Qed.


Lemma ModeDeq:
  forall Q,
    sup_mode_Q Q ->
    usr_mode_Q Q ->
    False.
Proof.
  intros.
  unfolds in H.
  unfolds in H0.
  destruct Q.
  unfolds in H.
  unfolds in H0.
  rewrite H in H0.
  inverts H0.
Qed.

Fixpoint no_psr(D: DelayList) : Prop :=
  match D with
  | (_,syb,_)::D' => syb<>psr /\ no_psr D'
  | _ => True
  end.

Lemma UserMode_Q:
  forall i M M' Q Q' D D',
  usr_mode_Q Q /\ no_psr D->
  Q__ (M,Q,D) i (M',Q',D') ->
  usr_mode_Q Q' /\ no_psr D'.
Proof.
  intros.

  inverts H0;
  try unfold usr_mode_Q;
  try unfold usr_mode_R;
  try unfold usr_mode;
  try iauto;
  split; try apply H.

  {
  apply (UsrMode_R i M M' R R'); iauto.
  }

  {
  asserts_rewrite (get_R s (next R' # rj <- ((get_R ri R) +ᵢ a)) = get_R s R').
  destruct rj; auto.
  assert (usr_mode_R R').
    apply (UserMode_DecWin R R' F F'); iauto.
  apply H0.
  }

  {
  asserts_rewrite (get_R s (next R' # rj <- ((get_R ri R) +ᵢ a)) = get_R s R').
  destruct rj; auto.
  assert (usr_mode_R R').
    apply (UserMode_IncWin R R' F F'); iauto.
  apply H0.
  }

  {
  destruct H.
  false.
  }

  {
  destruct syb; simpl; iauto.
  }

  {
  destruct syb; simpl; iauto.
  }

  {
  destruct H.
  false.
  }

  {
  unfolds in H5.
  destruct Q.
  destruct (trap_type i (r, f)); iauto.
  inverts H5.
  asserts_rewrite (get_R s (set_trap (RegMap.set tt w r)) = get_R s r); iauto.
  inverts H5.
  }
Qed.


Lemma Determinacy_Trap:
  forall i Q Q1 Q2,
  unexpected_trap i Q = Some Q1 ->
  unexpected_trap i Q = Some Q2 ->
  Q1 = Q2.
Proof.
  intros.
  destruct i;
  unfolds in H;
  unfold trap_type in H;
  unfolds in H0;
  unfold trap_type in H0;
  destruct Q;
  try solve [inverts H];
  try destruct (eval_AddrExp a r);
  try destruct (negb (word_aligned w));
  fequals.
Qed.




Lemma Determinacy_Deq:
    forall i M R M' R' F Q,
    R__ (M, R) i (M', R') ->
    unexpected_trap i (R,F) = Some Q -> False.
Proof.
  intros.
  inverts H;
  unfold unexpected_trap in H0;
  unfold trap_type in H0;

  try solve [

  try rewrite H7 in H0;
  try rewrite H6 in H0;
  try rewrite H9 in H0;


  try (unfold word_aligned_R in H8;
       rewrite H8 in H0;
       simpl in H0);
       try inverts H0
  ];


  try solve [
  try (unfold sup_mode_R in H7;
       rewrite H7 in H0);
       destruct syb; inverts H0
  ];

  try (unfold sup_mode_R in H6;
       rewrite H6 in H0);


  try solve [
    destruct syb;
    destruct H8;
    destruct H1;
    eauto;
    inverts H0
  ].

Qed.

Lemma Determinacy_Q:
    forall i M M1 M2 Q Q1 Q2 F F1 F2,
    Q__ (M,Q,F) i (M1,Q1,F1) ->
    Q__ (M,Q,F) i (M2,Q2,F2) ->
    M1 = M2 /\ Q1 = Q2 /\ F1 = F2.
Proof.
  intros.

  inverts H; inverts H0; fequals; try auto;
  try rename R' into R1;
  try rename R'0 into R2;
  try rename F0 into F;
  try rename F' into F1;
  try rename F'0 into F2;

 try solve [inverts H5; false].

  {
  assert(M1 = M2 /\ R1 = R2).
  apply (Determinacy_R i M M1 M2 R R1 R2); iauto.
  inverts H. auto.
  }

  {
  false. apply (Determinacy_Deq i M2 R M1 R1 F Q2); iauto.
  }

  {
  rewrite H9 in H11. clear H9.
  inverts H11.
  inverts H6.
  rewrite H10 in H12. clear H10.
  inverts H12. auto.
  }

  {
  unfold unexpected_trap in H4.
  unfold trap_type in H4.
  rewrite H9 in H4.
  inverts H4.
  }

  {
  rewrite H9 in H11. clear H9.
  inverts H11.
  inverts H6.
  rewrite H10 in H12. clear H10.
  inverts H12. auto.
  }

  {
  unfold unexpected_trap in H4.
  unfold trap_type in H4.
  rewrite H9 in H4.
  inverts H4.
  }

  {
  rewrite H13 in H18. clear H13.
  inverts H18.
  inverts H8.
  rewrite H11 in H16. clear H11.
  inverts H16.
  auto.
  }

  {
  unfold unexpected_trap in H4.
  unfold trap_type in H4.
  rewrite H9 in H4.
  false.
  }

  {
  inverts H8.
  rewrite H11 in H14. clear H11.
  inverts H14.
  auto.
  }

  {
  unfold unexpected_trap in H4.
  unfold trap_type in H4.
  destruct H10 as (TBR & WIM & PSR).
  destruct syb; false.
  }

  {
  inverts H8.
  rewrite H11 in H14. clear H11.
  inverts H14.
  auto.
  }

  {
  unfold unexpected_trap in H4.
  unfold trap_type in H4.
  destruct syb; try false; rewrite H9 in H4; false.
  }

  {
  inverts H7.
  rewrite H10 in H13.
  inverts H13. auto.
  }

  {
  unfold unexpected_trap in H4.
  unfold trap_type in H4.
  rewrite H8 in H4. clear H8.
  rewrite H10 in H4. clear H10.
  rewrite H12 in H4. clear H12.
  false.
  }

  {
  false. apply (Determinacy_Deq i M1 R M2 R1 F Q1); iauto.
  }

  {
  unfold unexpected_trap in H5.
  unfold trap_type in H5.
  rewrite H9 in H5.
  false.
  }

  {
  unfold unexpected_trap in H5.
  unfold trap_type in H5.
  rewrite H9 in H5.
  false.
  }

  {
  unfold unexpected_trap in H5.
  unfold trap_type in H5.
  rewrite H9 in H5.
  false.
  }

  {
  unfold unexpected_trap in H5.
  unfold trap_type in H5.
  destruct H10 as (TBR & WIM & PSR).
  destruct syb; false.
  }

  {
  unfold unexpected_trap in H5.
  unfold trap_type in H5.
  destruct syb; try false; rewrite H9 in H5; false.
  }

  {
  unfold unexpected_trap in H5.
  unfold trap_type in H5.
  rewrite H8 in H5.
  rewrite H10 in *.
  rewrite H12 in *.
  false.
  }

  {
  asserts_rewrite(Q1 = Q2).
  apply (Determinacy_Trap i Q Q1 Q2); iauto.
  auto.
  }

Qed.



Lemma No_PSR_in_D:
  forall Q D Q' D',
    usr_mode_Q Q ->
    no_psr D ->
    exe_delay Q D = (Q',D') ->
    usr_mode_Q Q' /\ no_psr D'.
Proof.
  induction D as [|d].
  - intros.
    unfolds in H1.
    inverts H1. auto.
  - intros.
    destruct d.
    destruct p.

    inverts H0.
    destruct s; try solve [false].
    {
      inverts H1.
      destruct d.
      remember (exe_delay Q D).
      destruct p as (Q'' & D'').
      assert (usr_mode_Q Q'' /\ no_psr D''). {
        apply (IHD Q'' D''); iauto.
      }
      clear IHD H2 Heqp.
      destruct Q'' as (R'' & F'').
      inverts H4.
      apply H0.
      remember (exe_delay Q D).
      destruct p as (Q'' & D'').
      assert (usr_mode_Q Q'' /\ no_psr D''). {
        apply (IHD Q'' D''); iauto.
      }
      clear IHD H2 Heqp.
      destruct Q'' as (R'' & F'').
      inverts H4.
      split.
      apply H0.
      unfolds.
      split.
      unfolds.
      intros.
      false.
      apply H0.
    }
    {
      inverts H1.
      destruct d.
      remember (exe_delay Q D).
      destruct p as (Q'' & D'').
      assert (usr_mode_Q Q'' /\ no_psr D''). {
        apply (IHD Q'' D''); iauto.
      }
      clear IHD H2 Heqp.
      destruct Q'' as (R'' & F'').
      inverts H4.
      apply H0.
      remember (exe_delay Q D).
      destruct p as (Q'' & D'').
      assert (usr_mode_Q Q'' /\ no_psr D''). {
        apply (IHD Q'' D''); iauto.
      }
      clear IHD H2 Heqp.
      destruct Q'' as (R'' & F'').
      inverts H4.
      split.
      apply H0.
      unfolds.
      split.
      unfolds.
      intros.
      false.
      apply H0.
    }
    {
      inverts H1.
      destruct d.
      remember (exe_delay Q D).
      destruct p as (Q'' & D'').
      assert (usr_mode_Q Q'' /\ no_psr D''). {
        apply (IHD Q'' D''); iauto.
      }
      clear IHD H2 Heqp.
      destruct Q'' as (R'' & F'').
      inverts H4.
      apply H0.
      remember (exe_delay Q D).
      destruct p as (Q'' & D'').
      assert (usr_mode_Q Q'' /\ no_psr D''). {
        apply (IHD Q'' D''); iauto.
      }
      clear IHD H2 Heqp.
      destruct Q'' as (R'' & F'').
      inverts H4.
      split.
      apply H0.
      unfolds.
      split.
      unfolds.
      intros.
      false.
      apply H0.
    }
    {
      inverts H1.
      destruct d.
      remember (exe_delay Q D).
      destruct p as (Q'' & D'').
      assert (usr_mode_Q Q'' /\ no_psr D''). {
        apply (IHD Q'' D''); iauto.
      }
      clear IHD H2 Heqp.
      destruct Q'' as (R'' & F'').
      inverts H4.
      apply H0.
      remember (exe_delay Q D).
      destruct p as (Q'' & D'').
      assert (usr_mode_Q Q'' /\ no_psr D''). {
        apply (IHD Q'' D''); iauto.
      }
      clear IHD H2 Heqp.
      destruct Q'' as (R'' & F'').
      inverts H4.
      split.
      apply H0.
      unfolds.
      split.
      unfolds.
      intros.
      false.
      apply H0.
    }
Qed.

Lemma UserMode_H:
  forall C M Q D M' Q' D',
  usr_mode_Q Q /\ no_psr D ->
  H__ C (M,Q,D) (M',Q',D') ->
  usr_mode_Q Q' /\ no_psr D'.
Proof.
  intros.
  inverts H0;
  try rename Q'0 into Q'';
  try rename D'0 into D''.

  assert(usr_mode_Q Q'' /\ no_psr D'').
  apply (No_PSR_in_D Q D Q'' D''); iauto.
  apply (UserMode_Q i M M' Q'' Q' D'' D'); iauto.

  assert(usr_mode_Q Q'' /\ no_psr D').
  apply (No_PSR_in_D Q D Q'' D'); iauto.

  destruct Q'' as (R'' & F'').
  unfold clear_annul_Q.
  apply H0.

Qed.


Lemma Determinacy_H:
    forall C M M1 M2 Q Q1 Q2 F F1 F2,
    H__ C (M,Q,F) (M1,Q1,F1) ->
    H__ C (M,Q,F) (M2,Q2,F2) ->
    M1 = M2 /\ Q1 = Q2 /\ F1 = F2.
Proof.
  intros.
  inverts H;
  inverts H0; auto.

  {
  rewrite H6 in H7. clear H6.
  inverts H7.

  rewrite H10 in H13. clear H10.
  inverts H13.

  apply (Determinacy_Q i0 M M1 M2 Q' Q1 Q2 D' F1 F2); iauto.
  }

  {
  rewrite H7 in H5. clear H7.
  inverts H5.
  destruct Q'0 as (R' & F').
  false.
  }

  {
  rewrite H7 in H6. clear H7.
  inverts H6.
  destruct Q' as (R' & F').
  false.
  }

  {
  rewrite H5 in H6. clear H5.
  inverts H6.
  auto.
  }
Qed.


Lemma UserMode_P:
  forall Cu Cs Mu Mu' Ms Ms' Q Q' D D',
  usr_mode_S ((Mu,Ms),Q,D) /\ no_psr D ->
  P__ (Cu,Cs) ((Mu,Ms),Q,D) ((Mu',Ms'),Q',D') ->
  usr_mode_S ((Mu',Ms'),Q',D') /\ Ms = Ms' /\ no_psr D'.
Proof.
  intros.
  inverts H0.
  assert (usr_mode_Q Q' /\ no_psr D'). {
    apply (UserMode_H Cu Mu Q D Mu' Q' D'); iauto.
  }
  splits;
  try apply H0;
  iauto.

  {
  assert (usr_mode_Q Q); iauto.
  destruct Q as (R & F).
  false.
  }

Qed.

Lemma Determinacy_P:
    forall CP S S1 S2,
    P__ CP S S1 ->
    P__ CP S S2 ->
    S1 = S2.
Proof.
  intros.
  inverts H; inverts H0; auto.
  assert (Mu' = Mu'0 /\ Q' = Q'0 /\ D' = D'0). {
    apply (Determinacy_H Cu Mu Mu' Mu'0 Q Q' Q'0 D D' D'0); iauto.
  }
  inverts H.
  inverts H4. auto.

  {
  destruct Q as (R' & F').
  false.
  }

  {
  destruct Q as (R' & F').
  false.
  }

  assert (Ms' = Ms'0 /\ Q' = Q'0 /\ D' = D'0). {
    apply (Determinacy_H Cs Ms Ms' Ms'0 Q Q' Q'0 D D' D'0); iauto.
  }
  inverts H.
  inverts H4. auto.
Qed.


Definition usr_mem_eq: MemPair -> MemPair -> Prop :=
  fun MP MP' =>
    let (Mu,Ms) := MP in
    let (Mu',Ms') := MP' in
    Mu = Mu'.


Definition sup_mem_eq: State -> State -> Prop :=
  fun S S' =>
    let '(MP,_,_) := S in
    let '(MP',_,_) := S' in
    let (Mu,Ms) := MP in
    let (Mu',Ms') := MP' in
    Ms = Ms'.

Definition interrupt_e: Event -> bool :=
  fun e => andb (17%Z <=? Int.signed e) (Int.signed e <=? 31%Z).

Fixpoint no_trap(E: EventList): Prop :=
    match E with
    | e::E' =>
      match e with
      | Some _ => False
      | None => no_trap E'
      end
    | Nil => True
    end.

Definition usr_code_eq: CodePair -> CodePair -> Prop :=
  fun CP CP' =>
    let (Cu,Cs) := CP in
    let (Cu',Cs') := CP' in
    Cu = Cu'.


Fixpoint no_interrupt(E: EventList):Prop :=
  match E with
  | e::E' =>
    no_interrupt E'/\
    match e with
    | Some w => interrupt_e(w) = false
    | None => True
    end
  | nil => True
  end.


Definition low_eq: State -> State -> Prop :=
  fun S S' =>
    let '(MP,Q,F) := S in
    let '(MP',Q',F') := S' in
    let (Mu,Ms) := MP in
    let (Mu',Ms') := MP' in
    Q = Q' /\ Mu = Mu' /\ F = F'.

Definition no_psr_S: State -> Prop :=
  fun S =>
    let '(MP,Q,F) := S in
      no_psr F.

Lemma LowEq_P:
  forall Cu1 Cu2 Cs1 Cs2 S1 S2 S1' S2',
    usr_mode_S S1 /\ no_psr_S S1 ->
    usr_mode_S S2 /\ no_psr_S S2 ->
    Cu1 = Cu2 /\ low_eq S1 S2 ->
    P__ (Cu1,Cs1) S1 S1' ->
    P__ (Cu2,Cs2) S2 S2' ->
    low_eq S1' S2'.
Proof.
  intros.

  destruct S1 as (MPQ1 & D1).
  destruct MPQ1 as (MP1 & Q1).
  destruct S2 as (MPQ2 & D2).
  destruct MPQ2 as (MP2 & Q2).
  destruct MP1 as (Mu1 & Ms1).
  destruct MP2 as (Mu2 & Ms2).
  simpl in H.
  simpl in H0.
  simpl in H1.

  inverts H1.
  inverts H5.
  inverts H4.

  rename Cu2 into Cu.
  rename D2 into D.
  rename Q2 into Q.
  rename Mu2 into Mu.

  inverts H2; inverts H3; iauto;
  try rename Mu' into Mu1;
  try rename Mu'0 into Mu2;
  try rename Q' into Q1;
  try rename Q'0 into Q2;
  try rename D' into D1;
  try rename D'0 into D2.

  {
  assert (Mu1 = Mu2 /\ Q1 = Q2 /\ D1 = D2).
  apply (Determinacy_H Cu Mu Mu1 Mu2 Q Q1 Q2 D D1 D2); iauto.
  unfolds.
  iauto.
  }

  {
  destruct Q as (R & F).
  false.
  }

  {
  destruct Q as (R & F).
  false.
  }

  {
  destruct Q as (R & F).
  destruct H.
  false.
  }
Qed.


Lemma and_true_true: forall m n,
    andb m n = true ->
    m = true /\ n = true.
Proof.
  intros.
  unfolds in H.
  destruct m.
  auto. 
  inverts H.
Qed.

Lemma and_false_false: forall m n,
    andb m n = false ->
    m = false \/ n = false.
Proof.
  intros.
  unfolds in H.
  destruct m; auto.
Qed.

Lemma Determinacy_Inturrupt_Eq:
  forall w1 w2 O O1 O2 ,
  interrupt w1 O = Some O1 ->
  interrupt w2 O = Some O2 ->
  get_tt O1 = get_tt O2 -> w1 = w2.
Proof.
  intros.
  unfolds in H.
  unfolds in H0.

  remember ((1 <=? Int.signed w1) && (Int.signed w1 <=? 15)).
  destruct b.
  remember ((1 <=? Int.signed w2) && (Int.signed w2 <=? 15)).
  destruct b.
  destruct O.
  destruct (negb (has_trap r) && trap_enabled r &&
      ((Int.signed w1 =? 15) || (Int.signed (get_R pil r) <? Int.signed w1))).
  destruct (negb (has_trap r) && trap_enabled r &&
      ((Int.signed w2 =? 15) || (Int.signed (get_R pil r) <? Int.signed w2))).
  remember (set_trap r # tt <- ($ (16 + Int.signed w1)), f).
  remember (set_trap r # tt <- ($ (16 + Int.signed w2)), f).
  inverts H0.
  inverts H.
  substs.

  unfolds in H1.
  unfolds in H1.
  assert (set_trap r # tt <- ($ (16 + Int.signed w1)) tt = r # tt <- ($ (16 + Int.signed w1)) tt).
  auto.
  assert (set_trap r # tt <- ($ (16 + Int.signed w2)) tt = r # tt <- ($ (16 + Int.signed w2)) tt).
  auto.

  rewrite H in H1.
  rewrite H0 in H1.
  clear H H0.

  assert (r # tt <- ($ (16 + Int.signed w1)) tt = $ (16 + Int.signed w1)).
  apply RegMap.gss.
  assert (r # tt <- ($ (16 + Int.signed w2)) tt = $ (16 + Int.signed w2)).
  apply RegMap.gss.
  rewrite H in H1.
  rewrite H0 in H1.
  clear H H0.

  symmetry in Heqb.
  apply and_true_true in Heqb.
  destruct Heqb as (A1 & A2).
  apply Z.leb_le in A1.
  apply Z.leb_le in A2.
  symmetry in Heqb0.
  apply and_true_true in Heqb0.
  destruct Heqb0 as (B1 & B2).
  apply Z.leb_le in B1.
  apply Z.leb_le in B2.

  remember (Int.signed w1) as n1.
  remember (Int.signed w2) as n2.

  assert (Int.signed ($ (16 + n1)) = Int.signed ($ (16 + n2))).
  rewrite H1. auto.
  clear H1.

  assert (17 <= (16 + n1) <= 31).  omega.
  assert (17 <= (16 + n2) <= 31).  omega.

  assert ( Int.min_signed <= (16 + n1) <= Int.max_signed ).
  {
    remember (16+n1) as n1'.
    intros.
    unfolds Int.max_signed.
    unfolds Int.min_signed.
    unfolds Int.half_modulus.
    unfolds Int.modulus.
    unfolds Int.wordsize.
    unfolds Wordsize_32.wordsize.
    unfolds two_power_nat.
    unfolds shift_nat.
    unfolds nat_rect.
    simpl.
    omega.
  }
  assert (Int.signed ($(16 + n1)) = 16 + n1). {
    apply Int.signed_repr. apply H2.
  }
  clear H2. rewrite H3 in H. clear H3.

  assert ( Int.min_signed <= (16 + n2) <= Int.max_signed ).
  {
    remember (16+n2) as n2'.
    intros.
    unfolds Int.max_signed.
    unfolds Int.min_signed.
    unfolds Int.half_modulus.
    unfolds Int.modulus.
    unfolds Int.wordsize.
    unfolds Wordsize_32.wordsize.
    unfolds two_power_nat.
    unfolds shift_nat.
    unfolds nat_rect.
    simpl.
    omega.
  }
  assert (Int.signed ($(16 + n2)) = 16 + n2). {
    apply Int.signed_repr. apply H2.
  }
  clear H2. rewrite H3 in H. clear H3.

  assert (n1 = n2). omega.

  assert (w1 = $n1). rewrite Heqn1.
  symmetry.
  apply Int.repr_signed.

  assert (w2 = $n2). rewrite Heqn2.
  symmetry.
  apply Int.repr_signed.

  substs. auto.

  inverts H0.
  inverts H.
  destruct O.
  inverts H0.
  destruct O.
  inverts H.
Qed.


Lemma Determinacy_Inturrupt_Trap:
  forall w Q Q',
  has_trap_Q Q ->
  interrupt w Q = Some Q' ->
  False.
Proof.
  intros.
  unfolds in H0.
  unfolds in H.
  destruct Q.
  unfolds in H.
  destruct ((1 <=? Int.signed w) && (Int.signed w <=? 15)).
  rewrite H in H0.
  simpl in H0.
  inverts H0.
  inverts H0.
Qed.

Lemma Determinacy_Inturrupt_Deq:
  forall w Q Q' e,
  interrupt w Q = Some Q' ->
  get_tt Q' = e ->
  interrupt_e e = false ->
  False.
Proof.
  intros.
  unfolds in H.
  unfolds in H1.
  unfolds in H0.
  destruct Q.
  remember ((1 <=? Int.signed w) && (Int.signed w <=? 15)).
  destruct b.
  destruct (negb (has_trap r) && trap_enabled r &&
      ((Int.signed w =? 15) || (Int.signed (get_R pil r) <? Int.signed w))).
  destruct Q'.
  remember (set_trap r # tt <- ($ (16 + Int.signed w))).
  inverts H.
  rewrite <- H2 in H0. clear H2.

  unfold get_R in H0.

  assert (forall R,set_trap R tt = R tt). {
    intros.
    unfolds.
    reflexivity.
  }
  rewrite H in H0. clear H.


  assert (r # tt <- ($ (16 + Int.signed w)) tt = ($ (16 + Int.signed w))). {
  apply RegMap.gss.
  }
  rewrite H in H0. clear H.

  remember (Int.signed w) as n.

  assert ( 1 <= n <= 15).
  {
    unfolds in Heqb.
    remember (1 <=? n).
    destruct b.
    - symmetry in Heqb0.
      apply Z.leb_le in Heqb0.
      symmetry in Heqb.
      apply Z.leb_le in Heqb.
      auto.
    - inverts Heqb.
  }

  assert ( 17 <= (16 + n) <= 31).
  {
    omega.
  }

  assert ( Int.min_signed <= (16 + n) <= Int.max_signed ).
  {
    remember (16+n) as n'.
    intros.
    unfolds Int.max_signed.
    unfolds Int.min_signed.
    unfolds Int.half_modulus.
    unfolds Int.modulus.
    unfolds Int.wordsize.
    unfolds Wordsize_32.wordsize.
    unfolds two_power_nat.
    unfolds shift_nat.
    unfolds nat_rect.
    simpl.
    omega.
  }

  assert (Int.signed ($(16 + n)) = 16 + n). {
    apply Int.signed_repr. apply H3.
  }

  rewrite <- H0 in H1.
  rewrite H4 in H1.

  clear H Heqn H2 H0 H3 H4.


  symmetry in Heqb.
  apply and_true_true in Heqb.
  destruct Heqb.
  apply Z.leb_le in H.
  apply Z.leb_le in H0.

  apply and_false_false in H1.
  destruct H1.

  assert ((17 <=? 16 + n) = true).
  {
    apply Z.leb_le.
    omega.
  }
  rewrite H1 in H2. inverts H2.

  assert ((16 + n <=? 31) = true).
  {
    apply Z.leb_le.
    omega.
  }
  rewrite H1 in H2. inverts H2.

  inverts H.
  inverts H.

Qed.

Lemma Determinacy_E:
    forall CP S e S1 S2,
    E__ CP S e S1 ->
    E__ CP S e S2 ->
    S1 = S2.
Proof.
  intros.
  inverts H; inverts H0; auto;
  try rename w into w1;
  try rename w0 into w2;
  try rename Q' into Q1;
  try rename Q'0 into Q2;
  try rename Q'' into Q1';
  try rename Q''0 into Q2';
  try rename Q''' into Q1'';
  try rename Q'''0 into Q2'';
  try rename D' into D1;
  try rename D'0 into D2;
  try rename Ms' into Ms1;
  try rename Ms'0 into Ms2.

  - symmetry in H11.
    assert (w1 = w2). apply (Determinacy_Inturrupt_Eq w1 w2 Q Q1 Q2); iauto.
    substs.
    rewrite H1 in H11. clear H1.
    inverts H11.
    rewrite H3 in H13. clear H3.
    inverts H13.
    assert ( Ms1 = Ms2 /\ Q1'' = Q2'' /\ D1 = D2). {
      apply (Determinacy_H Cs Ms Ms1 Ms2 Q2' Q1'' Q2'' D D1 D2); iauto.
    }
    inverts H.
    inverts H1.
    auto.
  - false. apply (Determinacy_Inturrupt_Trap w1 Q Q1); iauto.
  - false. apply (Determinacy_Inturrupt_Trap w1 Q Q2); iauto.
  - rewrite H3 in H13. clear H3.
    inverts H13.
    assert ( Ms1 = Ms2 /\ Q1' = Q2' /\ D1 = D2). {
    apply (Determinacy_H Cs Ms Ms1 Ms2 Q2 Q1' Q2' D D1 D2); iauto.
    }
    inverts H.
    inverts H2.
    auto.
Qed.

Lemma Determinacy_PE_Deq:
    forall CP S S1 S2 e,
    P__ CP S S1 ->
    interrupt_e e = false ->
    E__ CP S e S2 ->
    False.
Proof.
  intros.
  inverts H; inverts H0; auto;
  inverts H1; auto;
  try (apply (Determinacy_Inturrupt_Deq w Q Q'0 ((get_tt Q'0))); iauto);
  try (destruct Q as (R & F); false).
Qed.

Theorem Determinacy:
    forall n E CP S S1 S2,
    Z__ CP S E n S1 ->
    Z__ CP S E n S2 ->
    S1 = S2.
Proof.
  induction n as [|n'].
  - intros.
    inverts H; inverts H0; auto.
  - intros.
    assert (Z__ CP S E (Datatypes.S n') S1) as I1. apply H.
    assert (Z__ CP S E (Datatypes.S n') S2) as I2. apply H0.
    inverts H; inverts H0; auto.
    + assert (S'' = S''0).
      apply (IHn' E0 CP S S'' S''0); auto.
      substs.
      apply (Determinacy_P CP S''0); auto.
    + assert (S'' = S''0).
      apply (IHn' E0 CP S S'' S''0); auto.
      substs.
      apply (Determinacy_E CP S''0 e); auto.
Qed.

Definition empty_DL: State -> Prop :=
  fun S =>
    let '(_,_,D) := S in D = nil.

Theorem Non_Exfiltration_Iter:
    forall CP S S' n E,
    usr_mode_S S ->
    no_psr_S S ->
    Z__ CP S E n S' ->
    no_trap E ->
    sup_mem_eq S S' /\ usr_mode_S S' /\ no_psr_S S'.
Proof.
  intros.
  gen S S' E.
  induction n as [|n'].
  - intros.
    inverts H1.
    unfolds sup_mem_eq.
    split; auto.
    destruct S'.
    destruct p.
    destruct m.
    auto.
  - intros.
    inverts H1.
    assert (sup_mem_eq S S'' /\ usr_mode_S S'' /\ no_psr_S S''). {
    apply (IHn' S H H0 S'' E0); iauto.
    }
    clear IHn' H4.

    destruct S'' as (MPQ'' & D'').
    destruct MPQ'' as (MP'' & Q'').
    destruct MP'' as (Mu'' & Ms'').
    destruct S as (MPQ & D).
    destruct MPQ as (MP & Q).
    destruct MP as (Mu & Ms).
    destruct S' as (MPQ' & D').
    destruct MPQ' as (MP' & Q').
    destruct MP' as (Mu' & Ms').
    destruct CP as (Cu & Cs).

    simpl in H1.
    simpl.

    assert (usr_mode_Q Q' /\ Ms'' = Ms' /\ no_psr D'). {
      apply (UserMode_P Cu Cs Mu'' Mu' Ms'' Ms' Q'' Q' D'' D'); iauto.
    }
    inverts H1.
    inverts H3.
    inverts H4.
    iauto.


  false.
Qed.

Definition ArrorWR: CodePair -> State -> nat -> State -> Prop:=
    fun CP S n S' =>
    exists E,usr_mode_S S /\ empty_DL S /\ Z__ CP S E n S' /\ no_trap E.

Theorem ModeControl:
    forall CP S n S',
      ArrorWR CP S n S' ->
      usr_mode_S S'.
Proof.
  intros.
  unfolds in H.
  destruct H as (E & H).
  destruct H as (H0 & H1 & H2 & H3).
  apply (Non_Exfiltration_Iter CP S S' n E); iauto.
  unfolds.
  destruct S.
  destruct p.
  unfolds in H1.
  substs. unfolds. auto.
Qed.


Theorem Non_Exfiltration:
    forall CP S n S',
      ArrorWR CP S n S' ->
      sup_mem_eq S S'.
Proof.
  intros.
  unfolds in H.
  destruct H as (E & H).
  destruct H as (H0 & H1 & H2 & H3).
  apply (Non_Exfiltration_Iter CP S S' n E); iauto.
  unfolds.
  destruct S.
  destruct p.
  unfolds in H1.
  substs. unfolds. auto.
Qed.



Lemma Non_Infiltration_Iter:
    forall n CP1 CP2 S1 S1' S2 S2' E1 E2,
    usr_mode_S S1 /\ no_psr_S S1 ->
    usr_mode_S S2 /\ no_psr_S S2 ->
    usr_code_eq CP1 CP2 /\ low_eq S1 S2 ->
    Z__ CP1 S1 E1 n S1' /\ Z__ CP2 S2 E2 n S2' ->
    no_trap E1 /\ no_trap E2 ->
    low_eq S1' S2' /\ usr_mode_S S1' /\ usr_mode_S S2' /\ no_psr_S S1' /\ no_psr_S S2'.
Proof.
  induction n.
  - intros.
    destruct H2 as (I1 & I2).
    inverts I1; inverts I2; auto.
    splits; iauto.
  - intros.
    destruct H2 as (I1 & I2).
    inverts I1; inverts I2; auto.

    rename S'' into S1''.
    rename S''0 into S2''.
    assert (low_eq S1'' S2'' /\ usr_mode_S S1'' /\ usr_mode_S S2'' /\ no_psr_S S1'' /\ no_psr_S S2''). {
    apply (IHn CP1 CP2 S1 S1'' S2 S2'' E E0);
    try split; iauto.
    }

    clear IHn H4 H5.

    destruct CP1 as (Cu1 & Cs1).
    destruct CP2 as (Cu2 & Cs2).

    split.
    apply (LowEq_P Cu1 Cu2 Cs1 Cs2 S1'' S2'' S1' S2'); iauto.
    destruct S1'' as (MPQ1'' & D1'').
    destruct MPQ1'' as (MP1'' & Q1'').
    destruct MP1'' as (Mu1'' & Ms1'').
    destruct S2'' as (MPQ2'' & D2'').
    destruct MPQ2'' as (MP2'' & Q2'').
    destruct MP2'' as (Mu2'' & Ms2'').
    destruct S1' as (MPQ1' & D1').
    destruct MPQ1' as (MP1' & Q1').
    destruct MP1' as (Mu1' & Ms1').
    destruct S2' as (MPQ2' & D2').
    destruct MPQ2' as (MP2' & Q2').
    destruct MP2' as (Mu2' & Ms2').


    assert (usr_mode_S (Mu1', Ms1', Q1', D1') /\ Ms1'' = Ms1' /\ no_psr D1'). {
    apply (UserMode_P Cu1 Cs1 Mu1'' Mu1' Ms1'' Ms1' Q1'' Q1' D1'' D1'); iauto.
    }

    assert (usr_mode_S (Mu2', Ms2', Q2', D2') /\ Ms2'' = Ms2' /\ no_psr D2'). {
    apply (UserMode_P Cu2 Cs2 Mu2'' Mu2' Ms2'' Ms2' Q2'' Q2' D2'' D2'); iauto.
    }

    simpl in H4.
    simpl in H5.
    simpl.
    splits; iauto.

    inverts H3.
    inverts H6.

    inverts H3.
    inverts H2.

    inverts H3.
    inverts H2.

Qed.

Theorem Non_Infiltration:
  forall n CP1 CP2 S1 S1' S2 S2',
    usr_code_eq CP1 CP2 /\ low_eq S1 S2 ->
    ArrorWR CP1 S1 n S1' /\ ArrorWR CP2 S2 n S2' ->
    low_eq S1' S2'.
Proof.
  intros.
  destruct H.
  destruct H0.
  destruct H0 as (E1 & Hx).
  destruct H2 as (E2 & Hy).
  destruct Hx as (Hx0 & Hx1 & Hx2 & Hx3).
  destruct Hy as (Hy0 & Hy1 & Hy2 & Hy3).
  apply (Non_Infiltration_Iter n CP1 CP2 S1 S1' S2 S2' E1 E2); iauto;
  splits; iauto.
  unfolds.
  destruct S1.
  destruct p.
  unfolds in Hx1.
  substs. unfolds. auto.
  unfolds.
  destruct S2.
  destruct p.
  unfolds in Hy1.
  substs. unfolds. auto.
Qed.

Lemma Exsits_Q:
  forall i M R F D,
    abort_ins i (R,F) M = false ->
    unexpected_trap i (R,F) = None ->
    exists M' R' F' D', Q__ (M,(R,F),D) i (M',(R',F'),D').
Proof.
  intros.
  destruct i;
  unfolds in H;
  unfolds in H0;
  unfold trap_type in H0.

  - (* bicc *)
    remember (eval_AddrExp a R) as W.
    destruct W; try solve [inverts H].
    clear H.
    remember (negb (word_aligned w)) as B.
    destruct B; try solve [inverts H0].
    assert (word_aligned_R w). {
      unfolds in HeqB.
      remember (word_aligned w).
      destruct b.
      unfolds. auto.
      inverts HeqB.
    }
    clear H0.

    remember (eval_TestCond t R).
    destruct b; symmetry in Heqb.
    assert (Q__ (M, (R,F),D) (bicc t a) (M, (djmp w R,F),D)).
    {
      apply MR.
      apply (Bicc_true t a (bicc t a) w M R); auto.
    }
    exists M (djmp w R) F D. auto.

    assert (Q__ (M, (R,F),D) (bicc t a) (M, (next R,F),D)). {
      apply MR.
      apply (Bicc_false t a (bicc t a) w M R); auto.
    }
    exists M (next R) F D. auto.

  - (* bicca *)
    remember (eval_AddrExp a R) as W.
    destruct W; try solve [inverts H].
    clear H.
    remember (negb (word_aligned w)) as B.
    destruct B; try solve [inverts H0].
    assert (word_aligned_R w). {
      unfolds in HeqB.
      remember (word_aligned w).
      destruct b.
      unfolds. auto.
      inverts HeqB.
    }
    clear H0.

    destruct t.
    assert (Q__ (M, (R,F),D) (bicca al a) (M,(set_annul(djmp w R),F),D)). {
      apply MR.
      apply (Bicca_always a (bicca al a) w M R); auto.
    }
    exists M (set_annul(djmp w R)) F D. auto.

    assert (Q__ (M, (R,F),D) (bicca nv a) (M,(set_annul(next R),F),D)). {
      apply MR.
      apply (Bicca_false nv a (bicca nv a) w M R); auto.
    }
    exists M (set_annul(next R)) F D. auto.

    remember (eval_TestCond ne R).
    destruct b.
    assert (Q__ (M, (R,F),D) (bicca ne a) (M,(djmp w R,F),D)). {
      apply MR.
      apply (Bicca ne a (bicca ne a) w M R); auto.
      unfolds. intros I. inverts I.
    }
    exists M (djmp w R) F D. auto.
    assert (Q__ (M, (R,F),D) (bicca ne a) (M,(set_annul(next R),F),D)). {
      apply MR.
      apply (Bicca_false ne a (bicca ne a) w M R); auto.
    }
    exists M (set_annul(next R)) F D. auto.

    remember (eval_TestCond eq R).
    destruct b.
    assert (Q__ (M, (R,F),D) (bicca eq a) (M,(djmp w R,F),D)). {
      apply MR.
      apply (Bicca eq a (bicca eq a) w M R); auto.
      unfolds. intros I. inverts I.
    }
    exists M (djmp w R) F D. auto.
    assert (Q__ (M, (R,F),D) (bicca eq a) (M,(set_annul(next R),F),D)). {
      apply MR.
      apply (Bicca_false eq a (bicca eq a) w M R); auto.
    }
    exists M (set_annul(next R)) F D. auto.

  - (* jmpl *)
    remember (eval_AddrExp a R) as W.
    destruct W; try solve [inverts H]. clear H.
    remember (negb (word_aligned w)) as B.
    destruct B; try solve [inverts H0].
    assert (word_aligned_R w). {
      unfolds in HeqB.
      remember (word_aligned w).
      destruct b.
      unfolds. auto.
      inverts HeqB.
    }

    remember (save_pc g R) as R'.

    assert (Q__ (M, (R,F),D) (jmpl a g) (M,(djmp w R',F),D)). {
      apply MR.
      apply (Jmpl g a (jmpl a g) w M R R'); auto.
    }
    exists M (djmp w R') F D. auto.

  - (* ld *)
    remember (eval_AddrExp a R) as W.
    destruct W; try solve [inverts H].
    remember (M w) as A;
    destruct A; try solve [inverts H].
    clear H.
    remember (negb (word_aligned w)) as B.
    destruct B; try solve [inverts H0].
    assert (word_aligned_R w). {
      unfolds in HeqB.
      remember (word_aligned w).
      destruct b.
      unfolds. auto.
      inverts HeqB.
    }
    clear H0.

    remember (R#g <- w0) as R'.
    assert (Q__ (M, (R,F),D) (ld a g)  (M,(next R',F),D)). {
      apply MR.
      apply (Ld g a (ld a g) w w0 M R R'); auto.
    }
    exists M (next R') F D. auto.

  - (* st *)
    remember (eval_AddrExp a R) as W.
    destruct W; try solve [inverts H].
    clear H.
    remember (negb (word_aligned w)) as B.
    destruct B; try solve [inverts H0].
    assert (word_aligned_R w). {
      unfolds in HeqB.
      remember (word_aligned w).
      destruct b.
      unfolds. auto.
      inverts HeqB.
    }
    clear H0.

    remember (WordMap.set w (Some(R#g)) M) as M'.
    assert (Q__ (M, (R,F),D) (st g a) (M',(next R,F),D)). {
      apply MR.
      apply (St g a (st g a) w M M' R); auto.
    }
    exists M' (next R) F D. auto.

  - remember (eval_TrapExp t0 R) as W.
    destruct W; try solve [inverts H].
    clear H.

    remember (eval_TestCond t R).
    destruct b.

    assert (Q__ (M, (R,F),D)  (ticc t t0) (M,(set_user_trap (get_range 0 6 w) R,F),D)). {
      apply MR.
      apply (Ticc_true t t0 (ticc t t0) w M R); auto.
    }
    exists M (set_user_trap (get_range 0 6 w) R) F D. auto.

    assert (Q__ (M, (R,F),D)  (ticc t t0) (M,(next R,F),D)). {
      apply MR.
      apply (Ticc_false t t0 (ticc t t0) w M R); auto.
    }
    exists M (next R) F D. auto.

  - (* save *)
    remember (eval_OpExp o R) as W.
    destruct W; try solve [inverts H].
    remember (dec_win (R, F)) as I.
    destruct I; try solve [inverts H0].
    destruct r as (R' & F').
    remember (R'#g0 <- ((R#g) +ᵢ w)) as R''.
    assert (Q__ (M,(R,F),D) (save g o g0) (M,(next R'',F'),D)). {
      apply (Save g o g0 (save g o g0) w M R R' R'' F F'); auto.
    }
    exists M (next R'') F' D. auto.

  - (* restore *)
    remember (eval_OpExp o R) as W.
    destruct W; try solve [inverts H].
    remember (inc_win (R, F)) as I.
    destruct I; try solve [inverts H0].
    destruct r as (R' & F').
    remember (R'#g0 <- ((R#g) +ᵢ w)) as R''.
    assert (Q__ (M,(R,F),D) (restore g o g0) (M,(next R'',F'),D)). {
      apply (Restore g o g0 (restore g o g0) w M R R' R'' F F'); auto.
    }
    exists M (next R'') F' D. auto.

  - (* rett *)
    remember (eval_AddrExp a R) as W.
    destruct W; try solve [inverts H].
    remember (word_aligned w) as B.
    destruct B; try solve [inverts H].
    remember (usr_mode R).
    destruct b; try solve [inverts H].
    remember (inc_win (R, F)) as I.
    destruct I; try solve [inverts H].
    destruct r as (R' & F').
    clear H.
    remember (trap_enabled R) as T.
    destruct T; try solve [inverts H0].
    clear H0.

    remember (rett_f (R,F)) as K.
    unfolds in HeqK.
    rewrite <- HeqI in HeqK.
    remember (restore_mode (enable_trap R')) as R''.
 
    assert (Q__ (M,(R,F),D) (rett a) (M,(djmp w R'',F'),D)). {
      apply (Rett a (rett a) w M R R'' F F'); try solve [unfolds; auto]; auto.
      unfolds. rewrite <- HeqI. rewrite HeqR''. auto.
    }
    exists M (djmp w R'') F' D. auto.

  - (* rd *)
    destruct s;
    remember (usr_mode R);
    destruct b; try solve [inverts H0].

    remember (R#g <- (R#psr)) as R'.
    assert (Q__ (M,(R,F),D) (rd psr g) (M,(next R',F),D)). {
      apply MR.
      apply (Rd_sup psr g (rd psr g) M R R'); auto.
      unfolds. auto.
    }
    exists M (next R') F D. auto.

    remember (R#g <- (R#wim)) as R'.
    assert (Q__ (M,(R,F),D) (rd wim g) (M,(next R',F),D)). {
      apply MR.
      apply (Rd_sup wim g (rd wim g) M R R'); auto.
      unfolds. auto.
    }
    exists M (next R') F D. auto.

    remember (R#g <- (R#tbr)) as R'.
    assert (Q__ (M,(R,F),D) (rd tbr g) (M,(next R',F),D)). {
      apply MR.
      apply (Rd_sup tbr g (rd tbr g) M R R'); auto.
      unfolds. auto.
    }
    exists M (next R') F D. auto.

    remember (R#g <- (R#y)) as R'.
    assert (Q__ (M,(R,F),D) (rd y g) (M,(next R',F),D)). {
      apply MR.
      apply (Rd_usr y g (rd y g) M R R'); auto.
      unfolds. auto.
      split; try split; try unfolds; intros; inverts H1.
    }
    exists M (next R') F D. auto.

    remember (R#g <- (R#y)) as R'.
    assert (Q__ (M,(R,F),D) (rd y g) (M,(next R',F),D)). {
      apply MR.
      apply (Rd_sup y g (rd y g) M R R'); auto.
      unfolds. auto.
    }
    exists M (next R') F D. auto.

    remember (R#g <- (R#a)) as R'.
    assert (Q__ (M,(R,F),D) (rd a g) (M,(next R',F),D)). {
      apply MR.
      apply (Rd_usr a g (rd a g) M R R'); auto.
      unfolds. auto.
      split; try split; try unfolds; intros; inverts H1.
    }
    exists M (next R') F D. auto.

    remember (R#g <- (R#a)) as R'.
    assert (Q__ (M,(R,F),D) (rd a g) (M,(next R',F),D)). {
      apply MR.
      apply (Rd_sup a g (rd a g) M R R'); auto.
      unfolds. auto.
    }
    exists M (next R') F D. auto.

 - (* wr *)
    remember (eval_OpExp o R) as W.
    destruct W; try solve [inverts H];
    clear H;
    remember ((R#g) xor w) as k;
    destruct s;
    remember (usr_mode R);
    destruct b; try solve [inverts H0].

    remember ((get_range 0 4 k) >=ᵢ Asm.N);
    destruct b; try solve [inverts H0];
    clear H0.

    remember (set_delay psr k D) as D'.
    remember (R#et <- (get_bit 5 k)
              #pil <- (get_range 8 11 k)) as R'.
    assert (Q__ (M,(R,F),D) (wr g o psr) (M,(next R',F),D')).
    {
      apply (Wr_psr g o (wr g o psr) w k M R R'); iauto.
      unfolds. auto.
    }
    exists M (next R') F D'. auto.

    remember (set_delay wim k D) as D'.
    assert (Q__ (M,(R,F),D) (wr g o wim) (M,(next R,F),D')).
    {
      apply (Wr_sup g o wim (wr g o wim) w k M R F D D'); iauto.
      unfolds. auto.
      unfolds. intros. inverts H.
    }
    exists M (next R) F D'. auto.

    remember (set_delay tbr k D) as D'.
    assert (Q__ (M,(R,F),D) (wr g o tbr) (M,(next R,F),D')).
    {
      apply (Wr_sup g o tbr (wr g o tbr) w k M R F D D'); iauto.
      unfolds. auto.
      unfolds. intros. inverts H.
    }
    exists M (next R) F D'. auto.

    remember (set_delay y k D) as D'.
    assert (Q__ (M,(R,F),D) (wr g o y) (M,(next R,F),D')).
    {
      apply (Wr_usr g o y (wr g o y) w k M R F D D'); iauto.
      unfolds. auto.
      splits; unfolds; intros; inverts H.
    }
    exists M (next R) F D'. auto.

    remember (set_delay y k D) as D'.
    assert (Q__ (M,(R,F),D) (wr g o y) (M,(next R,F),D')).
    {
      apply (Wr_sup g o y (wr g o y) w k M R F D D'); iauto.
      unfolds. auto.
      unfolds. intros. inverts H.
    }
    exists M (next R) F D'. auto.

    remember (set_delay a k D) as D'.
    assert (Q__ (M,(R,F),D) (wr g o a) (M,(next R,F),D')).
    {
      apply (Wr_usr g o a (wr g o a) w k M R F D D'); iauto.
      unfolds. auto.
      splits; unfolds; intros; inverts H.
    }
    exists M (next R) F D'. auto.

    remember (set_delay a k D) as D'.
    assert (Q__ (M,(R,F),D) (wr g o a) (M,(next R,F),D')).
    {
      apply (Wr_sup g o a (wr g o a) w k M R F D D'); iauto.
      unfolds. auto.
      unfolds. intros. inverts H.
    }
    exists M (next R) F D'. auto.


  - (* sll *)
    remember (eval_OpExp o R) as W.
    destruct W; try solve [inverts H].
    clear H. clear H0.
    remember ((R#g) <<ᵢ (get_range 0 4 w)) as k.
    remember (R#g0 <- k) as R'.
    assert (Q__ (M,(R,F),D) (sll g o g0) (M,(next R',F),D)). {
    apply MR.
    apply (Sll g o g0 (sll g o g0) w k M R R'); auto.
    }
    exists M (next R') F D. auto.

  - (* srl *)
    remember (eval_OpExp o R) as W.
    destruct W; try solve [inverts H].
    clear H. clear H0.
    remember ((R#g) >>ᵢ (get_range 0 4 w)) as k.
    remember (R#g0 <- k) as R'.
    assert (Q__ (M,(R,F),D) (srl g o g0) (M,(next R',F),D)). {
    apply MR.
    apply (Srl g o g0 (srl g o g0) w k M R R'); auto.
    }
    exists M (next R') F D. auto.

  - (* or *)
    remember (eval_OpExp o R) as W.
    destruct W; try solve [inverts H].
    clear H. clear H0.
    remember ((R#g) |ᵢ w) as k.
    remember (R#g0 <- k) as R'.
    assert (Q__ (M,(R,F),D) (or g o g0) (M,(next R',F),D)). {
    apply MR.
    apply (Or_ g o g0 (or g o g0) w k M R R'); auto.
    }
    exists M (next R') F D. auto.

  - (* and *)
    remember (eval_OpExp o R) as W.
    destruct W; try solve [inverts H].
    clear H. clear H0.
    remember ((R#g) &ᵢ w) as k.
    remember (R#g0 <- k) as R'.
    assert (Q__ (M,(R,F),D) (and g o g0) (M,(next R',F),D)). {
    apply MR.
    apply (And_ g o g0 (and g o g0) w k M R R'); auto.
    }
    exists M (next R') F D. auto.

  - (* nop *)
    assert (Q__ (M,(R,F),D) nop (M,(next R,F),D)). {
    apply MR.
    apply (Nop nop M R). auto.
    }
    exists M (next R) F D. auto.
Qed.



Lemma Exsits_Ins:
  forall i M Q D,
    abort_ins i Q M = false ->
    exists M' Q' D', Q__ (M,Q,D) i (M',Q',D').
Proof.
  intros.
  remember (unexpected_trap i Q).
  destruct o.
  assert (Q__ (M,Q,D) i (M,r,D)). {
    apply (Trap_ins i M Q r); auto.
  }
  exists M r D. auto.

  destruct Q as (R & F).
  assert (exists M' R' F' D', Q__ (M,(R,F),D) i (M',(R',F'),D')). {
    apply (Exsits_Q i M R F D); auto.
  }

  destruct H0 as (M' & R' & F' & D' & Hl).
  exists M' (R',F') D'. auto.
Qed.


Lemma Hold_Annul:
   forall D D' Q Q',
      annuled_Q Q ->
      exe_delay Q D = (Q',D') ->
      annuled_Q Q'.
Proof.
  induction D.
  - intros.
    inverts H0; auto.
  - intros.
    unfolds in H0.

    asserts_rewrite (
      (fix exe_delay (Q : RState) (D : DelayList) {struct D} :
               RState * DelayList :=
               match D with
               | [] => (Q, D)
               | (0%nat, syb0, w0) :: D' =>
                   let (Q', D'') := exe_delay Q D' in
                   let (R', F') := Q' in
                   match syb0 with
                   | psr =>
                       (set_win (get_range 0 4 w0) (R' # syb0 <- w0, F'),
                       D'')
                   | wim => (R' # syb0 <- w0, F', D'')
                   | tbr => (R' # syb0 <- w0, F', D'')
                   | y => (R' # syb0 <- w0, F', D'')
                   | Sasr _ => (R' # syb0 <- w0, F', D'')
                   end
               | (S k, syb0, w0) :: D' =>
                   let (Q', D'') := exe_delay Q D' in
                   (Q', (k, syb0, w0) :: D'')
               end) Q D
      = exe_delay Q D) in H0.
    { unfolds. auto. }

    remember (exe_delay Q D).
    destruct p as (Q'' & D'').
    assert (annuled_Q Q''). {
      apply (IHD D'' Q Q''); iauto.
    }
    clear IHD Heqp.

    {
    destruct a.
    destruct p.
    destruct Q'' as (R'' & F'').
    destruct Q' as (R' & F').
    unfolds.
    unfolds in H1.
    unfolds in H1.
    unfolds in H1.
    assert ((get_R annul R'') =ᵢ ($ 1) = true). {
      destruct ((get_R annul R'') =ᵢ ($ 1)); iauto.
    } clear H1. rename H2 into H1.
    unfolds.
    unfolds.
    assert ((get_R annul R') =ᵢ ($ 1) = true -> ((if (get_R annul R') =ᵢ ($ 1) then true else false) = true)).
    {
      intros.
      destruct ((get_R annul R') =ᵢ ($ 1)); iauto.
    }
    apply H2.
    clear H2.
    destruct d;
    destruct s;
    try solve [inverts H0; auto].

    {
    remember (set_win (get_range 0 4 w) (R'' # psr <- w, F'')).
    destruct r as (R''' & F''').

    assert ((R'' # psr <- w)#annul = R'''#annul). {
      apply (Hold_Sth_SetWin (R'' # psr <- w) R''' F'' F''' (get_range 0 4 w)); iauto.
    }
    assert (get_R annul R'' # psr <- w = get_R annul R''). iauto.
    rewrite H3 in H2.
    clear H3 Heqr.
    inverts H0.
    rewrite <- H2. auto.
    }

    }
Qed.


Lemma Hold_Annul2:
   forall D D' Q Q',
      not_annuled_Q Q ->
      exe_delay Q D = (Q',D') ->
      not_annuled_Q Q'.
Proof.
  induction D.
  - intros.
    inverts H0; auto.
  - intros.
    unfolds in H0.

    asserts_rewrite (
      (fix exe_delay (Q : RState) (D : DelayList) {struct D} :
               RState * DelayList :=
               match D with
               | [] => (Q, D)
               | (0%nat, syb0, w0) :: D' =>
                   let (Q', D'') := exe_delay Q D' in
                   let (R', F') := Q' in
                   match syb0 with
                   | psr =>
                       (set_win (get_range 0 4 w0) (R' # syb0 <- w0, F'),
                       D'')
                   | wim => (R' # syb0 <- w0, F', D'')
                   | tbr => (R' # syb0 <- w0, F', D'')
                   | y => (R' # syb0 <- w0, F', D'')
                   | Sasr _ => (R' # syb0 <- w0, F', D'')
                   end
               | (S k, syb0, w0) :: D' =>
                   let (Q', D'') := exe_delay Q D' in
                   (Q', (k, syb0, w0) :: D'')
               end) Q D
      = exe_delay Q D) in H0.
    { unfolds. auto. }

    remember (exe_delay Q D).
    destruct p as (Q'' & D'').
    assert (not_annuled_Q Q''). {
      apply (IHD D'' Q Q''); iauto.
    }
    clear IHD Heqp.

    {
    destruct a.
    destruct p.
    destruct Q'' as (R'' & F'').
    destruct Q' as (R' & F').
    unfolds.
    unfolds in H1.
    unfolds in H1.
    unfolds in H1.
    assert ((get_R annul R'') =ᵢ ($ 1) = false). {
      destruct ((get_R annul R'') =ᵢ ($ 1)); iauto.
    } clear H1. rename H2 into H1.
    unfolds.
    unfolds.
    assert ((get_R annul R') =ᵢ ($ 1) = false -> ((if (get_R annul R') =ᵢ ($ 1) then true else false) = false)).
    {
      intros.
      destruct ((get_R annul R') =ᵢ ($ 1)); iauto.
    }
    apply H2.
    clear H2.
    destruct d;
    destruct s;
    try solve [inverts H0; auto].

    {
    remember (set_win (get_range 0 4 w) (R'' # psr <- w, F'')).
    destruct r as (R''' & F''').

    assert ((R'' # psr <- w)#annul = R'''#annul). {
      apply (Hold_Sth_SetWin (R'' # psr <- w) R''' F'' F''' (get_range 0 4 w)); iauto.
    }
    assert (get_R annul R'' # psr <- w = get_R annul R''). iauto.
    rewrite H3 in H2.
    clear H3 Heqr.
    inverts H0.
    rewrite <- H2. auto.
    }

    }
Qed.


Lemma Exsits_H:
  forall C M Q Q' D D' i,
    exe_delay Q D = (Q',D') ->
    C (cursor_Q Q') = Some i ->
    abort_ins i Q' M = false ->
    exists M'' Q'' D'', H__ C (M,Q,D) (M'',Q'',D'').
Proof.
  intros.
  remember (exe_delay Q D).
  destruct p as (Q'' & D'').
  inverts H.
  destruct Q as (R & F).
  remember (annuled R).
  destruct b.

  remember (clear_annul_Q Q') as Q''.

  assert (H__ C (M,(R,F),D) (M,next_Q Q'',D')). {
    apply (Annul C M (R,F) Q' Q'' D D'); iauto.
    apply (Hold_Annul D D' ((R, F)) Q'); iauto.
    unfolds. unfolds. iauto.
  }

  exists M (next_Q Q'') D'. auto.

  remember (R,F) as Q.
  assert (exists M'' Q'' D'', Q__ (M,Q',D') i (M'',Q'',D'')). {
    apply (Exsits_Ins i M Q'); auto.
  }

  destruct H as (M'' & Q'' & D'' & Hl).
  destruct Q'' as (R'' & F'').

  remember (R'', F'') as Q''.

  assert (not_annuled_Q Q'). {
    apply (Hold_Annul2 D D' Q Q'); iauto.
    rewrite HeqQ.
    unfolds. unfolds. iauto.
  }

  assert (H__ C (M,Q,D) (M'',Q'',D'')). {
    apply (Normal i C M M'' Q Q' Q'' D D' D''); iauto.
  }

  exists M'' Q'' D''. auto.
Qed.



Definition not_abort(C: CodeHeap)(M: Memory)(Q: RState)(D: DelayList) :Prop :=
  exists Q' D' i,
    exe_delay Q D = (Q',D') /\
    C (cursor_Q Q') = Some i /\
    abort_ins i Q' M = false.


Lemma Exsits_H2:
  forall C M Q D,
    not_abort C M Q D ->
    exists M'' Q'' D'', H__ C (M,Q,D) (M'',Q'',D'').
Proof.
  intros.

  unfolds in H.
  destruct H as (Q' & D' & i & H & H1 & H2).

  apply (Exsits_H C M Q Q' D D' i); iauto.
Qed.


Lemma Exists_P_Sup:
  forall Cu Cs Mu Ms Q D,
    no_trap_Q Q ->
    sup_mode_Q Q ->
    not_abort Cs Ms Q D ->
    exists Ms' Q' D', P__ (Cu,Cs) ((Mu,Ms),Q,D) ((Mu,Ms'),Q',D').
Proof.
  intros.

  assert (exists Ms'' Q'' D'', H__ Cs (Ms,Q,D) (Ms'',Q'',D'')). {
    apply (Exsits_H2 Cs Ms Q ); auto.
  }
  destruct H2 as (Ms'' & Q'' & D'' & Hl).
  assert (P__ (Cu,Cs) ((Mu,Ms),Q,D) ((Mu,Ms''),Q'',D'')). {
    apply (Nor_sup Q Q'' Cs Cu Ms Ms'' Mu D D''); iauto.
  }
  exists Ms'' Q'' D''. auto.
Qed.

Definition f_context(F: FrameList) :=
  exists
    P_w00 P_w01 P_w02 P_w03 P_w04 P_w05 P_w06 P_w07 
    P_w10 P_w11 P_w12 P_w13 P_w14 P_w15 P_w16 P_w17 
    P_w20 P_w21 P_w22 P_w23 P_w24 P_w25 P_w26 P_w27 
    P_w30 P_w31 P_w32 P_w33 P_w34 P_w35 P_w36 P_w37 
    P_w40 P_w41 P_w42 P_w43 P_w44 P_w45 P_w46 P_w47 
    P_w50 P_w51 P_w52 P_w53 P_w54 P_w55 P_w56 P_w57 
    P_w60 P_w61 P_w62 P_w63 P_w64 P_w65 P_w66 P_w67 
    P_w70 P_w71 P_w72 P_w73 P_w74 P_w75 P_w76 P_w77 
    P_w80 P_w81 P_w82 P_w83 P_w84 P_w85 P_w86 P_w87 
    P_w90 P_w91 P_w92 P_w93 P_w94 P_w95 P_w96 P_w97 
    P_wa0 P_wa1 P_wa2 P_wa3 P_wa4 P_wa5 P_wa6 P_wa7 
    P_wb0 P_wb1 P_wb2 P_wb3 P_wb4 P_wb5 P_wb6 P_wb7 
    P_wc0 P_wc1 P_wc2 P_wc3 P_wc4 P_wc5 P_wc6 P_wc7,
  F =
   [[P_w00;P_w01;P_w02;P_w03;P_w04;P_w05;P_w06;P_w07];
    [P_w10;P_w11;P_w12;P_w13;P_w14;P_w15;P_w16;P_w17];
    [P_w20;P_w21;P_w22;P_w23;P_w24;P_w25;P_w26;P_w27];
    [P_w30;P_w31;P_w32;P_w33;P_w34;P_w35;P_w36;P_w37];
    [P_w40;P_w41;P_w42;P_w43;P_w44;P_w45;P_w46;P_w47];
    [P_w50;P_w51;P_w52;P_w53;P_w54;P_w55;P_w56;P_w57];
    [P_w60;P_w61;P_w62;P_w63;P_w64;P_w65;P_w66;P_w67];
    [P_w70;P_w71;P_w72;P_w73;P_w74;P_w75;P_w76;P_w77];
    [P_w80;P_w81;P_w82;P_w83;P_w84;P_w85;P_w86;P_w87];
    [P_w90;P_w91;P_w92;P_w93;P_w94;P_w95;P_w96;P_w97];
    [P_wa0;P_wa1;P_wa2;P_wa3;P_wa4;P_wa5;P_wa6;P_wa7];
    [P_wb0;P_wb1;P_wb2;P_wb3;P_wb4;P_wb5;P_wb6;P_wb7];
    [P_wc0;P_wc1;P_wc2;P_wc3;P_wc4;P_wc5;P_wc6;P_wc7]].



Lemma left_then_right1 :
  forall (i:RegNameEq.t) R F R' F' R'' F'',
      f_context F ->
      left_win 1 (R,F) = (R',F') ->
      right_win 1 (R',F') = (R'',F'') ->
      i <> cwp ->
      R i = R'' i.
Proof.
  intros.
  rewrite <- H0 in H1.
  clear H0.
  unfold right_win in H1.
  unfold left_win in H1.
  asserts_rewrite ((Z.to_nat 1) = 1%nat) in H1. compute. auto.
  unfold left_iter in H1.
  unfold right_iter in H1.
  unfolds in H.
  destruct H as (
    P_w00 & P_w01 & P_w02 & P_w03 & P_w04 & P_w05 & P_w06 & P_w07 &
    P_w10 & P_w11 & P_w12 & P_w13 & P_w14 & P_w15 & P_w16 & P_w17 &
    P_w20 & P_w21 & P_w22 & P_w23 & P_w24 & P_w25 & P_w26 & P_w27 &
    P_w30 & P_w31 & P_w32 & P_w33 & P_w34 & P_w35 & P_w36 & P_w37 & 
    P_w40 & P_w41 & P_w42 & P_w43 & P_w44 & P_w45 & P_w46 & P_w47 & 
    P_w50 & P_w51 & P_w52 & P_w53 & P_w54 & P_w55 & P_w56 & P_w57 & 
    P_w60 & P_w61 & P_w62 & P_w63 & P_w64 & P_w65 & P_w66 & P_w67 & 
    P_w70 & P_w71 & P_w72 & P_w73 & P_w74 & P_w75 & P_w76 & P_w77 & 
    P_w80 & P_w81 & P_w82 & P_w83 & P_w84 & P_w85 & P_w86 & P_w87 & 
    P_w90 & P_w91 & P_w92 & P_w93 & P_w94 & P_w95 & P_w96 & P_w97 & 
    P_wa0 & P_wa1 & P_wa2 & P_wa3 & P_wa4 & P_wa5 & P_wa6 & P_wa7 & 
    P_wb0 & P_wb1 & P_wb2 & P_wb3 & P_wb4 & P_wb5 & P_wb6 & P_wb7 & 
    P_wc0 & P_wc1 & P_wc2 & P_wc3 & P_wc4 & P_wc5 & P_wc6 & P_wc7 & H).
  substs.
  unfold left in H1.
  unfold right in H1.
  unfold fench in H1.
  unfold replace in H1.
  simpl in H1.
  inverts H1.

  destruct i;
  simpl; auto.
  destruct g;
  simpl; auto.
  destruct p;
  simpl; auto.
  unfolds in H2.
  false.
Qed.


Lemma right_cwp:
  forall R R' F F',
  f_context F ->
  right_win 1 (R,F) = (R',F') ->
  R'#cwp = pre_cwp 1 R.
Proof.
  intros.
  unfold right_win in *.
  asserts_rewrite ((Z.to_nat 1) = 1%nat) in *. compute. auto.
  unfold right_iter in *.
  unfolds in H.
  destruct H as (
    P_w00 & P_w01 & P_w02 & P_w03 & P_w04 & P_w05 & P_w06 & P_w07 &
    P_w10 & P_w11 & P_w12 & P_w13 & P_w14 & P_w15 & P_w16 & P_w17 &
    P_w20 & P_w21 & P_w22 & P_w23 & P_w24 & P_w25 & P_w26 & P_w27 &
    P_w30 & P_w31 & P_w32 & P_w33 & P_w34 & P_w35 & P_w36 & P_w37 & 
    P_w40 & P_w41 & P_w42 & P_w43 & P_w44 & P_w45 & P_w46 & P_w47 & 
    P_w50 & P_w51 & P_w52 & P_w53 & P_w54 & P_w55 & P_w56 & P_w57 & 
    P_w60 & P_w61 & P_w62 & P_w63 & P_w64 & P_w65 & P_w66 & P_w67 & 
    P_w70 & P_w71 & P_w72 & P_w73 & P_w74 & P_w75 & P_w76 & P_w77 & 
    P_w80 & P_w81 & P_w82 & P_w83 & P_w84 & P_w85 & P_w86 & P_w87 & 
    P_w90 & P_w91 & P_w92 & P_w93 & P_w94 & P_w95 & P_w96 & P_w97 & 
    P_wa0 & P_wa1 & P_wa2 & P_wa3 & P_wa4 & P_wa5 & P_wa6 & P_wa7 & 
    P_wb0 & P_wb1 & P_wb2 & P_wb3 & P_wb4 & P_wb5 & P_wb6 & P_wb7 & 
    P_wc0 & P_wc1 & P_wc2 & P_wc3 & P_wc4 & P_wc5 & P_wc6 & P_wc7 & H).
  substs.
  unfold right in *.
  unfold left in *.
  unfold fench in *.
  unfold replace in *.
  inverts H0.
  simpl. auto.
Qed.



Lemma left_cwp:
  forall R R' F F',
  f_context F ->
  left_win 1 (R,F) = (R',F') ->
  R'#cwp = post_cwp 1 R.
Proof.
  intros.
  unfold left_win in *.
  asserts_rewrite ((Z.to_nat 1) = 1%nat) in *. compute. auto.
  unfold left_iter in *.
  unfolds in H.
  destruct H as (
    P_w00 & P_w01 & P_w02 & P_w03 & P_w04 & P_w05 & P_w06 & P_w07 &
    P_w10 & P_w11 & P_w12 & P_w13 & P_w14 & P_w15 & P_w16 & P_w17 &
    P_w20 & P_w21 & P_w22 & P_w23 & P_w24 & P_w25 & P_w26 & P_w27 &
    P_w30 & P_w31 & P_w32 & P_w33 & P_w34 & P_w35 & P_w36 & P_w37 & 
    P_w40 & P_w41 & P_w42 & P_w43 & P_w44 & P_w45 & P_w46 & P_w47 & 
    P_w50 & P_w51 & P_w52 & P_w53 & P_w54 & P_w55 & P_w56 & P_w57 & 
    P_w60 & P_w61 & P_w62 & P_w63 & P_w64 & P_w65 & P_w66 & P_w67 & 
    P_w70 & P_w71 & P_w72 & P_w73 & P_w74 & P_w75 & P_w76 & P_w77 & 
    P_w80 & P_w81 & P_w82 & P_w83 & P_w84 & P_w85 & P_w86 & P_w87 & 
    P_w90 & P_w91 & P_w92 & P_w93 & P_w94 & P_w95 & P_w96 & P_w97 & 
    P_wa0 & P_wa1 & P_wa2 & P_wa3 & P_wa4 & P_wa5 & P_wa6 & P_wa7 & 
    P_wb0 & P_wb1 & P_wb2 & P_wb3 & P_wb4 & P_wb5 & P_wb6 & P_wb7 & 
    P_wc0 & P_wc1 & P_wc2 & P_wc3 & P_wc4 & P_wc5 & P_wc6 & P_wc7 & H).
  substs.
  unfold left in *.
  unfold fench in *.
  unfold replace in *.
  inverts H0.
  simpl. auto.
Qed.


Lemma left_then_right2 :
  forall R F R' F' R'' F'',
      0 <= Int.unsigned (R#cwp) <= Int.unsigned(Asm.N)-1 ->
      f_context F ->
      left_win 1 (R,F) = (R',F') ->
      right_win 1 (R',F') = (R'',F'') ->
      R#cwp = R''#cwp.
Proof.
  intros.

  assert (f_context F' /\ R'#cwp = post_cwp 1 R). {
  unfold left_win in *.
  asserts_rewrite ((Z.to_nat 1) = 1%nat) in *. compute. auto.
  unfold left_iter in *.
  destruct H0 as (
    P_w00 & P_w01 & P_w02 & P_w03 & P_w04 & P_w05 & P_w06 & P_w07 &
    P_w10 & P_w11 & P_w12 & P_w13 & P_w14 & P_w15 & P_w16 & P_w17 &
    P_w20 & P_w21 & P_w22 & P_w23 & P_w24 & P_w25 & P_w26 & P_w27 &
    P_w30 & P_w31 & P_w32 & P_w33 & P_w34 & P_w35 & P_w36 & P_w37 & 
    P_w40 & P_w41 & P_w42 & P_w43 & P_w44 & P_w45 & P_w46 & P_w47 & 
    P_w50 & P_w51 & P_w52 & P_w53 & P_w54 & P_w55 & P_w56 & P_w57 & 
    P_w60 & P_w61 & P_w62 & P_w63 & P_w64 & P_w65 & P_w66 & P_w67 & 
    P_w70 & P_w71 & P_w72 & P_w73 & P_w74 & P_w75 & P_w76 & P_w77 & 
    P_w80 & P_w81 & P_w82 & P_w83 & P_w84 & P_w85 & P_w86 & P_w87 & 
    P_w90 & P_w91 & P_w92 & P_w93 & P_w94 & P_w95 & P_w96 & P_w97 & 
    P_wa0 & P_wa1 & P_wa2 & P_wa3 & P_wa4 & P_wa5 & P_wa6 & P_wa7 & 
    P_wb0 & P_wb1 & P_wb2 & P_wb3 & P_wb4 & P_wb5 & P_wb6 & P_wb7 & 
    P_wc0 & P_wc1 & P_wc2 & P_wc3 & P_wc4 & P_wc5 & P_wc6 & P_wc7 & H0).
  substs.
  unfold left in *.
  unfold fench in *.
  unfold replace in *.

  split.

  inverts H1.
  unfolds.
  exists P_w20 P_w21 P_w22 P_w23 P_w24 P_w25.
  exists P_w26 P_w27 P_w30 P_w31 P_w32 P_w33.
  exists P_w34 P_w35 P_w36 P_w37 P_w40 P_w41.
  exists P_w42 P_w43 P_w44 P_w45 P_w46 P_w47.
  exists P_w50 P_w51 P_w52 P_w53 P_w54 P_w55.
  exists P_w56 P_w57 P_w60 P_w61 P_w62 P_w63.
  exists P_w64 P_w65 P_w66 P_w67 P_w70 P_w71.
  exists P_w72 P_w73 P_w74 P_w75 P_w76 P_w77.
  exists P_w80 P_w81 P_w82 P_w83 P_w84 P_w85.
  exists P_w86 P_w87 P_w90 P_w91 P_w92 P_w93.
  exists P_w94 P_w95 P_w96 P_w97 P_wa0 P_wa1.
  exists P_wa2 P_wa3 P_wa4 P_wa5 P_wa6 P_wa7.
  exists P_wb0 P_wb1 P_wb2 P_wb3 P_wb4 P_wb5.
  exists P_wb6 P_wb7 P_wc0 P_wc1 P_wc2 P_wc3.
  exists P_wc4 P_wc5 P_wc6 P_wc7 (R r8) (R r9).
  exists (R r10) (R r11) (R r12) (R r13) (R r14) (R r15).
  exists (R r16) (R r17) (R r18) (R r19) (R r20) (R r21).
  exists (R r22) (R r23). auto.

  inverts H1. simpl. auto.
  }
  clear H0 H1.


  destruct H3 as (H0 & G).
  assert (R''#cwp = pre_cwp 1 R'). {
  unfold right_win in *.
  asserts_rewrite ((Z.to_nat 1) = 1%nat) in *. compute. auto.
  unfold right_iter in *.
  destruct H0 as (
    P_w00 & P_w01 & P_w02 & P_w03 & P_w04 & P_w05 & P_w06 & P_w07 &
    P_w10 & P_w11 & P_w12 & P_w13 & P_w14 & P_w15 & P_w16 & P_w17 &
    P_w20 & P_w21 & P_w22 & P_w23 & P_w24 & P_w25 & P_w26 & P_w27 &
    P_w30 & P_w31 & P_w32 & P_w33 & P_w34 & P_w35 & P_w36 & P_w37 & 
    P_w40 & P_w41 & P_w42 & P_w43 & P_w44 & P_w45 & P_w46 & P_w47 & 
    P_w50 & P_w51 & P_w52 & P_w53 & P_w54 & P_w55 & P_w56 & P_w57 & 
    P_w60 & P_w61 & P_w62 & P_w63 & P_w64 & P_w65 & P_w66 & P_w67 & 
    P_w70 & P_w71 & P_w72 & P_w73 & P_w74 & P_w75 & P_w76 & P_w77 & 
    P_w80 & P_w81 & P_w82 & P_w83 & P_w84 & P_w85 & P_w86 & P_w87 & 
    P_w90 & P_w91 & P_w92 & P_w93 & P_w94 & P_w95 & P_w96 & P_w97 & 
    P_wa0 & P_wa1 & P_wa2 & P_wa3 & P_wa4 & P_wa5 & P_wa6 & P_wa7 & 
    P_wb0 & P_wb1 & P_wb2 & P_wb3 & P_wb4 & P_wb5 & P_wb6 & P_wb7 & 
    P_wc0 & P_wc1 & P_wc2 & P_wc3 & P_wc4 & P_wc5 & P_wc6 & P_wc7 & H0).
  substs.
  unfold right in *.
  unfold left in *.
  unfold fench in *.
  unfold replace in *.
  inverts H2.
  simpl. auto.
  }
  clear H0 H2.

  unfold post_cwp in G.
  unfold pre_cwp in H1.
  rewrite G in H1. clear G.
  unfold Asm.N in H1.

  remember (get_R cwp R) as c.
  remember (get_R cwp R'') as c'.
  remember (Int.unsigned c) as n.

  unfold Asm.N in H.
  asserts_rewrite (Int.unsigned $ 8 - 1 = 7) in H. {
    clear Heqc Heqn H H1.
    int auto.
  }

  assert (n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5
   \/ n = 6 \/ n = 7). {
    clear Heqc Heqn H1.
    int auto.
  }
  clear H Heqc Heqc'.

  destruct H0.
  {
    substs.
    int auto;
    rewrite H;
    simpl;
    int auto;
    int auto;
    mauto.
    compute.
    rewrite <- H.
    symmetry.
    apply Int.repr_unsigned.
  }
  destruct H.
  {
    substs.
    int auto;
    rewrite H;
    simpl;
    int auto;
    int auto;
    mauto.
    compute.
    rewrite <- H.
    symmetry.
    apply Int.repr_unsigned.
  }
  destruct H.
  {
    substs.
    int auto;
    rewrite H;
    simpl;
    int auto;
    int auto;
    mauto.
    compute.
    rewrite <- H.
    symmetry.
    apply Int.repr_unsigned.
  }
  destruct H.
  {
    substs.
    int auto;
    rewrite H;
    simpl;
    int auto;
    int auto;
    mauto.
    compute.
    rewrite <- H.
    symmetry.
    apply Int.repr_unsigned.
  }
  destruct H.
  {
    substs.
    int auto;
    rewrite H;
    simpl;
    int auto;
    int auto;
    mauto.
    compute.
    rewrite <- H.
    symmetry.
    apply Int.repr_unsigned.
  }
  destruct H.
  {
    substs.
    int auto;
    rewrite H;
    simpl;
    int auto;
    int auto;
    mauto.
    compute.
    rewrite <- H.
    symmetry.
    apply Int.repr_unsigned.
  }
  destruct H.
  {
    substs.
    int auto;
    rewrite H;
    simpl;
    int auto;
    int auto;
    mauto.
    compute.
    rewrite <- H.
    symmetry.
    apply Int.repr_unsigned.
  }
  {
    substs.
    int auto;
    rewrite H;
    simpl;
    int auto;
    int auto;
    mauto.
    compute.
    rewrite <- H.
    symmetry.
    apply Int.repr_unsigned.
  }
Qed.


Lemma left_then_right_R :
  forall R F R' F' R'' F'',
      0 <= Int.unsigned (R#cwp) <= Int.unsigned(Asm.N)-1 ->
      f_context F ->
      left_win 1 (R,F) = (R',F') ->
      right_win 1 (R',F') = (R'',F'') ->
      R = R''.
Proof.
  intros.
  apply functional_extensionality.
  intros.
  assert ({x = cwp} + {x <> cwp}). repeat decide equality.
  destruct H3.
  assert (get_R cwp R = get_R cwp R'').
  apply (left_then_right2 R F R' F' R'' F''); iauto.
  substs. iauto.

  apply (left_then_right1 x R F R' F' R'' F''); iauto.
Qed.


Lemma left_then_right_F :
  forall R F R' F' R'' F'',
      f_context F ->
      left_win 1 (R,F) = (R',F') ->
      right_win 1 (R',F') = (R'',F'') ->
      F = F''.
Proof.
  intros.
  rewrite <- H0 in H1.
  clear H0.
  unfold right_win in H1.
  unfold left_win in H1.
  asserts_rewrite ((Z.to_nat 1) = 1%nat) in H1. compute. auto.
  unfold left_iter in H1.
  unfold right_iter in H1.
  unfolds in H.
  destruct H as (
    P_w00 & P_w01 & P_w02 & P_w03 & P_w04 & P_w05 & P_w06 & P_w07 &
    P_w10 & P_w11 & P_w12 & P_w13 & P_w14 & P_w15 & P_w16 & P_w17 &
    P_w20 & P_w21 & P_w22 & P_w23 & P_w24 & P_w25 & P_w26 & P_w27 &
    P_w30 & P_w31 & P_w32 & P_w33 & P_w34 & P_w35 & P_w36 & P_w37 & 
    P_w40 & P_w41 & P_w42 & P_w43 & P_w44 & P_w45 & P_w46 & P_w47 & 
    P_w50 & P_w51 & P_w52 & P_w53 & P_w54 & P_w55 & P_w56 & P_w57 & 
    P_w60 & P_w61 & P_w62 & P_w63 & P_w64 & P_w65 & P_w66 & P_w67 & 
    P_w70 & P_w71 & P_w72 & P_w73 & P_w74 & P_w75 & P_w76 & P_w77 & 
    P_w80 & P_w81 & P_w82 & P_w83 & P_w84 & P_w85 & P_w86 & P_w87 & 
    P_w90 & P_w91 & P_w92 & P_w93 & P_w94 & P_w95 & P_w96 & P_w97 & 
    P_wa0 & P_wa1 & P_wa2 & P_wa3 & P_wa4 & P_wa5 & P_wa6 & P_wa7 & 
    P_wb0 & P_wb1 & P_wb2 & P_wb3 & P_wb4 & P_wb5 & P_wb6 & P_wb7 & 
    P_wc0 & P_wc1 & P_wc2 & P_wc3 & P_wc4 & P_wc5 & P_wc6 & P_wc7 & H).
  substs.
  unfold left in *.
  unfold fench in *.
  unfold replace in *.
  inverts H1.
  simpl. auto.
Qed.


Lemma right_stack_p :
  forall R R' F F',
      f_context F ->
      right_win 1 (R,F) = (R',F') ->
      R'#r30 = R#r14.
Proof.
  intros.
  unfolds in H.
  destruct H as (
    P_w00 & P_w01 & P_w02 & P_w03 & P_w04 & P_w05 & P_w06 & P_w07 &
    P_w10 & P_w11 & P_w12 & P_w13 & P_w14 & P_w15 & P_w16 & P_w17 &
    P_w20 & P_w21 & P_w22 & P_w23 & P_w24 & P_w25 & P_w26 & P_w27 &
    P_w30 & P_w31 & P_w32 & P_w33 & P_w34 & P_w35 & P_w36 & P_w37 & 
    P_w40 & P_w41 & P_w42 & P_w43 & P_w44 & P_w45 & P_w46 & P_w47 & 
    P_w50 & P_w51 & P_w52 & P_w53 & P_w54 & P_w55 & P_w56 & P_w57 & 
    P_w60 & P_w61 & P_w62 & P_w63 & P_w64 & P_w65 & P_w66 & P_w67 & 
    P_w70 & P_w71 & P_w72 & P_w73 & P_w74 & P_w75 & P_w76 & P_w77 & 
    P_w80 & P_w81 & P_w82 & P_w83 & P_w84 & P_w85 & P_w86 & P_w87 & 
    P_w90 & P_w91 & P_w92 & P_w93 & P_w94 & P_w95 & P_w96 & P_w97 & 
    P_wa0 & P_wa1 & P_wa2 & P_wa3 & P_wa4 & P_wa5 & P_wa6 & P_wa7 & 
    P_wb0 & P_wb1 & P_wb2 & P_wb3 & P_wb4 & P_wb5 & P_wb6 & P_wb7 & 
    P_wc0 & P_wc1 & P_wc2 & P_wc3 & P_wc4 & P_wc5 & P_wc6 & P_wc7 & H).
  substs.
  unfold right_win in *.
  asserts_rewrite ((Z.to_nat 1) = 1%nat) in *. compute. auto.
  unfold right_iter in *.
  unfold right in *.
  unfold left in *.
  simpl in H0.
  inverts H0.
  simpl. auto.
Qed.


Lemma hold_context:
  forall R R' F F',
    f_context F->
    right_win 1 (R,F) = (R',F') ->
    f_context F'.
Proof.
  intros.
  unfold right_win in *.
  asserts_rewrite ((Z.to_nat 1) = 1%nat) in *. compute. auto.
  unfold right_iter in *.
  unfolds in H.
  destruct H as (
    P_w00 & P_w01 & P_w02 & P_w03 & P_w04 & P_w05 & P_w06 & P_w07 &
    P_w10 & P_w11 & P_w12 & P_w13 & P_w14 & P_w15 & P_w16 & P_w17 &
    P_w20 & P_w21 & P_w22 & P_w23 & P_w24 & P_w25 & P_w26 & P_w27 &
    P_w30 & P_w31 & P_w32 & P_w33 & P_w34 & P_w35 & P_w36 & P_w37 & 
    P_w40 & P_w41 & P_w42 & P_w43 & P_w44 & P_w45 & P_w46 & P_w47 & 
    P_w50 & P_w51 & P_w52 & P_w53 & P_w54 & P_w55 & P_w56 & P_w57 & 
    P_w60 & P_w61 & P_w62 & P_w63 & P_w64 & P_w65 & P_w66 & P_w67 & 
    P_w70 & P_w71 & P_w72 & P_w73 & P_w74 & P_w75 & P_w76 & P_w77 & 
    P_w80 & P_w81 & P_w82 & P_w83 & P_w84 & P_w85 & P_w86 & P_w87 & 
    P_w90 & P_w91 & P_w92 & P_w93 & P_w94 & P_w95 & P_w96 & P_w97 & 
    P_wa0 & P_wa1 & P_wa2 & P_wa3 & P_wa4 & P_wa5 & P_wa6 & P_wa7 & 
    P_wb0 & P_wb1 & P_wb2 & P_wb3 & P_wb4 & P_wb5 & P_wb6 & P_wb7 & 
    P_wc0 & P_wc1 & P_wc2 & P_wc3 & P_wc4 & P_wc5 & P_wc6 & P_wc7 & H).
  substs.
  unfold right in *.
  unfold left in *.
  unfold fench in *.
  unfold replace in *.

  inverts H0.
  unfolds.
  jauto.
Qed.

(*
  hold in local when save -restore :
*)
Lemma right_then_left_il :
  forall (i:GenReg) R F R' F' R'' F'' R''',
      f_context F ->
      right_win 1 (R,F) = (R',F') ->
      left_win 1 (R'',F') = (R''',F'') ->
      i = r16 \/ i = r17 \/ i = r18 \/ i = r31 ->
      R''' i = R i.
Proof.
  intros.
  unfolds in H.
  destruct H as (
    P_w00 & P_w01 & P_w02 & P_w03 & P_w04 & P_w05 & P_w06 & P_w07 &
    P_w10 & P_w11 & P_w12 & P_w13 & P_w14 & P_w15 & P_w16 & P_w17 &
    P_w20 & P_w21 & P_w22 & P_w23 & P_w24 & P_w25 & P_w26 & P_w27 &
    P_w30 & P_w31 & P_w32 & P_w33 & P_w34 & P_w35 & P_w36 & P_w37 & 
    P_w40 & P_w41 & P_w42 & P_w43 & P_w44 & P_w45 & P_w46 & P_w47 & 
    P_w50 & P_w51 & P_w52 & P_w53 & P_w54 & P_w55 & P_w56 & P_w57 & 
    P_w60 & P_w61 & P_w62 & P_w63 & P_w64 & P_w65 & P_w66 & P_w67 & 
    P_w70 & P_w71 & P_w72 & P_w73 & P_w74 & P_w75 & P_w76 & P_w77 & 
    P_w80 & P_w81 & P_w82 & P_w83 & P_w84 & P_w85 & P_w86 & P_w87 & 
    P_w90 & P_w91 & P_w92 & P_w93 & P_w94 & P_w95 & P_w96 & P_w97 & 
    P_wa0 & P_wa1 & P_wa2 & P_wa3 & P_wa4 & P_wa5 & P_wa6 & P_wa7 & 
    P_wb0 & P_wb1 & P_wb2 & P_wb3 & P_wb4 & P_wb5 & P_wb6 & P_wb7 & 
    P_wc0 & P_wc1 & P_wc2 & P_wc3 & P_wc4 & P_wc5 & P_wc6 & P_wc7 & H).
  substs.
  unfold right_win in *.
  asserts_rewrite ((Z.to_nat 1) = 1%nat) in *. compute. auto.
  unfold right_iter in *.
  unfold right in *.
  unfold left in *.
  simpl in H0.
  inverts H0.
  unfold left_win in *.
  asserts_rewrite ((Z.to_nat 1) = 1%nat) in *. compute. auto.
  unfold left_iter in *.
  unfold left in *.
  simpl in H1.
  inverts H1.

  destruct H2. substs. simpl. auto.
  destruct H. substs. simpl. auto.
  destruct H. substs. simpl. auto.
  substs. simpl. auto.
Qed.

Lemma right_right_same :
  forall (i:GenReg) R1 R2 F R1' R2' F1 F2,
      f_context F ->
      right_win 1 (R1,F) = (R1',F1) ->
      right_win 1 (R2,F) = (R2',F2) ->
      i = r8 \/ i = r14 \/ i = r23 ->
      R1' i = R2' i.
Proof.
  intros.
  unfolds in H.
  destruct H as (
    P_w00 & P_w01 & P_w02 & P_w03 & P_w04 & P_w05 & P_w06 & P_w07 &
    P_w10 & P_w11 & P_w12 & P_w13 & P_w14 & P_w15 & P_w16 & P_w17 &
    P_w20 & P_w21 & P_w22 & P_w23 & P_w24 & P_w25 & P_w26 & P_w27 &
    P_w30 & P_w31 & P_w32 & P_w33 & P_w34 & P_w35 & P_w36 & P_w37 & 
    P_w40 & P_w41 & P_w42 & P_w43 & P_w44 & P_w45 & P_w46 & P_w47 & 
    P_w50 & P_w51 & P_w52 & P_w53 & P_w54 & P_w55 & P_w56 & P_w57 & 
    P_w60 & P_w61 & P_w62 & P_w63 & P_w64 & P_w65 & P_w66 & P_w67 & 
    P_w70 & P_w71 & P_w72 & P_w73 & P_w74 & P_w75 & P_w76 & P_w77 & 
    P_w80 & P_w81 & P_w82 & P_w83 & P_w84 & P_w85 & P_w86 & P_w87 & 
    P_w90 & P_w91 & P_w92 & P_w93 & P_w94 & P_w95 & P_w96 & P_w97 & 
    P_wa0 & P_wa1 & P_wa2 & P_wa3 & P_wa4 & P_wa5 & P_wa6 & P_wa7 & 
    P_wb0 & P_wb1 & P_wb2 & P_wb3 & P_wb4 & P_wb5 & P_wb6 & P_wb7 & 
    P_wc0 & P_wc1 & P_wc2 & P_wc3 & P_wc4 & P_wc5 & P_wc6 & P_wc7 & H).
  substs.
  unfold right_win in *.
  asserts_rewrite ((Z.to_nat 1) = 1%nat) in *. compute. auto.
  unfold right_iter in *.
  unfold right in *.
  unfold left in *.
  simpl in H0.
  inverts H0.
  simpl in H1.
  inverts H1.

  destruct H2. substs.
  compute. auto.

  destruct H. substs.
  compute. auto.

  substs.
  compute. auto.
Qed.



Lemma hold_context_left:
  forall R R' F F',
    f_context F->
    left_win 1 (R,F) = (R',F') ->
    f_context F'.
Proof.
  intros.
  unfold left_win in *.
  asserts_rewrite ((Z.to_nat 1) = 1%nat) in *. compute. auto.
  unfold left_iter in *.
  unfolds in H.
  destruct H as (
    P_w00 & P_w01 & P_w02 & P_w03 & P_w04 & P_w05 & P_w06 & P_w07 &
    P_w10 & P_w11 & P_w12 & P_w13 & P_w14 & P_w15 & P_w16 & P_w17 &
    P_w20 & P_w21 & P_w22 & P_w23 & P_w24 & P_w25 & P_w26 & P_w27 &
    P_w30 & P_w31 & P_w32 & P_w33 & P_w34 & P_w35 & P_w36 & P_w37 & 
    P_w40 & P_w41 & P_w42 & P_w43 & P_w44 & P_w45 & P_w46 & P_w47 & 
    P_w50 & P_w51 & P_w52 & P_w53 & P_w54 & P_w55 & P_w56 & P_w57 & 
    P_w60 & P_w61 & P_w62 & P_w63 & P_w64 & P_w65 & P_w66 & P_w67 & 
    P_w70 & P_w71 & P_w72 & P_w73 & P_w74 & P_w75 & P_w76 & P_w77 & 
    P_w80 & P_w81 & P_w82 & P_w83 & P_w84 & P_w85 & P_w86 & P_w87 & 
    P_w90 & P_w91 & P_w92 & P_w93 & P_w94 & P_w95 & P_w96 & P_w97 & 
    P_wa0 & P_wa1 & P_wa2 & P_wa3 & P_wa4 & P_wa5 & P_wa6 & P_wa7 & 
    P_wb0 & P_wb1 & P_wb2 & P_wb3 & P_wb4 & P_wb5 & P_wb6 & P_wb7 & 
    P_wc0 & P_wc1 & P_wc2 & P_wc3 & P_wc4 & P_wc5 & P_wc6 & P_wc7 & H).
  substs.
  unfold left in *.
  unfold fench in *.
  unfold replace in *.

  inverts H0.
  unfolds.
  jauto.
Qed.

