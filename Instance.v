Require Import Asm.
Require Import Coqlib.
Require Import Props.
Require Import LibTactics.
Import ListNotations.
Local Open Scope sparc_scope.
Require Import int_auto.
Require Import math_sol.
Require Import Integers.

(************************************************************************************************************************)
(* ₐₑₕᵢⱼₖₗₘₙₒₚᵣₛₜᵤᵥₓ *)

Notation " ri +ₐᵣ rj " := (Aro ri (Or rj))(at level 1) : asm_scope.
Notation " r  +ₐₙ n  " := (Aro r (Ow n))(at level 1) : asm_scope.
Notation " r 'ₐᵣ' " := (Ao (Or r))(at level 1) : asm_scope.
Notation " n 'ₐₙ' " := (Ao (Ow n))(at level 1) : asm_scope.

Notation " ri +ₜᵣ rj " := (Trr ri rj)(at level 1) : asm_scope.
Notation " r  +ₜₙ n  " := (Trw r n)(at level 1) : asm_scope.
Notation " r 'ₜᵣ' " := (Tr r)(at level 1) : asm_scope.
Notation " n 'ₜₙ' " := (Tw n)(at level 1) : asm_scope.

Notation " r 'ᵣ' " := (Or r)(at level 1) : asm_scope.
Notation " n 'ₙ' " := (Ow n)(at level 1) : asm_scope.


Notation "'g0'" := r0 (only parsing) : asm_scope.
Notation "'g1'" := r1 (only parsing) : asm_scope.
Notation "'g2'" := r2 (only parsing) : asm_scope.
Notation "'g3'" := r3 (only parsing) : asm_scope.
Notation "'g4'" := r4 (only parsing) : asm_scope.
Notation "'g5'" := r5 (only parsing) : asm_scope.
Notation "'g6'" := r6 (only parsing) : asm_scope.
Notation "'g7'" := r7 (only parsing) : asm_scope.
Notation "'o0'" := r8 (only parsing) : asm_scope.
Notation "'o1'" := r9 (only parsing) : asm_scope.
Notation "'o2'" := r10 (only parsing) : asm_scope.
Notation "'o3'" := r11 (only parsing) : asm_scope.
Notation "'o4'" := r12 (only parsing) : asm_scope.
Notation "'o5'" := r13 (only parsing) : asm_scope.
Notation "'o6'" := r14 (only parsing) : asm_scope.
Notation "'o7'" := r15 (only parsing) : asm_scope.
Notation "'l0'" := r16 (only parsing) : asm_scope.
Notation "'l1'" := r17 (only parsing) : asm_scope.
Notation "'l2'" := r18 (only parsing) : asm_scope.
Notation "'l3'" := r19 (only parsing) : asm_scope.
Notation "'l4'" := r20 (only parsing) : asm_scope.
Notation "'l5'" := r21 (only parsing) : asm_scope.
Notation "'l6'" := r22 (only parsing) : asm_scope.
Notation "'l7'" := r23 (only parsing) : asm_scope.
Notation "'i0'" := r24 (only parsing) : asm_scope.
Notation "'i1'" := r25 (only parsing) : asm_scope.
Notation "'i2'" := r26 (only parsing) : asm_scope.
Notation "'i3'" := r27 (only parsing) : asm_scope.
Notation "'i4'" := r28 (only parsing) : asm_scope.
Notation "'i5'" := r29 (only parsing) : asm_scope.
Notation "'i6'" := r30 (only parsing) : asm_scope.
Notation "'i7'" := r31 (only parsing) : asm_scope.
Notation "'fp'" := r30 (only parsing) : asm_scope.
Notation "'sp'" := r14 (only parsing) : asm_scope.


(************************************************************************************************************************)

Local Open Scope asm_scope.
Local Open Scope sparc_scope.

Definition Cond := World -> Prop.

Definition Function : Type := list SparcIns.

Definition overflow_handler := [
  rd wim l3;
  sll l3 (Asm.N-ᵢ($1))ₙ l4;
  srl l3 ($1)ₙ l3;
  or l3 l4 ᵣ l3;
  and l3 ($255)ₙ l3;
  wr g0 g0 ᵣ wim;
  save g0 g0 ᵣ g0;
  st l0 sp ₐᵣ;
  restore g0 g0 ᵣ g0;
  wr g0 l3 ᵣ wim;
  jmpl l1 ₐᵣ g0;
  rett l2 ₐᵣ
].

Definition underflow_handler := [
  rd wim l3;
  srl l3 (Asm.N-ᵢ($1))ₙ l4;
  sll l3 ($1)ₙ l3;
  or l3 l4 ᵣ l3;
  wr g0 l3 ᵣ wim;
  jmpl l1 ₐᵣ g0;
  rett l2 ₐᵣ
].

Parameter
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
    P_wc0 P_wc1 P_wc2 P_wc3 P_wc4 P_wc5 P_wc6 P_wc7: Word.

Parameter
    P_r00 P_r01 P_r02 P_r03 P_r04 P_r05 P_r06 P_r07
    P_r08 P_r09 P_r10 P_r11 P_r12 P_r13 P_r14 P_r15
    P_r16 P_r17 P_r18 P_r19 P_r20 P_r21 P_r22 P_r23
    P_r24 P_r25 P_r26 P_r27 P_r28 P_r29 P_r30 P_r31: Word.


Definition handler_context (R: RegFile) :=
  0 <= Int.unsigned (R#cwp) <= 7 /\ not_annuled_R R /\ trap_disabled_R R /\
  no_trap_R R /\  sup_mode_R R /\ word_aligned_R R#l1 /\ word_aligned_R R#l2.

Definition single_mask : Word -> Word -> Prop :=
  fun cwp wim =>
    ($1) <<ᵢ cwp = wim.

Definition align_context(O: RState) :=
  let (R',F') := left_win 1 O in word_aligned_R R'#sp.

Definition normal_cursor(O: RState) :=
  let (R,_) := O in R#npc = R#pc +ᵢ ($4).

Definition normal_step(S S': State) :=
  let '(_,Q,_) := S in
  let '(_,Q',_) := S' in
  let (R,_) := Q in 
  let (R',_) := Q' in 
  R'#pc = R#pc +ᵢ ($4).

Fixpoint set_function (w: Address) (F: Function)(C: CodeHeap)  : Prop :=
  match F with
  | i::F' => C w = Some i /\ set_function (w +ᵢ ($4)) F' C 
  | nil => True
  end.


Definition f_context(F: FrameList) :=
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

Definition r_context(R: RegFile) :=
  R#r0 = P_r00 /\ R#r1 = P_r01 /\ R#r2 = P_r02 /\ R#r3 = P_r03 /\ 
  R#r4 = P_r04 /\ R#r5 = P_r05 /\ R#r6 = P_r06 /\ R#r7 = P_r07 /\ 
  R#r8 = P_r08 /\ R#r9 = P_r09 /\ R#r10 = P_r10 /\ R#r11 = P_r11 /\ 
  R#r12 = P_r12 /\ R#r13 = P_r13 /\ R#r14 = P_r14 /\ R#r15 = P_r15 /\ 
  R#r16 = P_r16 /\ R#r17 = P_r17 /\ R#r18 = P_r18 /\ R#r19 = P_r19 /\ 
  R#r20 = P_r20 /\ R#r21 = P_r21 /\ R#r22 = P_r22 /\ R#r23 = P_r23 /\ 
  R#r24 = P_r24 /\ R#r25 = P_r25 /\ R#r26 = P_r26 /\ R#r27 = P_r27 /\ 
  R#r28 = P_r28 /\ R#r29 = P_r29 /\ R#r30 = P_r30 /\ R#r31 = P_r31.
(*
Lemma left_equal :
  forall (i:GenReg) R1 R1' R2 R2' F F1' F2',
      f_context F ->
      left_win 1 (R1,F) = (R1',F1') ->
      left_win 1 (R2,F) = (R2',F2') ->
      i =  \/ i = g1 /\ i = g2 /\ i = g3 /\ 
      i = g4 \/ i = g5 /\ i = g6 /\ i = g7 /\
      i = i1 \/ i = i2 /\ i = i2 /\ i = i3 /\ 
      i = i4 \/ i = i5 /\ i = i6 /\ i = i7 ->
      R1'#i = R2'#i.
Proof.
  intros.
  unfolds in H.
  substs.
  unfold left_win in *.
  asserts_rewrite ((Z.to_nat 1) = 1%nat) in *. compute. auto.
  unfold left_iter in *.
  unfold left in *.
  simpl in H1.
  simpl in H0.
  inverts H0.
  inverts H1.

  destruct H2 as (b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7).

  destruct i.

  destruct i;
  try solve [false].
Qed.
  simpl; auto.
*)
Lemma left_then_right :
  forall (i:GenReg) R F R' F' R'' F'',
      f_context F ->
      left_win 1 (R,F) = (R',F') ->
      right_win 1 (R',F') = (R'',F'') ->
      R#i = R''#i.
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
  substs.
  unfold left in H1.
  unfold right in H1.
  unfold fench in H1.
  unfold replace in H1.
  simpl in H1.
  inverts H1.

  destruct i;
  simpl; auto.
Qed.

Definition parameter_context(O: RState) :=
  let (R,F) := O in
    r_context(R) /\ f_context(F).

Definition overflow_pre_cond : Cond :=
  fun W =>
    let (CP,S) := W in
    let (Cu,Cs) := CP in
    let '(MP,Q,_) := S in
    let (R,F) := Q in
    handler_context R /\ set_function (cursor_Q Q) overflow_handler Cs /\
    single_mask R#cwp R#wim /\ align_context Q /\ normal_cursor Q /\ parameter_context Q.

Definition overflow_post_cond : Cond :=
  fun W =>
    let (CP,S) := W in
    let (Cu,Cs) := CP in
    let '(MP,Q,_) := S in
    let (R,F) := Q in
    single_mask (pre_cwp 2 R) R#wim.

Lemma ModeDeq:
  forall O,
    sup_mode_Q O ->
    usr_mode_Q O ->
    False.
Proof.
  intros.
  unfolds in H.
  unfolds in H0.
  destruct O.
  unfolds in H.
  unfolds in H0.
  rewrite H in H0.
  inverts H0.
Qed.

Lemma AnnulDeq:
  forall R,
    annuled_R R ->
    not_annuled_R R ->
    False.
Proof.
  intros.
  unfolds in H.
  unfolds in H0.
  rewrite H in H0.
  inverts H0.
Qed.


Lemma Mask_When_Shiftl:
  forall cwp wim,
    0 <= Int.unsigned cwp <= 7 ->
    single_mask cwp wim ->
    single_mask cwp +ᵢ ($ 7) wim <<ᵢ ($ 7).
Proof.
  intros.
  destruct H.
  unfolds in H0.
  unfolds.
  rewrite <- H0.
  unfolds.
  clear H0.

  int auto;
  remember (Int.unsigned cwp) as n;
  clear Heqn;

  assert (n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5
   \/ n = 6 \/ n = 7); mauto;
  clear H H1;
  destruct H0; substs; mauto.
Qed.

Lemma Mask_When_Shiftr:
  forall cwp wim,
    0 <= Int.unsigned cwp <= 7 ->
    single_mask cwp wim ->
    (1 <= Int.unsigned cwp <= 7 /\ single_mask cwp -ᵢ ($ 1) wim >>ᵢ ($ 1)) \/ (Int.unsigned cwp = 0 /\ wim >>ᵢ ($ 1) = ($0)).
Proof.
  intros.
  destruct H.
  unfolds in H0.
  rewrite <- H0.
  clear H0.
  unfold single_mask.

  remember (Int.unsigned cwp) as n;

  assert (n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5
   \/ n = 6 \/ n = 7). mauto.

  destruct H0. right. split; auto.
  int auto. rewrite <- Heqn.
  rewrite H0. int auto.

  clear H H1.

  destruct H0; left; split; int auto;
  rewrite <- Heqn.
  rewrite H.
  int auto.

  destruct H.
  rewrite H.
  int auto.

  destruct H.
  rewrite H.
  int auto.

  destruct H.
  rewrite H.
  int auto.
    destruct H.
  rewrite H.
  int auto.
    destruct H.
  rewrite H.
  int auto.

  rewrite H.
  int auto.
Qed.

Lemma align_plus4:
  forall w,
  word_aligned_R w ->
  word_aligned_R w +ᵢ ($4).
Proof.
  intros.
  unfold word_aligned_R in *.
  unfold word_aligned in *.
  unfold get_range in *.
Admitted.

Lemma Win_Xor:
forall cwp x y,
    0 <= Int.unsigned cwp <= 7 ->
    single_mask (cwp+ᵢ ($7)) y ->
     (1 <= Int.unsigned cwp <= 7 /\ single_mask(cwp -ᵢ ($1)) x) \/
     (Int.unsigned cwp = 0 /\ x = ($0)) ->
    single_mask ((cwp +ᵢ Asm.N -ᵢ ($1)) modu Asm.N) (x |ᵢ  y)&ᵢ($255).
Proof.
  intros.
  unfold single_mask in H0.
  unfold single_mask in H1.
  unfold single_mask.
  unfold Asm.N.
  remember (Int.unsigned cwp) as n.

  assert (n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5
   \/ n = 6 \/ n = 7). mauto.
  clear H.
  destruct H2.
  destruct H1.
  {
    destruct H1.
    false.
    omega.
  }
  {
    destruct H1.
    clear H1.
    substs.
    int auto;
    rewrite H.
    unfold Z.shiftl.
    simpl. auto.
    mauto.
    simpl.
    assert (7 mod 8 = 7).
    compute. auto.
    omega.
    unfold Z.shiftl.
    int auto.
    simpl. omega.
    simpl. omega.
    int auto;
    unfold Z.shiftl;
    simpl; try omega.
    int auto;
    simpl; try omega.
  }

  destruct H.
  destruct H1.
  destruct H1.
  clear H1.
  substs.
  int auto;
  rewrite H.
    unfold Z.shiftl.
    simpl. auto.
    mauto.
    simpl.
    assert (8 mod 8 = 0).
    compute. auto.
    omega.
    unfold Z.shiftl.
    int auto; simpl; omega.
    try unfold Z.shiftl;
    int auto; simpl; omega.
    int auto; simpl. omega.
    omega.
    try unfold Z.shiftl;
    int auto; simpl; omega.
    try unfold Z.shiftl;
    int auto; simpl; omega.
  false. rewrite H in H1. inverts H1. inverts H2.

  destruct H.
  destruct H1.
  destruct H1.
  clear H1.
  substs.
  int auto;
  rewrite H.
    unfold Z.shiftl.
    simpl. auto.
    mauto.
    simpl.
    assert (9 mod 8 = 1).
    compute. auto.
    omega.
    unfold Z.shiftl.
    int auto; simpl; omega.
    try unfold Z.shiftl;
    int auto; simpl; omega.
    int auto; simpl. omega.
    omega.
    try unfold Z.shiftl;
    int auto; simpl; omega.
    try unfold Z.shiftl;
    int auto; simpl; omega.
  false. rewrite H in H1. inverts H1. inverts H2.

  destruct H.
  destruct H1.
  destruct H1.
  clear H1.
  substs.
  int auto;
  rewrite H.
    unfold Z.shiftl.
    simpl. auto.
    mauto.
    simpl.
    assert (10 mod 8 = 2).
    compute. auto.
    omega.
    unfold Z.shiftl.
    int auto; simpl; omega.
    try unfold Z.shiftl;
    int auto; simpl; omega.
    int auto; simpl. omega.
    omega.
    try unfold Z.shiftl;
    int auto; simpl; omega.
    try unfold Z.shiftl;
    int auto; simpl; omega.
  false. rewrite H in H1. inverts H1. inverts H2.


  destruct H.
  destruct H1.
  destruct H1.
  clear H1.
  substs.
  int auto;
  rewrite H.
    unfold Z.shiftl.
    simpl. auto.
    mauto.
    simpl.
    assert (11 mod 8 = 3).
    compute. auto.
    omega.
    unfold Z.shiftl.
    int auto; simpl; omega.
    try unfold Z.shiftl;
    int auto; simpl; omega.
    int auto; simpl. omega.
    omega.
    try unfold Z.shiftl;
    int auto; simpl; omega.
    try unfold Z.shiftl;
    int auto; simpl; omega.
  false. rewrite H in H1. inverts H1. inverts H2.


  destruct H.
  destruct H1.
  destruct H1.
  clear H1.
  substs.
  int auto;
  rewrite H.
    unfold Z.shiftl.
    simpl. auto.
    mauto.
    simpl.
    assert (12 mod 8 = 4).
    compute. auto.
    omega.
    unfold Z.shiftl.
    int auto; simpl; omega.
    try unfold Z.shiftl;
    int auto; simpl; omega.
    int auto; simpl. omega.
    omega.
    try unfold Z.shiftl;
    int auto; simpl; omega.
    try unfold Z.shiftl;
    int auto; simpl; omega.
  false. rewrite H in H1. inverts H1. inverts H2.


  destruct H.
  destruct H1.
  destruct H1.
  clear H1.
  substs.
  int auto;
  rewrite H.
    unfold Z.shiftl.
    simpl. auto.
    mauto.
    simpl.
    assert (13 mod 8 = 5).
    compute. auto.
    omega.
    unfold Z.shiftl.
    int auto; simpl; omega.
    try unfold Z.shiftl;
    int auto; simpl; omega.
    int auto; simpl. omega.
    omega.
    try unfold Z.shiftl;
    int auto; simpl; omega.
    try unfold Z.shiftl;
    int auto; simpl; omega.
  false. rewrite H in H1. inverts H1. inverts H2.


  destruct H1.
  destruct H1.
  clear H1.
  substs.
  int auto;
  rewrite H.
    unfold Z.shiftl.
    simpl. auto.
    mauto.
    simpl.
    assert (14 mod 8 = 6).
    compute. auto.
    omega.
    unfold Z.shiftl.
    int auto; simpl; omega.
    try unfold Z.shiftl;
    int auto; simpl; omega.
    int auto; simpl. omega.
    omega.
    try unfold Z.shiftl;
    int auto; simpl; omega.
    try unfold Z.shiftl;
    int auto; simpl; omega.
  false. rewrite H in H1. inverts H1. inverts H2.
Qed.

(*

Theorem HandleOverflow:
  forall CP S,
    overflow_pre_cond (CP,S) ->
    exists S' E ,Q__ CP S E 8 S'/\
    overflow_post_cond (CP,S').
Proof.
  intros.
  unfolds in H.
  destruct CP as (Cu & Cs).
  destruct S as (MP & O).
  destruct MP as (Mu & Ms).
  destruct O as (R & F).
  destruct H as (IVR & FUNC & MASK & SP & CSR & PARAM).

  (* change sp_align in to f_align*)
  assert (word_aligned_R P_r30) as SP'.
  {
    clear FUNC MASK CSR IVR.
    unfolds in SP.
    unfolds in PARAM.
    remember (left_win 1 (R, F)) as O'.
    destruct O' as (R' & F').
    unfolds in HeqO'.
    assert ((Z.to_nat 1) = 1%nat). compute. auto.
    rewrite H in HeqO'. clear H.
    unfold left_iter in HeqO'.
    remember (left F (fench R)) as K.
    destruct K as (K1 & K2).
    destruct PARAM as (PR & PF).
    unfolds in PR.
    assert (fench R =
       [[P_r08;P_r09;P_r10;P_r11;P_r12;P_r13;P_r14;P_r15];
        [P_r16;P_r17;P_r18;P_r19;P_r20;P_r21;P_r22;P_r23];
        [P_r24;P_r25;P_r26;P_r27;P_r28;P_r29;P_r30;P_r31]]). {
      unfold fench.
      asserts_rewrite(get_R r8 R = P_r08). iauto.
      asserts_rewrite(get_R r9 R = P_r09). iauto.
      asserts_rewrite(get_R r10 R = P_r10). iauto.
      asserts_rewrite(get_R r11 R = P_r11). iauto.
      asserts_rewrite(get_R r12 R = P_r12). iauto.
      asserts_rewrite(get_R r13 R = P_r13). iauto.
      asserts_rewrite(get_R r14 R = P_r14). iauto.
      asserts_rewrite(get_R r15 R = P_r15). iauto.
      asserts_rewrite(get_R r16 R = P_r16). iauto.
      asserts_rewrite(get_R r17 R = P_r17). iauto.
      asserts_rewrite(get_R r18 R = P_r18). iauto.
      asserts_rewrite(get_R r19 R = P_r19). iauto.
      asserts_rewrite(get_R r20 R = P_r20). iauto.
      asserts_rewrite(get_R r21 R = P_r21). iauto.
      asserts_rewrite(get_R r22 R = P_r22). iauto.
      asserts_rewrite(get_R r23 R = P_r23). iauto.
      asserts_rewrite(get_R r24 R = P_r24). iauto.
      asserts_rewrite(get_R r25 R = P_r25). iauto.
      asserts_rewrite(get_R r26 R = P_r26). iauto.
      asserts_rewrite(get_R r27 R = P_r27). iauto.
      asserts_rewrite(get_R r28 R = P_r28). iauto.
      asserts_rewrite(get_R r29 R = P_r29). iauto.
      asserts_rewrite(get_R r30 R = P_r30). iauto.
      asserts_rewrite(get_R r31 R = P_r31). iauto.
      auto.
    }
    clear PR.

    assert (K2 =
    [[P_r24;P_r25;P_r26;P_r27;P_r28;P_r29;P_r30;P_r31];
     [P_w00;P_w01;P_w02;P_w03;P_w04;P_w05;P_w06;P_w07];
     [P_w10;P_w11;P_w12;P_w13;P_w14;P_w15;P_w16;P_w17]]). {
      rewrite H in HeqK.
      unfolds in PF.
      rewrite PF in HeqK.
      unfolds in HeqK.
      inverts HeqK. auto.
    }
    clear H.

    assert ((replace K2 R)#r14 = P_r30). {
      unfolds.
      rewrite H0.
      unfolds.
      compute.
      auto.
    }
    assert (((replace K2 R) # cwp <- (post_cwp 1 R) #r14 = (replace K2 R)#r14)). {
      simpl. apply RegMap.gso. unfolds. intros. inverts H1.
    }
    assert (R'#r14 = P_r30). {
      inverts HeqO'.
      simpl in H1.
      simpl. auto.
    }
    rewrite H2 in SP.
    auto.
    }
    clear SP. rename SP' into SP.


(* step 1 *)

  (* to P__ *)
  assert
  (exists Ms' O', P__ (Cu,Cs) ((Mu,Ms),(R,F)) ((Mu,Ms'),O')) as H. {
    apply (Exists_P_Sup Cu Cs Mu Ms (rd wim r19) (R,F));
    auto; try apply IVR; try apply FUNC.
  }
  destruct H as (Ms' & O' & P__).
  destruct O' as (R' & F').

  (* small changes in one step *)
  assert (R#npc = R'#pc /\ R'#npc = R#npc +ᵢ ($4) /\ 
          R#cwp = R'#cwp /\ R#annul = R'#annul /\ R#et = R'#et /\ R#trap = R'#trap /\ R#s = R'#s /\
          R#wim = R'#r19 /\ R#r17 = R'#r17 /\ R#r18 = R'#r18 /\ F = F'). {
    inverts P__; auto.
    (* usr_mode *) {
    false. apply (ModeDeq (R,F)); auto.
    apply IVR.
    }
    (* sup_mode *) {
    inverts H8; auto.
    assert (Cs (get_R pc R) = Some (rd wim r19)). {
    apply FUNC.
    }
    rewrite H10 in H. clear H10.
    inverts H.
    inverts H11; try inverts H8; auto.
    {
      inverts H4;
      try inverts H6;
      try inverts H8;
      try inverts H2;
      repeat (split; auto).
    }
    (* unexpected_trap? no! *){
    unfolds in H2.
    unfold trap_type in H2.
    assert (usr_mode R = false). apply IVR.
    rewrite H in H2. inverts H2.
    }
    (* annul? no !*){
    false.
    apply (AnnulDeq R).
    apply H2. apply IVR.
    }
    }
  }

  assert (handler_context R') as IVR'. {
    unfolds.
    splits; try unfolds; try unfolds;
    try asserts_rewrite ((get_R cwp R') = (get_R cwp R));
    try asserts_rewrite ((get_R annul R') = (get_R annul R)); 
    try asserts_rewrite ((get_R et R') = (get_R et R));
    try asserts_rewrite ((get_R trap R') = (get_R trap R));
    try asserts_rewrite ((get_R s R') = (get_R s R));
    try asserts_rewrite ((get_R r17 R') = (get_R r17 R));
    try asserts_rewrite ((get_R r18 R') = (get_R r18 R));
    iauto; apply IVR.
  }

  assert (single_mask (get_R cwp R') (get_R r19 R') ) as MASK'. {
    asserts_rewrite ((get_R cwp R') = (get_R cwp R)). iauto.
    asserts_rewrite ((get_R r19 R') = (get_R wim R)). iauto.
    apply MASK.
  }

  assert (R'#pc = R#pc +ᵢ ($4) /\ normal_cursor (R',F')) as CSR'. {
    splits.
      asserts_rewrite (get_R pc R' = get_R npc R). iauto. apply CSR.
      unfolds.
        asserts_rewrite (get_R npc R' = (get_R npc R) +ᵢ ($ 4)). iauto.
        asserts_rewrite (get_R pc R'  = get_R npc R). iauto.
        auto.
  }

  assert (f_context F') as PARAM'. {
    asserts_rewrite (F' = F). iauto.
    apply PARAM.
  }

  assert (Q__ (Cu, Cs) (Mu, Ms, (R, F)) [None] 1 (Mu, Ms', (R', F'))) as GOAL'. {
    assert (Q__ (Cu, Cs) (Mu, Ms, (R, F)) nil 0 (Mu, Ms, (R, F))).
    apply Zero.
    apply (No_Event (Cu,Cs) nil 0 (Mu, Ms, (R, F)) (Mu, Ms', (R', F')) (Mu, Ms, (R, F))); auto.
  }
  rename Ms into Ms_.
  rename R into R_.
  rename F into F_.
  rename Ms' into Ms.
  rename R' into R.
  rename F' into F.
  clear H P__ IVR MASK CSR PARAM.
  rename IVR' into IVR.
  rename MASK' into MASK.
  rename CSR' into CSR.
  rename PARAM' into PARAM.
  rename GOAL' into GOAL.


(* step 2 *)

  (* to P__ *)
  assert
  (exists Ms' O', P__ (Cu,Cs) ((Mu,Ms),(R,F)) ((Mu,Ms'),O')) as H. {
    apply (Exists_P_Sup Cu Cs Mu Ms (sll l3 (Asm.N-ᵢ($1))ₙ l4) (R,F));
    try apply IVR; auto.
    asserts_rewrite (cursor_O (R, F) = (cursor_O (R_, F_)) +ᵢ ($4)). iauto.
    apply FUNC.
  }

  destruct H as (Ms' & O' & P__).
  destruct O' as (R' & F').

  (* small changes in one step *)
  assert (R#npc = R'#pc /\ R'#npc = R#npc +ᵢ ($4) /\
          R#cwp = R'#cwp /\ R#annul = R'#annul /\ R#et = R'#et /\ R#trap = R'#trap /\ R#s = R'#s /\
          R#r19 = R'#r19 /\ R'#r20 = R'#r19 <<ᵢ ($7) /\ R#r17 = R'#r17 /\ R#r18 = R'#r18 /\ F = F'). {

    inverts P__; auto.
    (* usr_mode *) {
    false. apply (ModeDeq (R,F)); auto.
    apply IVR.
    }
    (* sup_mode *) {
    inverts H8; auto.
    assert (Cs (get_R pc R) = Some (sll r19 (Asm.N -ᵢ ($ 1)) ₙ r20)). {
      asserts_rewrite (get_R pc R = (get_R pc R_) +ᵢ ($ 4)). iauto.
      apply FUNC.
    }
    rewrite H10 in H. clear H10.
    inverts H.
    inverts H11; try inverts H8; auto.
    {
      inverts H4;
      try inverts H6;
      try inverts H8;
      try inverts H2;
      repeat (split; auto).

      unfold eval_OpExp in H9.
      destruct (($ (-4096)) <=ᵢ (Asm.N -ᵢ ($ 1)) && (Asm.N -ᵢ ($ 1)) <=ᵢ ($ 4095));
      try inverts H9.
      auto.
    }
    (* unexpected_trap? no! *){
    unfolds in H2.
    unfold trap_type in H2.
    assert (usr_mode R = false). apply IVR.
    inverts H2.
    }
    (* annul? no !*){
    false.
    apply (AnnulDeq R).
    apply H2. apply IVR.
    }
    }
  }

  assert (handler_context R') as IVR'. {
    unfolds.
    splits; try unfolds; try unfolds;
    try asserts_rewrite ((get_R cwp R') = (get_R cwp R));
    try asserts_rewrite ((get_R annul R') = (get_R annul R)); 
    try asserts_rewrite ((get_R et R') = (get_R et R));
    try asserts_rewrite ((get_R trap R') = (get_R trap R));
    try asserts_rewrite ((get_R s R') = (get_R s R));
    try asserts_rewrite ((get_R r17 R') = (get_R r17 R));
    try asserts_rewrite ((get_R r18 R') = (get_R r18 R));
    iauto; apply IVR.
  }

  assert (single_mask R'#cwp+ᵢ($7) R'#r20 /\ single_mask R'#cwp R'#r19) as MASK'. {
    split.
    asserts_rewrite (get_R r20 R' = (get_R r19 R') <<ᵢ ($ 7)). iauto.
    apply (Mask_When_Shiftl (get_R cwp R') (get_R r19 R')).
    asserts_rewrite (get_R cwp R' = get_R cwp R). iauto. apply IVR.
      asserts_rewrite (get_R cwp R' = get_R cwp R); iauto;
      asserts_rewrite (get_R r19 R' = get_R r19 R); iauto; apply MASK.
      asserts_rewrite (get_R cwp R' = get_R cwp R); iauto;
      asserts_rewrite (get_R r19 R' = get_R r19 R); iauto; apply MASK.
  }

  assert (R'#pc = R_#pc +ᵢ ($4) +ᵢ ($4) /\ normal_cursor (R',F')) as CSR'. {
    splits. {
      asserts_rewrite (get_R pc R' = get_R npc R). iauto.
      asserts_rewrite (get_R npc R = (get_R pc R) +ᵢ ($ 4)). apply CSR.
      asserts_rewrite (get_R pc R = (get_R pc R_) +ᵢ ($ 4)). apply CSR.
      auto.
    }
    {
      unfolds.
        asserts_rewrite (get_R npc R' = (get_R npc R) +ᵢ ($ 4)). iauto.
        asserts_rewrite (get_R pc R'  = get_R npc R). iauto.
        auto.
    }
  }

  assert (f_context F') as PARAM'. {
    asserts_rewrite (F' = F). iauto.
    apply PARAM.
  }

  assert (Q__ (Cu, Cs) (Mu, Ms_, (R_, F_)) [None;None] 2 (Mu, Ms', (R', F'))) as GOAL'.
  {
    apply (No_Event (Cu,Cs) [None] 1 (Mu, Ms_, (R_, F_)) (Mu, Ms', (R', F')) (Mu, Ms, (R, F))); auto.
  }

  clear P__ IVR MASK CSR PARAM GOAL Ms R F H.
  rename Ms' into Ms.
  rename R' into R.
  rename F' into F.
  rename IVR' into IVR.
  rename MASK' into MASK.
  rename CSR' into CSR.
  rename PARAM' into PARAM.
  rename GOAL' into GOAL.





(* step 3 *)

  (* to P__ *)
  assert
  (exists Ms' O', P__ (Cu,Cs) ((Mu,Ms),(R,F)) ((Mu,Ms'),O')) as H. {
    apply (Exists_P_Sup Cu Cs Mu Ms (srl l3 ($1)ₙ l3) (R,F));
    try apply IVR; auto.
    asserts_rewrite (cursor_O (R, F) = (cursor_O (R_, F_)) +ᵢ ($4) +ᵢ ($4)). iauto.
    apply FUNC.
  }

  destruct H as (Ms' & O' & P__).
  destruct O' as (R' & F').

  (* small changes in one step *)
  assert (R#npc = R'#pc /\ R'#npc = R#npc +ᵢ ($4) /\
          R#cwp = R'#cwp /\ R#annul = R'#annul /\ R#et = R'#et /\ R#trap = R'#trap /\ R#s = R'#s /\
          R'#r19 = R#r19 >>ᵢ ($1) /\ R#r20 = R'#r20 /\ R#r17 = R'#r17 /\ R#r18 = R'#r18 /\ F = F'). {

    inverts P__; auto.
    (* usr_mode *) {
    false. apply (ModeDeq (R,F)); auto.
    apply IVR.
    }
    (* sup_mode *) {
    inverts H8; auto.
    assert (Cs (get_R pc R) = Some (srl l3 ($1)ₙ l3)). {
      asserts_rewrite (get_R pc R = (get_R pc R_) +ᵢ ($ 4) +ᵢ ($ 4) ). iauto.
      apply FUNC.
    }
    rewrite H10 in H. clear H10.
    inverts H.
    inverts H11; try inverts H8; auto.
    {
      inverts H4;
      try inverts H6;
      try inverts H8;
      try inverts H2;
      repeat (split; auto).

      unfold eval_OpExp in H9.
      destruct (($ (-4096)) <=ᵢ ($ 1) && ($ 1) <=ᵢ ($ 4095));
      try inverts H9.
      auto.
    }
    (* unexpected_trap? no! *){
    unfolds in H2.
    unfold trap_type in H2.
    assert (usr_mode R = false). apply IVR.
    inverts H2.
    }
    (* annul? no !*){
    false.
    apply (AnnulDeq R).
    apply H2. apply IVR.
    }
    }
  }

  assert (handler_context R') as IVR'. {
    unfolds.
    splits; try unfolds; try unfolds;
    try asserts_rewrite ((get_R cwp R') = (get_R cwp R));
    try asserts_rewrite ((get_R annul R') = (get_R annul R)); 
    try asserts_rewrite ((get_R et R') = (get_R et R));
    try asserts_rewrite ((get_R trap R') = (get_R trap R));
    try asserts_rewrite ((get_R s R') = (get_R s R));
    try asserts_rewrite ((get_R r17 R') = (get_R r17 R));
    try asserts_rewrite ((get_R r18 R') = (get_R r18 R));
    iauto; apply IVR.
  }

  assert (single_mask R'#cwp+ᵢ($7) R'#r20 /\
              ((1 <= Int.unsigned (R'#cwp) <= 7 /\ single_mask (R'#cwp) -ᵢ ($ 1) (R'#r19)) \/
              (Int.unsigned (R'#cwp) = 0 /\ (R'#r19) = ($0)))) as MASK'. {
    split.
    {
    asserts_rewrite (get_R r20 R' = get_R r20 R). iauto.
    asserts_rewrite (get_R cwp R' = get_R cwp R). iauto.
    apply MASK.
    }
    {
      intros.
      asserts_rewrite (get_R r19 R' = (get_R r19 R) >>ᵢ ($ 1)). iauto.
      apply Mask_When_Shiftr; auto.
      asserts_rewrite (get_R cwp R' = get_R cwp R). iauto.
      apply IVR.
      asserts_rewrite (get_R cwp R' = get_R cwp R). iauto.
      apply MASK.
    }
  }


  assert (R'#pc = R_#pc +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) /\ normal_cursor (R',F')) as CSR'. {
    splits. {
      asserts_rewrite (get_R pc R' = get_R npc R). iauto.
      asserts_rewrite (get_R npc R = (get_R pc R) +ᵢ ($ 4)). apply CSR.
      asserts_rewrite (get_R pc R = (get_R pc R_) +ᵢ ($ 4) +ᵢ ($ 4) ). apply CSR.
      auto.
    }
    {
      unfolds.
        asserts_rewrite (get_R npc R' = (get_R npc R) +ᵢ ($ 4)). iauto.
        asserts_rewrite (get_R pc R'  = get_R npc R). iauto.
        auto.
    }
  }

  assert (f_context F') as PARAM'. {
    asserts_rewrite (F' = F). iauto.
    apply PARAM.
  }

  assert (Q__ (Cu, Cs) (Mu, Ms_, (R_, F_)) [None;None;None] 3 (Mu, Ms', (R', F'))) as GOAL'.
  {
    apply (No_Event (Cu,Cs) [None;None] 2 (Mu, Ms_, (R_, F_)) (Mu, Ms', (R', F')) (Mu, Ms, (R, F))); auto.
  }

  clear P__ IVR MASK CSR PARAM GOAL Ms R F H.
  rename Ms' into Ms.
  rename R' into R.
  rename F' into F.
  rename IVR' into IVR.
  rename MASK' into MASK.
  rename CSR' into CSR.
  rename PARAM' into PARAM.
  rename GOAL' into GOAL.



(* step 4 *)

  (* to P__ *)
  assert
  (exists Ms' O', P__ (Cu,Cs) ((Mu,Ms),(R,F)) ((Mu,Ms'),O')) as H. {
    apply (Exists_P_Sup Cu Cs Mu Ms (or l3 l4 ᵣ l3) (R,F));
    try apply IVR; auto.
    asserts_rewrite (cursor_O (R, F) = (cursor_O (R_, F_)) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)). iauto.
    apply FUNC.
  }

  destruct H as (Ms' & O' & P__).
  destruct O' as (R' & F').

  (* small changes in one step *)
  assert (R#npc = R'#pc /\ R'#npc = R#npc +ᵢ ($4) /\
          R#cwp = R'#cwp /\ R#annul = R'#annul /\ R#et = R'#et /\ R#trap = R'#trap /\ R#s = R'#s /\
          R'#r19 = R#r19 |ᵢ  (R#r20) /\ R#r17 = R'#r17 /\ R#r18 = R'#r18 /\ F = F'). {

    inverts P__; auto.
    (* usr_mode *) {
    false. apply (ModeDeq (R,F)); auto.
    apply IVR.
    }
    (* sup_mode *) {
    inverts H8; auto.
    assert (Cs (get_R pc R) = Some (or l3 l4 ᵣ l3)). {
      asserts_rewrite (get_R pc R = (get_R pc R_) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) ). iauto.
      apply FUNC.
    }
    rewrite H10 in H. clear H10.
    inverts H.
    inverts H11; try inverts H8; auto.
    {
      inverts H4;
      try inverts H6;
      try inverts H8;
      try inverts H2;
      repeat (split; auto).
      unfold eval_OpExp in H9.
      inverts H9.
      auto.
    }
    (* unexpected_trap? no! *){
    unfolds in H2.
    unfold trap_type in H2.
    assert (usr_mode R = false). apply IVR.
    inverts H2.
    }
    (* annul? no !*){
    false.
    apply (AnnulDeq R).
    apply H2. apply IVR.
    }
    }
  }

  assert (handler_context R') as IVR'. {
    unfolds.
    splits; try unfolds; try unfolds;
    try asserts_rewrite ((get_R cwp R') = (get_R cwp R));
    try asserts_rewrite ((get_R annul R') = (get_R annul R)); 
    try asserts_rewrite ((get_R et R') = (get_R et R));
    try asserts_rewrite ((get_R trap R') = (get_R trap R));
    try asserts_rewrite ((get_R s R') = (get_R s R));
    try asserts_rewrite ((get_R r17 R') = (get_R r17 R));
    try asserts_rewrite ((get_R r18 R') = (get_R r18 R));
    iauto; apply IVR.
  }

  assert (single_mask (pre_cwp 1 R')(R'#r19&ᵢ($255))) as MASK'. {
    asserts_rewrite (get_R r19 R' = (get_R r19 R) |ᵢ (get_R r20 R)). iauto.
    unfold pre_cwp.
    asserts_rewrite (get_R cwp R' = get_R cwp R). iauto.
     apply Win_Xor; iauto.
     apply IVR.
  }

  assert (R'#pc = R_#pc +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) /\ normal_cursor (R',F')) as CSR'. {
    splits. {
      asserts_rewrite (get_R pc R' = get_R npc R). iauto.
      asserts_rewrite (get_R npc R = (get_R pc R) +ᵢ ($ 4)). apply CSR.
      asserts_rewrite (get_R pc R = (get_R pc R_) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) ). apply CSR.
      auto.
    }
    {
      unfolds.
        asserts_rewrite (get_R npc R' = (get_R npc R) +ᵢ ($ 4)). iauto.
        asserts_rewrite (get_R pc R'  = get_R npc R). iauto.
        auto.
    }
  }

  assert (f_context F') as PARAM'. {
    asserts_rewrite (F' = F). iauto.
    apply PARAM.
  }

  assert (Q__ (Cu, Cs) (Mu, Ms_, (R_, F_)) [None;None;None;None] 4 (Mu, Ms', (R', F'))) as GOAL'.
  {
    apply (No_Event (Cu,Cs) [None;None;None] 3 (Mu, Ms_, (R_, F_)) (Mu, Ms', (R', F')) (Mu, Ms, (R, F))); auto.
  }

  clear P__ IVR MASK CSR PARAM GOAL Ms R F H.
  rename Ms' into Ms.
  rename R' into R.
  rename F' into F.
  rename IVR' into IVR.
  rename MASK' into MASK.
  rename CSR' into CSR.
  rename PARAM' into PARAM.
  rename GOAL' into GOAL.



(* step 5 *)

  (* to P__ *)
  assert
  (exists Ms' O', P__ (Cu,Cs) ((Mu,Ms),(R,F)) ((Mu,Ms'),O')) as H. {
    apply (Exists_P_Sup Cu Cs Mu Ms (and l3 ($255)ₙ l3) (R,F));
    try apply IVR; auto.
    asserts_rewrite (cursor_O (R, F) = (cursor_O (R_, F_)) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)). iauto.
    apply FUNC.
  }

  destruct H as (Ms' & O' & P__).
  destruct O' as (R' & F').

  (* small changes in one step *)
  assert (R#npc = R'#pc /\ R'#npc = R#npc +ᵢ ($4) /\
          R#cwp = R'#cwp /\ R#annul = R'#annul /\ R#et = R'#et /\ R#trap = R'#trap /\ R#s = R'#s /\
          R'#r19 = R#r19 &ᵢ($255) /\ R#r17 = R'#r17 /\ R#r18 = R'#r18 /\ F = F'). {

    inverts P__; auto.
    (* usr_mode *) {
    false. apply (ModeDeq (R,F)); auto.
    apply IVR.
    }
    (* sup_mode *) {
    inverts H8; auto.
    assert (Cs (get_R pc R) = Some (and l3 ($255)ₙ l3)). {
      asserts_rewrite (get_R pc R = (get_R pc R_) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)). iauto.
      apply FUNC.
    }
    rewrite H10 in H. clear H10.
    inverts H.
    inverts H11; try inverts H8; auto.
    {
      inverts H4;
      try inverts H6;
      try inverts H8;
      try inverts H2;
      repeat (split; auto).

    unfold eval_OpExp in H9.
    destruct (($ (-4096)) <=ᵢ ($ 255) && ($ 255) <=ᵢ ($ 4095));
    try inverts H9.
    auto.
    }
    }
    (* unexpected_trap? no! *){
    unfolds in H2.
    unfold trap_type in H2.
    assert (usr_mode R = false). apply IVR.
    inverts H2.
    }
    (* annul? no !*){
    false.
    apply (AnnulDeq R).
    apply H2. apply IVR.
    }
    }
  }

  assert (handler_context R') as IVR'. {
    unfolds.
    splits; try unfolds; try unfolds;
    try asserts_rewrite ((get_R cwp R') = (get_R cwp R));
    try asserts_rewrite ((get_R annul R') = (get_R annul R)); 
    try asserts_rewrite ((get_R et R') = (get_R et R));
    try asserts_rewrite ((get_R trap R') = (get_R trap R));
    try asserts_rewrite ((get_R s R') = (get_R s R));
    try asserts_rewrite ((get_R r17 R') = (get_R r17 R));
    try asserts_rewrite ((get_R r18 R') = (get_R r18 R));
    iauto; apply IVR.
  }

  assert (single_mask (pre_cwp 1 R')(R'#r19)) as MASK'. {
    asserts_rewrite (get_R r19 R' = (get_R r19 R) &ᵢ ($ 255)). iauto.
    unfold pre_cwp.
    asserts_rewrite (get_R cwp R' = get_R cwp R). iauto.
    apply MASK.
  }

  assert (R'#pc = R_#pc +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) /\ normal_cursor (R',F')) as CSR'. {
    splits. {
      asserts_rewrite (get_R pc R' = get_R npc R). iauto.
      asserts_rewrite (get_R npc R = (get_R pc R) +ᵢ ($ 4)). apply CSR.
      asserts_rewrite (get_R pc R = (get_R pc R_) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) ). apply CSR.
      auto.
    }
    {
      unfolds.
        asserts_rewrite (get_R npc R' = (get_R npc R) +ᵢ ($ 4)). iauto.
        asserts_rewrite (get_R pc R'  = get_R npc R). iauto.
        auto.
    }
  }

  assert (f_context F') as PARAM'. {
    asserts_rewrite (F' = F). iauto.
    apply PARAM.
  }

  assert (Q__ (Cu, Cs) (Mu, Ms_, (R_, F_)) [None;None;None;None;None] 5 (Mu, Ms', (R', F'))) as GOAL'.
  {
    apply (No_Event (Cu,Cs) [None;None;None;None] 4 (Mu, Ms_, (R_, F_)) (Mu, Ms', (R', F')) (Mu, Ms, (R, F))); auto.
  }

  clear P__ IVR MASK CSR PARAM GOAL Ms R F H.
  rename Ms' into Ms.
  rename R' into R.
  rename F' into F.
  rename IVR' into IVR.
  rename MASK' into MASK.
  rename CSR' into CSR.
  rename PARAM' into PARAM.
  rename GOAL' into GOAL.



(* step 6 *)

  (* to P__ *)
  assert
  (exists Ms' O', P__ (Cu,Cs) ((Mu,Ms),(R,F)) ((Mu,Ms'),O')) as H. {
    apply (Exists_P_Sup Cu Cs Mu Ms (wr g0 g0 ᵣ wim) (R,F));
    try apply IVR; auto.
    asserts_rewrite (cursor_O (R, F) = (cursor_O (R_, F_)) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)). iauto.
    apply FUNC.
  }

  destruct H as (Ms' & O' & P__).
  destruct O' as (R' & F').

  (* small changes in one step *)
  assert (R#npc = R'#pc /\ R'#npc = R#npc +ᵢ ($4) /\
          R#cwp = R'#cwp /\ R#annul = R'#annul /\ R#et = R'#et /\ R#trap = R'#trap /\ R#s = R'#s /\
          R'#wim = ($0) /\ R#r19 = R'#r19 /\ R#r17 = R'#r17 /\ R#r18 = R'#r18 /\ F = F'). {

    inverts P__; auto.
    (* usr_mode *) {
    false. apply (ModeDeq (R,F)); auto.
    apply IVR.
    }
    (* sup_mode *) {
    inverts H8; auto.
    assert (Cs (get_R pc R) = Some (wr g0 g0 ᵣ wim)). {
      asserts_rewrite (get_R pc R = (get_R pc R_) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)). iauto.
      apply FUNC.
    }
    rewrite H10 in H. clear H10.
    inverts H.
    inverts H11; try inverts H8; auto.
    {
      inverts H4;
      try inverts H6;
      try inverts H8;
      try inverts H2;
      repeat (split; auto).

      destruct H9 as ( b1 & FALSE & b2).
      unfolds in FALSE. iauto.

      unfold eval_OpExp in H11.
      simpl in H11.
      inverts H11.
      asserts_rewrite (((get_R r0 R) xor ($ 0)) = ($0)). {
        simpl.
        apply Int.xor_zero.
      }
      auto.
    }
    (* unexpected_trap? no! *){
    unfolds in H2.
    unfold trap_type in H2.
    asserts_rewrite (usr_mode R = false) in H2. apply IVR.
    inverts H2.
    }
    (* annul? no !*){
    false.
    apply (AnnulDeq R).
    apply H2. apply IVR.
    }
    }
  }

  assert (handler_context R') as IVR'. {
    unfolds.
    splits; try unfolds; try unfolds;
    try asserts_rewrite ((get_R cwp R') = (get_R cwp R));
    try asserts_rewrite ((get_R annul R') = (get_R annul R)); 
    try asserts_rewrite ((get_R et R') = (get_R et R));
    try asserts_rewrite ((get_R trap R') = (get_R trap R));
    try asserts_rewrite ((get_R s R') = (get_R s R));
    try asserts_rewrite ((get_R r17 R') = (get_R r17 R));
    try asserts_rewrite ((get_R r18 R') = (get_R r18 R));
    iauto; apply IVR.
  }

  assert (single_mask (pre_cwp 1 R')(R'#r19) /\ R'#wim = ($0)) as MASK'. {
    split.
    asserts_rewrite (get_R r19 R' = (get_R r19 R)). iauto.
    unfold pre_cwp.
    asserts_rewrite (get_R cwp R' = get_R cwp R). iauto.
    apply MASK.
    iauto.
  }

  assert (R'#pc = R_#pc +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) /\ normal_cursor (R',F')) as CSR'. {
    splits. {
      asserts_rewrite (get_R pc R' = get_R npc R). iauto.
      asserts_rewrite (get_R npc R = (get_R pc R) +ᵢ ($ 4)). apply CSR.
      asserts_rewrite (get_R pc R = (get_R pc R_) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) ). apply CSR.
      auto.
    }
    {
      unfolds.
        asserts_rewrite (get_R npc R' = (get_R npc R) +ᵢ ($ 4)). iauto.
        asserts_rewrite (get_R pc R'  = get_R npc R). iauto.
        auto.
    }
  }

  assert (f_context F') as PARAM'. {
    asserts_rewrite (F' = F). iauto.
    apply PARAM.
  }

  assert (Q__ (Cu, Cs) (Mu, Ms_, (R_, F_)) [None;None;None;None;None;None] 6 (Mu, Ms', (R', F'))) as GOAL'.
  {
    apply (No_Event (Cu,Cs) [None;None;None;None;None] 5 (Mu, Ms_, (R_, F_)) (Mu, Ms', (R', F')) (Mu, Ms, (R, F))); auto.
  }

  clear P__ IVR MASK CSR PARAM GOAL Ms R F H.
  rename Ms' into Ms.
  rename R' into R.
  rename F' into F.
  rename IVR' into IVR.
  rename MASK' into MASK.
  rename CSR' into CSR.
  rename PARAM' into PARAM.
  rename GOAL' into GOAL.

Abort.



(* step 6*)

  assert (Cs (cursor_O (R, F)) = Some (wr g0 l3 ᵣ wim)) as INS. {
  assert (cursor_O (R, F) = (cursor_O (R_, F_)) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)+ᵢ ($ 4)). {
     apply MOV.
    }
    rewrite H.
    apply FUNC.
  }

  assert
  (exists Ms' O', P__ (Cu,Cs) ((Mu,Ms),(R,F)) ((Mu,Ms'),O')). {
    apply (Exists_P_Sup Cu Cs Mu Ms (wr g0 l3 ᵣ wim) (R,F));
    auto; try apply IVR; try apply FUNC.
  }
  destruct H as (Ms' & O' & H).
  destruct O' as (R' & F').
  assert (R#npc = R'#pc /\ R'#npc = R#npc +ᵢ ($4) /\ R#cwp = R'#cwp
  /\ R#annul = R'#annul /\ R#et = R'#et /\ R#trap = R'#trap /\ R#s = R'#s /\ R'#wim = R#r19 /\ R#r17 = R'#r17 /\ R#r18 = R'#r18). {
    inverts H; auto.
    (* usr_mode *) {
    false. apply (ModeDeq (R,F)); auto.
    apply IVR.
    }
    (* sup_mode *) {
    inverts FUNC2; auto.
    assert (Cs (get_R pc R) = Some (wr g0 l3 ᵣ wim)). {
    apply INS.
    }
    rewrite H in FUNC3. clear H.
    inverts FUNC3.
    inverts FUNC4; try inverts FUNC0; auto.
    {
      inverts H6;
      try inverts H5;
      try inverts H9;
      try inverts FUNC0;
      repeat (split; auto).
      false.
      inverts FUNC4.
      auto.
      assert ((get_R r0 R) xor (R r19) = (R r19)).
      {
        simpl.
        apply (Int.xor_zero_l (R r19)).
      }
      rewrite H. auto.
    }
    (* unexpected_trap? no! *){
    unfolds in H5.
    unfold trap_type in H5.
    assert (usr_mode R = false).
    {
      apply FUNC1.
    }
    rewrite H in H5.
    inverts H5.
    }
    (* annul? no !*){
    false.
    apply (AnnulDeq R).
    apply H5. apply IVR.
    }
    }
  }

  assert (align_context (R', F')).
  {
   unfolds.
   assert (get_R r17 R = get_R r17 R'). apply H3.
   rewrite <- H4. clear H4.
   assert (get_R r18 R = get_R r18 R'). apply H3.
   rewrite <- H4. clear H4.
   apply A.
  }
  clear A. rename H4 into A.

  assert (R'#pc = R_#pc +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)/\ normal_cursor (R',F') /\  handler_context (R', F') /\ single_mask (pre_cwp 1 R')(R'#wim)). {
    split.
    {
      assert (get_R npc R = get_R pc R'). apply H3.
      assert (get_R npc R = (get_R pc R) +ᵢ ($ 4)). apply CSR.
      rewrite H4 in H5.
      rewrite <- MOV. apply H5.
    }
    split.
    {
      unfolds.
      assert (get_R npc R' = (get_R pc R') +ᵢ ($ 4)).
      {
      assert (get_R npc R' = (get_R npc R) +ᵢ ($ 4)). apply H3.
      assert (get_R npc R = get_R pc R' ). apply H3.
      rewrite H5 in H4.
      apply H4.
      }
      unfolds.
      auto.
    }
    split.
    {
      unfolds.
      split.
      {
      assert (get_R cwp R = get_R cwp R'). apply H3.
      unfolds.
      rewrite <- H4.
      apply IVR.
      }
      split.
      {
      assert (get_R annul R = get_R annul R'). apply H3.
      unfolds.
      unfolds.
      unfolds.
      rewrite <- H4.
      apply IVR.
      }
      split.
      {
      assert (get_R et R = get_R et R' ). apply H3.
      unfolds.
      unfolds.
      unfolds.
      rewrite <- H4.
      apply IVR.
      }
      split.
      {
      assert (get_R trap R = get_R trap R'). apply H3.
      unfolds.
      unfolds.
      unfolds.
      rewrite <- H4.
      apply IVR.
      }
      assert (get_R s R = get_R s R' ). apply H3.
      unfolds.
      unfolds.
      unfolds.
      rewrite <- H4.
      apply IVR.
      }
      {
        assert (get_R cwp R = get_R cwp R').
        apply H3.
        unfold pre_cwp.
        rewrite <- H4. clear H4.
        assert (get_R wim R' = get_R r19 R).
        apply H3.
        rewrite H4. clear H4.
        apply H2.
      }
  }
  clear H3 CSR.
  clear IVR H2 MOV.
  destruct H4 as (MOV & CSR & IVR & H2).
  rename GOAL into PRE_GOAL.
  assert (Q__ (Cu, Cs) (Mu, Ms_, (R_, F_)) [None;None;None;None;None;None] 6 (Mu, Ms', (R', F'))) as GOAL.
  {
    apply (No_Event (Cu,Cs) [None;None;None;None;None] 5 (Mu, Ms_, (R_, F_)) (Mu, Ms', (R', F')) (Mu, Ms, (R, F))); auto.
  }
  clear H.
  clear PRE_GOAL.
  clear INS.
  clear Ms R F.
  rename Ms' into Ms.
  rename R' into R.
  rename F' into F.



(* step 7*)
  
  assert (Cs (cursor_O (R, F)) = Some (jmpl l1 ₐᵣ g0)) as INS. {
  assert (cursor_O (R, F) = (cursor_O (R_, F_)) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)+ᵢ ($ 4)+ᵢ ($ 4)). {
     apply MOV.
    }
    rewrite H.
    apply FUNC.
  }

  assert
  (exists Ms' O', P__ (Cu,Cs) ((Mu,Ms),(R,F)) ((Mu,Ms'),O')). {
    apply (Exists_P_Sup Cu Cs Mu Ms (jmpl l1 ₐᵣ g0) (R,F));
    auto; try apply IVR; try apply FUNC.
  }
  destruct H as (Ms' & O' & H).
  destruct O' as (R' & F').
  assert (R#npc = R'#pc /\ R#cwp = R'#cwp
  /\ R#annul = R'#annul /\ R#et = R'#et /\ R#trap = R'#trap /\ R#s = R'#s /\ R#wim = R'#wim /\ R#r17 = R'#r17 /\ R#r18 = R'#r18). {
    inverts H; auto.
    (* usr_mode *) {
    false. apply (ModeDeq (R,F)); auto.
    apply IVR.
    }
    (* sup_mode *) {
    inverts FUNC2; auto.
    assert (Cs (get_R pc R) = Some (jmpl l1 ₐᵣ g0)). {
    apply INS.
    }
    rewrite H in FUNC3. clear H.
    inverts FUNC3.
    inverts FUNC4; try inverts FUNC0; auto.
    {
      inverts H6;
      try inverts H5;
      try inverts H9;
      try inverts FUNC0;
      repeat (split; auto).
    }
    (* unexpected_trap? no! *){
    unfolds in H5.
    unfold trap_type in H5.
    unfold eval_AddrExp in H5.
    unfold eval_OpExp in H5.
    assert (word_aligned (get_R r17 R) = true).
    apply A.
    rewrite H in H5.
    simpl in H5.
    inverts H5.
    }
    (* annul? no !*){
    false.
    apply (AnnulDeq R).
    apply H5. apply IVR.
    }
    }
  }

  assert (align_context (R', F')).
  {
   unfolds.
   assert (get_R r17 R = get_R r17 R'). apply H3.
   rewrite <- H4. clear H4.
   assert (get_R r18 R = get_R r18 R'). apply H3.
   rewrite <- H4. clear H4.
   apply A.
  }
  clear A. rename H4 into A.

  assert (R'#pc = R_#pc +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) /\ handler_context (R', F') /\ single_mask (pre_cwp 1 R')(R'#wim)). {
    split.
    {
      assert (get_R npc R = get_R pc R'). apply H3.
      assert (get_R npc R = (get_R pc R) +ᵢ ($ 4)). apply CSR.
      rewrite H4 in H5.
      rewrite <- MOV. apply H5.
    }
    split.
    {
      unfolds.
      split.
      {
      assert (get_R cwp R = get_R cwp R'). apply H3.
      unfolds.
      rewrite <- H4.
      apply IVR.
      }
      split.
      {
      assert (get_R annul R = get_R annul R'). apply H3.
      unfolds.
      unfolds.
      unfolds.
      rewrite <- H4.
      apply IVR.
      }
      split.
      {
      assert (get_R et R = get_R et R' ). apply H3.
      unfolds.
      unfolds.
      unfolds.
      rewrite <- H4.
      apply IVR.
      }
      split.
      {
      assert (get_R trap R = get_R trap R'). apply H3.
      unfolds.
      unfolds.
      unfolds.
      rewrite <- H4.
      apply IVR.
      }
      assert (get_R s R = get_R s R' ). apply H3.
      unfolds.
      unfolds.
      unfolds.
      rewrite <- H4.
      apply IVR.
      }
      {
        assert (get_R cwp R = get_R cwp R').
        apply H3.
        unfold pre_cwp.
        rewrite <- H4. clear H4.
        assert (get_R wim R = get_R wim R').
        apply H3.
        rewrite <- H4. clear H4.
        apply H2.
      }
  }
  clear H3 CSR.
  clear IVR H2 MOV.
  destruct H4 as (MOV & IVR & H2).
  rename GOAL into PRE_GOAL.
  assert (Q__ (Cu, Cs) (Mu, Ms_, (R_, F_)) [None;None;None;None;None;None;None] 7 (Mu, Ms', (R', F'))) as GOAL.
  {
    apply (No_Event (Cu,Cs) [None;None;None;None;None;None] 6 (Mu, Ms_, (R_, F_)) (Mu, Ms', (R', F')) (Mu, Ms, (R, F))); auto.
  }
  clear H.
  clear PRE_GOAL.
  clear INS.
  clear Ms R F.
  rename Ms' into Ms.
  rename R' into R.
  rename F' into F.


(* step 8*)
  
  assert (Cs (cursor_O (R, F)) = Some (rett l2 ₐᵣ)) as INS. {
  assert (cursor_O (R, F) = (cursor_O (R_, F_)) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)+ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)). {
     apply MOV.
    }
    rewrite H.
    apply FUNC.
  }

  assert
  (exists Ms' O', P__ (Cu,Cs) ((Mu,Ms),(R,F)) ((Mu,Ms'),O')). {
    apply (Exists_P_Sup Cu Cs Mu Ms (rett l2 ₐᵣ) (R,F));
    auto; try apply IVR; try apply FUNC.
    unfolds.
    unfold eval_AddrExp.
    unfold eval_OpExp.
    assert (word_aligned (get_R r18 R) = true). apply A.
    rewrite H. clear H.
    assert (usr_mode R = false). apply IVR.
    rewrite H. clear H.
    unfold inc_win.
    assert ((win_masked (post_cwp 1 R) R) = false). {
      unfold win_masked.
      unfold single_mask in H2.
      rewrite <- H2.
      unfold post_cwp.
      unfold pre_cwp.
      unfold Asm.N.
      simpl.
      assert (0 <= Int.unsigned (R#cwp) <= 7). apply IVR.
      clear A MOV IVR FUNC H2 INS GOAL.
      remember (Int.unsigned (R#cwp)) as n.
      simpl in Heqn.
        assert (n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5
   \/ n = 6 \/ n = 7). mauto. clear H.
      destruct IVR. {
        assert (((R cwp) +ᵢ ($ 1)) modu ($ 8) = ($1)). {
          mauto.
          rewrite <- Heqn.
          rewrite H.
          mauto.
        }
        rewrite IVR. clear IVR.
        assert ((((R cwp) +ᵢ ($ 8)) -ᵢ ($ 1)) modu ($ 8) = ($7)). {
          mauto.
          rewrite <- Heqn.
          rewrite H.
          mauto.
        }
        rewrite IVR. clear IVR.
        mauto.
      }
      destruct H. {
        assert (((R cwp) +ᵢ ($ 1)) modu ($ 8) = ($2)). {
          mauto.
          rewrite <- Heqn.
          rewrite H.
          mauto.
        }
        rewrite IVR. clear IVR.
        assert ((((R cwp) +ᵢ ($ 8)) -ᵢ ($ 1)) modu ($ 8) = ($0)). {
          mauto.
          rewrite <- Heqn.
          rewrite H.
          mauto.
        }
        rewrite IVR. clear IVR.
        mauto.
      }
      destruct H. {
        assert (((R cwp) +ᵢ ($ 1)) modu ($ 8) = ($3)). {
          mauto.
          rewrite <- Heqn.
          rewrite H.
          mauto.
        }
        rewrite IVR. clear IVR.
        assert ((((R cwp) +ᵢ ($ 8)) -ᵢ ($ 1)) modu ($ 8) = ($1)). {
          mauto.
          rewrite <- Heqn.
          rewrite H.
          mauto.
        }
        rewrite IVR. clear IVR.
        mauto.
      }
      destruct H. {
        assert (((R cwp) +ᵢ ($ 1)) modu ($ 8) = ($4)). {
          mauto.
          rewrite <- Heqn.
          rewrite H.
          mauto.
        }
        rewrite IVR. clear IVR.
        assert ((((R cwp) +ᵢ ($ 8)) -ᵢ ($ 1)) modu ($ 8) = ($2)). {
          mauto.
          rewrite <- Heqn.
          rewrite H.
          mauto.
        }
        rewrite IVR. clear IVR.
        mauto.
      }
      destruct H. {
        assert (((R cwp) +ᵢ ($ 1)) modu ($ 8) = ($5)). {
          mauto.
          rewrite <- Heqn.
          rewrite H.
          mauto.
        }
        rewrite IVR. clear IVR.
        assert ((((R cwp) +ᵢ ($ 8)) -ᵢ ($ 1)) modu ($ 8) = ($3)). {
          mauto.
          rewrite <- Heqn.
          rewrite H.
          mauto.
        }
        rewrite IVR. clear IVR.
        mauto.
      }
      destruct H. {
        assert (((R cwp) +ᵢ ($ 1)) modu ($ 8) = ($6)). {
          mauto.
          rewrite <- Heqn.
          rewrite H.
          mauto.
        }
        rewrite IVR. clear IVR.
        assert ((((R cwp) +ᵢ ($ 8)) -ᵢ ($ 1)) modu ($ 8) = ($4)). {
          mauto.
          rewrite <- Heqn.
          rewrite H.
          mauto.
        }
        rewrite IVR. clear IVR.
        mauto.
      }
      destruct H. {
        assert (((R cwp) +ᵢ ($ 1)) modu ($ 8) = ($7)). {
          mauto.
          rewrite <- Heqn.
          rewrite H.
          mauto.
        }
        rewrite IVR. clear IVR.
        assert ((((R cwp) +ᵢ ($ 8)) -ᵢ ($ 1)) modu ($ 8) = ($5)). {
          mauto.
          rewrite <- Heqn.
          rewrite H.
          mauto.
        }
        rewrite IVR. clear IVR.
        mauto.
      }
      {
        assert (((R cwp) +ᵢ ($ 1)) modu ($ 8) = ($0)). {
          mauto.
          rewrite <- Heqn.
          rewrite H.
          mauto.
        }
        rewrite IVR. clear IVR.
        assert ((((R cwp) +ᵢ ($ 8)) -ᵢ ($ 1)) modu ($ 8) = ($6)). {
          mauto.
          rewrite <- Heqn.
          rewrite H.
          mauto.
        }
        rewrite IVR. clear IVR.
        mauto.
      }
    }
    rewrite H. simpl. auto.
  }
  destruct H as (Ms' & O' & H).
  destruct O' as (R' & F').
  assert ( R'#cwp = post_cwp 1 R /\ R'#trap = R#trap /\ R#wim = R'#wim). {
    inverts H; auto.
    (* usr_mode *) {
    false. apply (ModeDeq (R,F)); auto.
    apply IVR.
    }
    (* sup_mode *) {
    inverts FUNC2; auto.
    assert (Cs (get_R pc R) = Some (rett l2 ₐᵣ)). {
    apply INS.
    }
    rewrite H in FUNC3. clear H.
    inverts FUNC3.
    inverts FUNC4; try inverts FUNC0; auto.
    {
      inverts H6;
      try inverts H5;
      try inverts H9;
      try inverts FUNC0;
      repeat (split; auto).
    }
    {
    unfolds in FUNC8.
    remember (inc_win (R, F)) as O''.
    destruct O''.
    destruct r as (R'' & F'').
    assert (R#wim = R''#wim /\ R#trap = R''#trap /\ R#s = R''#s).
    apply (Hold_Sth_IncWin R R'' F F''); auto.
    clear HeqO''.
    remember (restore_mode (enable_trap R'')) as R'''.
    inverts FUNC8.
    assert (R'0#wim = R''#wim /\ R'0#trap = R''#trap). {
      rewrite <- H3.
      split. auto. auto.
    }
    split. skip.
    split.
    {
      unfold djmp.
      asserts_rewrite (get_R trap R = get_R trap R'0). {
      assert (get_R trap R = get_R trap R''). apply H.
      rewrite H5. clear H5.
      symmetry.
      apply H4.
    }
     eauto.
     }
    {
    unfold djmp.
    asserts_rewrite (get_R wim R = get_R wim R'0). {
      assert (get_R wim R = get_R wim R''). apply H.
      rewrite H5. clear H5.
      symmetry.
      apply H4.
    }
    eauto.
    }
    inverts FUNC8.
    }
    (* unexpected_trap? no! *){
    unfolds in H5.
    unfold trap_type in H5.
    assert (trap_enabled R = false). apply IVR.
    rewrite H in H5. 
    inverts H5.
    }
    (* annul? no !*){
    false.
    apply (AnnulDeq R).
    apply H5. apply IVR.
    }
    }
  }

  assert (no_trap_R R' /\ single_mask (pre_cwp 2 R')(R'#wim)). {
    split.
    {
      unfolds.
      unfolds.
      assert (get_R trap R' = get_R trap R). apply H3.
      rewrite H4. apply IVR.
   }
    {
      unfold single_mask in *.
      unfold post_cwp in *.
      unfold pre_cwp in *.
      unfold Asm.N in *.
      assert (get_R cwp R' = ((get_R cwp R) +ᵢ ($ 1)) modu ($ 8)).
      apply H3.
      rewrite H4. clear H4.
      assert (get_R wim R = get_R wim R'). apply H3.
      rewrite <- H4. clear H4.
      rewrite <- H2.
      simpl.
      {
      assert (0 <= Int.unsigned (R#cwp) <= 7). apply IVR.
      clear A MOV H IVR FUNC H2 H3 INS GOAL.
      remember (Int.unsigned (R#cwp)) as n.
      simpl in Heqn.
        assert (n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5
   \/ n = 6 \/ n = 7). mauto. clear H4.
      destruct H. {
       assert (((R cwp) +ᵢ ($ 1)) modu ($ 8) = ($1)). {
         int auto.
         rewrite <- Heqn.
         rewrite H.
         int auto.
       }
       rewrite IVR. clear IVR.
      assert ((($ 1) +ᵢ ($ 8)) -ᵢ ($ 2) modu ($ 8) = ($7)). {
         int auto.
      }
      rewrite IVR. clear IVR.
      assert ((((R cwp) +ᵢ ($ 8)) -ᵢ ($ 1)) modu ($ 8) = ($7)). {
         int auto.
         rewrite <- Heqn.
         rewrite H.
         int auto.
      }
      rewrite IVR. clear IVR. auto.
      }


      destruct H. {
       assert (((R cwp) +ᵢ ($ 1)) modu ($ 8) = ($2)). {
         int auto.
         rewrite <- Heqn.
         rewrite H.
         int auto.
       }
       rewrite IVR. clear IVR.
      assert ((($ 2) +ᵢ ($ 8)) -ᵢ ($ 2) modu ($ 8) = ($0)). {
         mauto.
      }
      rewrite IVR. clear IVR.
      assert ((((R cwp) +ᵢ ($ 8)) -ᵢ ($ 1)) modu ($ 8) = ($0)). {
         int auto.
         rewrite <- Heqn.
         rewrite H.
         int auto.
      }
      rewrite IVR. clear IVR. auto.
      }

      destruct H. {
       assert (((R cwp) +ᵢ ($ 1)) modu ($ 8) = ($3)). {
         int auto.
         rewrite <- Heqn.
         rewrite H.
         int auto.
       }
       rewrite IVR. clear IVR.
      assert ((($ 3) +ᵢ ($ 8)) -ᵢ ($ 2) modu ($ 8) = ($1)). {
         mauto.
      }
      rewrite IVR. clear IVR.
      assert ((((R cwp) +ᵢ ($ 8)) -ᵢ ($ 1)) modu ($ 8) = ($1)). {
         int auto.
         rewrite <- Heqn.
         rewrite H.
         int auto.
      }
      rewrite IVR. clear IVR. auto.
      }

      destruct H. {
       assert (((R cwp) +ᵢ ($ 1)) modu ($ 8) = ($4)). {
         int auto.
         rewrite <- Heqn.
         rewrite H.
         int auto.
       }
       rewrite IVR. clear IVR.
      assert ((($ 4) +ᵢ ($ 8)) -ᵢ ($ 2) modu ($ 8) = ($2)). {
         mauto.
      }
      rewrite IVR. clear IVR.
      assert ((((R cwp) +ᵢ ($ 8)) -ᵢ ($ 1)) modu ($ 8) = ($2)). {
         int auto.
         rewrite <- Heqn.
         rewrite H.
         int auto.
      }
      rewrite IVR. clear IVR. auto.
      }

      destruct H. {
       assert (((R cwp) +ᵢ ($ 1)) modu ($ 8) = ($5)). {
         int auto.
         rewrite <- Heqn.
         rewrite H.
         int auto.
       }
       rewrite IVR. clear IVR.
      assert ((($ 5) +ᵢ ($ 8)) -ᵢ ($ 2) modu ($ 8) = ($3)). {
         mauto.
      }
      rewrite IVR. clear IVR.
      assert ((((R cwp) +ᵢ ($ 8)) -ᵢ ($ 1)) modu ($ 8) = ($3)). {
         int auto.
         rewrite <- Heqn.
         rewrite H.
         int auto.
      }
      rewrite IVR. clear IVR. auto.
      }


      destruct H. {
       assert (((R cwp) +ᵢ ($ 1)) modu ($ 8) = ($6)). {
         int auto.
         rewrite <- Heqn.
         rewrite H.
         int auto.
       }
       rewrite IVR. clear IVR.
      assert ((($ 6) +ᵢ ($ 8)) -ᵢ ($ 2) modu ($ 8) = ($4)). {
         mauto.
      }
      rewrite IVR. clear IVR.
      assert ((((R cwp) +ᵢ ($ 8)) -ᵢ ($ 1)) modu ($ 8) = ($4)). {
         int auto.
         rewrite <- Heqn.
         rewrite H.
         int auto.
      }
      rewrite IVR. clear IVR. auto.
      }


      destruct H. {
       assert (((R cwp) +ᵢ ($ 1)) modu ($ 8) = ($7)). {
         int auto.
         rewrite <- Heqn.
         rewrite H.
         int auto.
       }
       rewrite IVR. clear IVR.
      assert ((($ 7) +ᵢ ($ 8)) -ᵢ ($ 2) modu ($ 8) = ($5)). {
         mauto.
      }
      rewrite IVR. clear IVR.
      assert ((((R cwp) +ᵢ ($ 8)) -ᵢ ($ 1)) modu ($ 8) = ($5)). {
         int auto.
         rewrite <- Heqn.
         rewrite H.
         int auto.
      }
      rewrite IVR. clear IVR. auto.
      }


      {
       assert (((R cwp) +ᵢ ($ 1)) modu ($ 8) = ($0)). {
         int auto.
         rewrite <- Heqn.
         rewrite H.
         int auto.
       }
       rewrite IVR. clear IVR.
      assert ((($ 0) +ᵢ ($ 8)) -ᵢ ($ 2) modu ($ 8) = ($6)). {
         mauto.
      }
      rewrite IVR. clear IVR.
      assert ((((R cwp) +ᵢ ($ 8)) -ᵢ ($ 1)) modu ($ 8) = ($6)). {
         int auto.
         rewrite <- Heqn.
         rewrite H.
         int auto.
      }
      rewrite IVR. clear IVR. auto.
      }
   }
   }
   }

  clear H3.
  clear IVR H2 MOV.
  rename GOAL into PRE_GOAL.
  assert (Q__ (Cu, Cs) (Mu, Ms_, (R_, F_)) [None;None;None;None;None;None;None;None] 8 (Mu, Ms', (R', F'))) as GOAL.
  {
    apply (No_Event (Cu,Cs) [None;None;None;None;None;None;None] 7 (Mu, Ms_, (R_, F_)) (Mu, Ms', (R', F')) (Mu, Ms, (R, F))); auto.
  }
  clear H.
  clear PRE_GOAL.
  clear INS.
  clear A.
  clear Ms R F.
  rename Ms' into Ms.
  rename R' into R.
  rename F' into F.

  remember ([None; None; None; None; None; None; None; None]) as L.
  exists (Mu, Ms, (R, F)) L.

  split.
  auto.
  apply H4.
Qed.
*)
