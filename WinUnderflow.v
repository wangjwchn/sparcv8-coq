Require Import Asm.
Require Import SMTC.Coqlib.
Require Import SMTC.Integers.
Require Import Property.
Require Import LibTactics.
Import ListNotations.
Local Open Scope sparc_scope.
Require Import IntAuto.
Require Import MathSol.
Require Import Coq.Logic.FunctionalExtensionality.

Require Import SMTC.Tactic.
Set SMT Solver "z3".
Set SMT Debug.

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

Definition underflow_handler := [
  rd wim l3;
  sll l3 ($1)ₙ l4;
  srl l3 (Asm.N-ᵢ($1))ₙ l5;
  or l5 l4 ᵣ l5;
  wr g0 l5 ᵣ wim;
  nop;
  nop;
  nop;
  restore g0 g0 ᵣ g0;
  restore g0 g0 ᵣ g0;
  ld sp ₐᵣ  l0;
  ld (sp+ₐₙ($4)) l1;
  ld (sp+ₐₙ($8)) l2;
  ld (sp+ₐₙ($12)) l3;
  ld (sp+ₐₙ($16)) l4;
  ld (sp+ₐₙ($20)) l5;
  ld (sp+ₐₙ($24)) l6;
  ld (sp+ₐₙ($28)) l7;
  ld (sp+ₐₙ($32)) i0;
  ld (sp+ₐₙ($36)) i1;
  ld (sp+ₐₙ($40)) i2;
  ld (sp+ₐₙ($44)) i3;
  ld (sp+ₐₙ($48)) i4;
  ld (sp+ₐₙ($52)) i5;
  ld (sp+ₐₙ($56)) i6;
  ld (sp+ₐₙ($60)) i7;
  save g0 g0 ᵣ g0;
  save g0 g0 ᵣ g0;
  jmpl l1 ₐᵣ g0;
  rett l2 ₐᵣ
].

Definition handler_context (R: RegFile) :=
 0 <= Int.unsigned (R#cwp) <= Int.unsigned(Asm.N)-1 /\ not_annuled_R R /\ trap_disabled_R R /\
  no_trap_R R /\  sup_mode_R R.

Definition single_mask : Word -> Word -> Prop :=
  fun cwp wim =>
    ($1) <<ᵢ cwp = wim.

Definition single_mask2:Word -> Word -> Prop :=
  fun cwp wim =>
    (($1) <<ᵢ ((cwp +ᵢ ($2)) modu (Asm.N))) = wim.

Definition memort_context : Word -> Memory -> Prop :=
  fun loc M =>
    exists v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16, 
    M loc = Some v1 /\ M (loc+ᵢ($4)) = Some v2 /\
    M (loc+ᵢ($8)) = Some v3 /\ M (loc+ᵢ($12)) = Some v4 /\
    M (loc+ᵢ($16)) = Some v5 /\ M (loc+ᵢ($20)) = Some v6 /\
    M (loc+ᵢ($24)) = Some v7 /\ M (loc+ᵢ($28)) = Some v8 /\
    M (loc+ᵢ($32)) = Some v9 /\ M (loc+ᵢ($36)) = Some v10 /\
    M (loc+ᵢ($40)) = Some v11 /\ M (loc+ᵢ($44)) = Some v12 /\
    M (loc+ᵢ($48)) = Some v13 /\ M (loc+ᵢ($52)) = Some v14 /\
    M (loc+ᵢ($56)) = Some v15 /\ M (loc+ᵢ($60)) = Some v16.

Definition align_context (Ms: Memory)(O: RState) :=
  let (R,F) := O in word_aligned_R R#l1 /\ word_aligned_R R#l2 /\ 
      let (R',F') := left_win 2 (R,F) in word_aligned_R R'#sp /\ memort_context R'#sp Ms.

Definition normal_cursor(O: RState) :=
  let (R,_) := O in R#npc = R#pc +ᵢ ($4).

Fixpoint set_function (w: Address) (F: Function)(C: CodeHeap)  : Prop :=
  match F with
  | i::F' => C w = Some i /\ set_function (w +ᵢ ($4)) F' C 
  | nil => True
  end.

Definition overflow_pre_cond : Cond :=
  fun W =>
    let (CP,S) := W in
    let (Cu,Cs) := CP in
    let '(MP,Q,D) := S in
    let (Mu,Ms) := MP in
    let (R,F) := Q in
    set_function (cursor_Q Q) underflow_handler Cs /\ normal_cursor Q /\
    handler_context R /\ align_context Ms Q /\ single_mask2 R#cwp R#wim /\ D = nil /\ f_context F.

Definition overflow_post_cond : Cond :=
  fun W =>
    let (CP,S) := W in
    let (Cu,Cs) := CP in
    let '(MP,Q,_) := S in
    let (R,F) := Q in
    single_mask (post_cwp 2 R) R#wim.

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

Lemma left_left_same :
  forall (i:GenReg) R1 R2 F R1' R2' F1 F2,
      f_context F ->
      left_win 2 (R1,F) = (R1',F1) ->
      left_win 2 (R2,F) = (R2',F2) ->
      R1' sp = R2' sp.
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
  unfold left_win in *.
  asserts_rewrite ((Z.to_nat 2) = 2%nat) in *. compute. auto.
  unfold left_iter in *.
  unfold left in *.
  unfold right in *.
  simpl in H0.
  inverts H0.
  simpl in H1.
  inverts H1.

  destruct i;
  substs;
  compute; auto.

Qed.

Lemma mask_cwp_post:
    forall R,
    0 <= Int.unsigned (R#cwp) <= 7 ->
    single_mask2 (post_cwp 1 R) (R#wim) ->
    win_masked (post_cwp 1 R) R = false.
Proof.
  unfold single_mask2.
  unfold win_masked.
  unfold post_cwp.
  unfold Asm.N.
  intros.
  remember (get_R cwp R) as cwp.
  remember (get_R wim R) as wim.
  clear R Heqcwp Heqwim.
  asserts_rewrite (((($ 1) <<ᵢ ((cwp +ᵢ ($ 1)) modu ($ 8))) &ᵢ wim) = ($ 0)). {
    smt solve.
    skip.
  }
  asserts_rewrite (($ 0) !=ᵢ ($ 0) = false). {
    mauto.
  }
  auto.
Admitted.


Lemma mask_cwp_post2:
    forall R,
    0 <= Int.unsigned (R#cwp) <= 7 ->
    single_mask2 (R#cwp) (R#wim) ->
    win_masked (post_cwp 1 R) R = false.
Proof.
  unfold single_mask2.
  unfold win_masked.
  unfold post_cwp.
  unfold Asm.N.
  intros.
  remember (get_R cwp R) as cwp.
  remember (get_R wim R) as wim.
  clear R Heqcwp Heqwim.
  asserts_rewrite (((($ 1) <<ᵢ ((cwp +ᵢ ($ 1)) modu ($ 8))) &ᵢ wim) = ($ 0)). {
    smt solve.
    skip.
  }
  asserts_rewrite (($ 0) !=ᵢ ($ 0) = false). {
    mauto.
  }
  auto.
Admitted.

Lemma mask_cwp_pre1:
    forall R,
    0 <= Int.unsigned (R#cwp) <= 7 ->
    single_mask (post_cwp 1 R) (get_R wim R) ->
    win_masked (pre_cwp 1 R) R = false.
Proof.
  unfold single_mask.
  unfold win_masked.
  unfold post_cwp.
  unfold pre_cwp.
  unfold Asm.N.
  intros.
  remember (get_R cwp R) as cwp.
  remember (get_R wim R) as wim.
  clear R Heqcwp Heqwim.
  rewrite <- H0.
  asserts_rewrite (((($ 1) <<ᵢ (((cwp +ᵢ ($ 8)) -ᵢ ($ 1)) modu ($ 8))) &ᵢ (($ 1) <<ᵢ ((cwp +ᵢ ($ 1)) modu ($ 8)))) = ($ 0)). {
    smt solve.
    skip.
  }
  asserts_rewrite (($ 0) !=ᵢ ($ 0) = false). {
    mauto.
  }
  auto.
Admitted.

Lemma Mask_When_Left:
  forall cwp n1 n2 n3 n4,
        0 <= Int.unsigned cwp <= 7 ->
        single_mask2 cwp n1 ->
        n2 = n1 <<ᵢ ($ 1) ->
        n3 = n1 >>ᵢ ($ 7) ->
        n4 = n3 |ᵢ n2 -> 
        single_mask2 ((cwp +ᵢ ($1)) modu Asm.N) (n4 &ᵢ ($ 255)).
Proof.
  unfold single_mask2.
  unfold Asm.N.
  unfold Word.
  intros.
  smt solve.
Admitted.

Lemma cwp_cycle_post:
  forall R,
      0 <= Int.unsigned (R#cwp) <= 7 ->
      0 <= Int.unsigned (post_cwp 1 R) <= 7.
Proof.
  unfold post_cwp.
  unfold Asm.N.
  intros.
  smt solve.
Admitted.

Lemma Left_Left_is_Left2:
  forall R Rl' R' Rl Rll F Fl' F' Fl Fll,
  f_context F ->
  (Rl', Fl') = left_win 1 (R, F) ->
  (get_R r30 Rl') = (get_R r30 R') ->
   F' = Fl' ->
  (Rl, Fl) = left_win 1 (R', F') ->
  (Rll, Fll) = left_win 2 (R, F) ->
  (get_R r14 Rll) = (get_R r14 Rl).
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
  unfold left_win in *.
  asserts_rewrite ((Z.to_nat 1) = 1%nat) in *. compute. auto.
  asserts_rewrite ((Z.to_nat 2) = 2%nat) in *. compute. auto.
  unfold left_iter in *.
  unfold left in *.
  substs.
  simpl in H0.
  inverts H0.
  simpl in H1.
  inverts H1.
  simpl in H3.
  inverts H3.
  simpl in H4.
  inverts H4.
  simpl.
  compute.
  compute in H.
  substs;
  compute; auto.
Qed.

Lemma Left1_Right2_is_Right1:
  forall R Rl R' Rr Rrr F Fl F' Fr Frr,
  f_context F ->
  (Rl, Fl) = left_win 1 (R, F) ->
  (get_R r17 Rl) = (get_R r17 R') /\ (get_R r18 Rl) = (get_R r18 R')->
  F' = Fl ->
  (Rrr, Frr) = right_win 2 (R', F') ->
  (Rr, Fr) = right_win 1 (R, F) ->
  (get_R r17 Rrr) = (get_R r17 Rr) /\ (get_R r18 Rrr) = (get_R r18 Rr).
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
  unfold left_win in *.
  unfold right_win in *.
  asserts_rewrite ((Z.to_nat 1) = 1%nat) in *. compute. auto.
  asserts_rewrite ((Z.to_nat 2) = 2%nat) in *. compute. auto.
  unfold right_iter in *.
  unfold left_iter in *.
  unfold right in *.
  unfold left in *.
  unfold fench in *.
  unfold replace in *.

  substs.
  simpl in H0.
  inverts H0.
  simpl in H1.
  inverts H1.
  simpl in H3.
  inverts H3.
  simpl in H4.
  inverts H4.
  simpl in H.
  simpl.
  compute.
  auto.
Qed.

Lemma Left_Right_is_Nothing:
  forall R R' Rl Rr F F' Fl Fr,
  f_context F ->
  (Rl, Fl) = left_win 1 (R, F) ->
  get_R r14 R' = get_R r14 Rl  /\ get_R r17 R' = get_R r17 Rl /\  get_R r18 R' = get_R r18 Rl ->
  F' = Fl ->
  (Rr, Fr) = right_win 1 (R', F') ->
  Rr#r14 = R#r14 /\ Rr#r17 = R#r17 /\ Rr#r18 = R#r18.
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
  unfold left_win in *.
  unfold right_win in *.
  asserts_rewrite ((Z.to_nat 1) = 1%nat) in *. compute. auto.
  unfold left_iter in *.
  unfold right_iter in *.
  unfold right in *.
  unfold left in *.
  unfold rev in *.
  unfold fench in *.
  unfold replace in *.
  substs.
  simpl in H0.
  inverts H0.
  simpl in H1.
  compute in H1.
  simpl in H3.
  inverts H3.
  compute.
  auto.
Qed. 


Lemma hold_context_right:
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


Lemma Post3_minus_1_is_2:
  forall R R',
  0 <= Int.unsigned R#cwp <= 7 ->
  single_mask2 (post_cwp 1 R) (get_R wim R) ->
  get_R cwp R' = post_cwp 1 R ->
  single_mask2 (get_R cwp R') (get_R wim R).
Proof.
  unfold single_mask2.
  unfold post_cwp.
  unfold Asm.N.
  intros.
  remember (get_R cwp R) as cwp.
  clear Heqcwp.
  remember ( get_R Asm.cwp R') as cwp'.
  clear Heqcwp'.
  remember (get_R wim R) as wim.
  clear Heqwim.
  clear R R'.
  sort.
  rewrite H1.
  smt solve; skip.
Qed.

Lemma Post2_minus_1_is_1:
  forall R R',
  0 <= Int.unsigned R#cwp <= 7 ->
  single_mask2 (get_R cwp R) (get_R wim R) ->
  get_R cwp R' = post_cwp 1 R ->
 single_mask (post_cwp 1 R') (get_R wim R).
Proof.
  unfold single_mask2.
  unfold single_mask.
  unfold post_cwp.
  unfold Asm.N.
  intros.
  remember (get_R cwp R) as cwp.
  clear Heqcwp.
  remember ( get_R Asm.cwp R') as cwp'.
  clear Heqcwp'.
  remember (get_R wim R) as wim.
  clear Heqwim.
  clear R R'.
  sort.
  rewrite H1.
  smt solve; skip.
Qed.

Lemma Right2_Right2_Same:
  forall R R' Rrr Rrr' F F' Frr Frr',
  f_context F->
  (Rrr, Frr) = right_win 2 (R, F) ->
  F' = F ->
  (Rrr', Frr') = right_win 2 (R', F') ->
  (get_R r17 Rrr') = (get_R r17 Rrr) /\ (get_R r18 Rrr') = (get_R r18 Rrr).
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

  unfold right_win in *.
  asserts_rewrite ((Z.to_nat 2) = 2%nat) in *. compute. auto.
  unfold right_iter in *.
  unfold right in *.
  unfold left in *.
  unfold fench in *.
  unfold replace in *.

  substs.
  simpl in H2.
  inverts H2.
  simpl in H0.
  inverts H0.
  compute.
  auto.
Qed.


Lemma align_plus4:
  forall w,
  word_aligned_R w ->
  word_aligned_R w +ᵢ ($4).
Proof.
  unfold word_aligned_R.
  unfold word_aligned.
  unfold get_range.
  intros.
  remember ((w &ᵢ (((($ 1) <<ᵢ ($ (1 - 0 + 1))) -ᵢ ($ 1)) <<ᵢ ($ 0))) =ᵢ ($ 0) ).
  destruct b; try inverts H.
  assert ((w &ᵢ (((($ 1) <<ᵢ ($ (1 - 0 + 1))) -ᵢ ($ 1)) <<ᵢ ($ 0)))  = ($ 0)). {
    smt solve; skip.
  }
  clear Heqb.
  asserts_rewrite(((w +ᵢ ($ 4)) &ᵢ (((($ 1) <<ᵢ ($ (1 - 0 + 1))) -ᵢ ($ 1)) <<ᵢ ($ 0))) = ($ 0)). {
    smt solve; skip.
  }
  asserts_rewrite(($ 0) =ᵢ ($ 0) = true). iauto. auto.
Qed.



Lemma Right_Right_is_Right2:
  forall R R' Rr Rr' Rrr F F' Fr Fr' Frr,
  f_context F ->
  (Rrr, Frr) = right_win 2 (R, F) ->
  F' = Fr ->
  (Rr, Fr) = right_win 1 (R, F) ->
  (Rr', Fr') = right_win 1 (R', F') ->
  (get_R r17 Rr') = (get_R r17 Rrr) /\ (get_R r18 Rr') = (get_R r18 Rrr).
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
  unfold right_win in *.
  asserts_rewrite ((Z.to_nat 2) = 2%nat) in *. compute. auto.
  asserts_rewrite ((Z.to_nat 1) = 1%nat) in *. compute. auto.
  unfold right_iter in *.
  unfold right in *.
  unfold left in *.
  unfold rev in *.
  unfold fench in *.
  unfold replace in *.
  substs.
  simpl in H2.
  inverts H2.
  simpl in H0.
  inverts H0.
  simpl in H3.
  inverts H3.
  compute.
  auto.
Qed. 



Lemma cwp_cycle_pre:
  forall R,
      0 <= Int.unsigned (R#cwp) <= 7 ->
      0 <= Int.unsigned (pre_cwp 1 R) <= 7.
Proof.
  unfold post_cwp.
  unfold Asm.N.
  intros.
  smt solve; skip.
Qed.


Lemma Post2_add_1_is_3:
  forall R R',
  single_mask2 (get_R cwp R) (get_R wim R) ->
  get_R cwp R' = pre_cwp 1 R ->
  single_mask2 (post_cwp 1 R') (get_R wim R).
Proof.
  unfold single_mask2.
  unfold single_mask.
  unfold post_cwp.
  unfold pre_cwp.
  unfold Asm.N.
  intros.
  remember (get_R cwp R) as cwp.
  clear Heqcwp.
  remember ( get_R Asm.cwp R') as cwp'.
  clear Heqcwp'.
  remember (get_R wim R) as wim.
  clear Heqwim.
  clear R R'.
  sort.
  rewrite H0.
  smt solve; skip.
Qed.



Lemma Post1_add_1_is_2:
  forall R R',
  single_mask (post_cwp 1 R) (get_R wim R) ->
  get_R cwp R' = pre_cwp 1 R ->
  single_mask2 (get_R cwp R') (get_R wim R).
Proof.
  unfold single_mask2.
  unfold single_mask.
  unfold post_cwp.
  unfold pre_cwp.
  unfold Asm.N.
  intros.
  remember (get_R cwp R) as cwp.
  clear Heqcwp.
  remember ( get_R Asm.cwp R') as cwp'.
  clear Heqcwp'.
  remember (get_R wim R) as wim.
  clear Heqwim.
  clear R R'.
  sort.
  rewrite H0.
  smt solve; skip.
Qed.



Lemma mask_cwp_post3:
    forall R,
    0 <= Int.unsigned (R#cwp) <= 7 ->
    single_mask2 (post_cwp 1 R) (get_R wim R) ->
    win_masked (post_cwp 1 R) R = false.
Proof.
  unfold single_mask2.
  unfold win_masked.
  unfold post_cwp.
  unfold Asm.N.
  intros.
  remember (get_R cwp R) as cwp.
  remember (get_R wim R) as wim.
  clear R Heqcwp Heqwim.
  asserts_rewrite (((($ 1) <<ᵢ ((cwp +ᵢ ($ 1)) modu ($ 8))) &ᵢ wim) = ($ 0)). {
  smt solve; skip.
  }
  asserts_rewrite (($ 0) !=ᵢ ($ 0) = false). {
    mauto.
  }
  auto.
Qed.


Lemma mask_cwp_pre2:
    forall R,
    0 <= Int.unsigned (R#cwp) <= 7 ->
    single_mask2 (get_R cwp R) (get_R wim R) ->
    win_masked (pre_cwp 1 R) R = false.
Proof.
  unfold single_mask2.
  unfold single_mask.
  unfold win_masked.
  unfold post_cwp.
  unfold pre_cwp.
  unfold Asm.N.
  intros.
  remember (get_R cwp R) as cwp.
  remember (get_R wim R) as wim.
  clear R Heqcwp Heqwim.
  rewrite <- H0.
  asserts_rewrite ((($ 1) <<ᵢ (((cwp +ᵢ ($ 8)) -ᵢ ($ 1)) modu ($ 8))) &ᵢ (($ 1) <<ᵢ ((cwp +ᵢ ($ 2)) modu ($ 8))) = ($ 0)). {
    smt solve; skip.
  }
  asserts_rewrite (($ 0) !=ᵢ ($ 0) = false). {
    mauto.
  }
  auto.
Qed.

Theorem HandleUnderflow:
  forall CP S,
    overflow_pre_cond (CP,S) ->
    exists S' E ,Z__ CP S E 30 S'/\
    overflow_post_cond (CP,S') /\ no_trap E.
Proof.
  intros.
  unfolds in H.
  destruct CP as (Cu & Cs).
  destruct S as (MPQ & D).
  destruct MPQ as (MP & Q).
  destruct MP as (Mu & Ms).
  destruct Q as (R & F).
  destruct H as (FUNC & CSR & IVR & ALIGN & MASK & DELAY & CONT).



(* step 1 *)

  assert (not_abort Cs Ms (R,F) D) as NA. {
    unfolds.
    exists (R,F) D (rd wim r19).
    splits.
    - substs. auto.
    - apply FUNC.
    - unfolds. auto.
  }

  (* to P__ *)
  assert
  (exists Ms' Q' D', P__ (Cu,Cs) ((Mu,Ms),(R,F),D) ((Mu,Ms'),Q',D')) as H. {
    apply (Exists_P_Sup Cu Cs Mu Ms (R,F) D);
    auto; try apply IVR.
  }
  destruct H as (Ms' & Q' & D' & P__).
  destruct Q' as (R' & F').
  clear NA.

  (* deal with delay *)
  rewrite DELAY in *.

  (* small changes in one step *)
  assert (R'#pc = R#npc /\ R'#npc = R#npc +ᵢ ($4) /\ 
          R'#cwp = R#cwp /\ R'#annul = R#annul /\ R'#et = R#et /\ R'#trap = R#trap /\ R'#s = R#s /\ R'#wim = R#wim /\
          R'#l3 = R#wim /\ R'#l1 = R#l1 /\ R'#l2 = R#l2 /\ R'#sp = R#sp /\ F' = F /\ D' = D /\ Ms' = Ms). {
  inverts P__.
  (* usr_mode *) {
    false. apply (ModeDeq (R,F)); auto.
    apply IVR.
  }
  (* sup_mode *) {
    inverts H10.
    unfolds in H6.
    inverts H6.
    assert (Cs (cursor_Q (R, F)) = Some (rd wim r19)) as INS. {
    apply FUNC.
    }
    rewrite H11 in INS.
    clear H11. inverts INS.

    {
    inverts H12; try solve [false].
    inverts H5; try solve [false].
    inverts H6; repeat (split; auto); auto.
    (* unexpected_trap? no! *)
    unfold unexpected_trap in *.
    unfold trap_type in *.
    assert (usr_mode R = false). apply IVR.
    rewrite H in *. false.
    }

    (* annul? no !*){
    inverts H5.
    false.
    apply (AnnulDeq R).
    apply H8. apply IVR.
    }
  }
  }

  assert (R'#pc = R#pc +ᵢ ($4) /\ normal_cursor (R',F')) as CSR'. {
    splits.
      asserts_rewrite (get_R pc R' = get_R npc R). iauto. apply CSR.
      unfolds.
        asserts_rewrite (get_R npc R' = (get_R npc R) +ᵢ ($ 4)). iauto.
        asserts_rewrite (get_R pc R'  = get_R npc R). iauto.
        auto.
  }


  {
  assert (handler_context R') as IVR'. {
    unfolds.
    splits; try unfolds; try unfolds;
    try asserts_rewrite ((get_R cwp R') = (get_R cwp R));
    try asserts_rewrite ((get_R annul R') = (get_R annul R)); 
    try asserts_rewrite ((get_R et R') = (get_R et R));
    try asserts_rewrite ((get_R trap R') = (get_R trap R));
    try asserts_rewrite ((get_R s R') = (get_R s R));
    iauto; apply IVR.
  }

  assert (align_context Ms' (R',F')) as ALIGN'. {
    unfolds.
    splits; try unfolds; try unfolds;
    try asserts_rewrite (get_R r17 R' = get_R r17 R);
    try asserts_rewrite (get_R r18 R' = get_R r18 R); 
    try asserts_rewrite (get_R r30 R' = get_R r30 R);
    try asserts_rewrite (Ms' = Ms);
    iauto; try apply ALIGN.
    {
      unfolds in ALIGN.
      unfold get_R.
      remember (left_win 2 (R, F)).
      destruct r as (R1 & F1).
      remember (left_win 2 (R', F')).
      destruct r as (R2 & F2).
      asserts_rewrite(F' = F) in Heqr0. iauto.
      unfold get_R in ALIGN.
      asserts_rewrite (R1 sp = R2 sp) in ALIGN. {
        apply (left_left_same sp R R' F R1 R2 F1 F2); iauto.
      }
      splits; iauto.
    }
  }

  assert (single_mask2 R'#cwp R'#wim /\ single_mask2 (get_R cwp R') (get_R l3 R') ) as MASK'. {
    asserts_rewrite ((get_R cwp R') = (get_R cwp R)). iauto.
    asserts_rewrite (get_R wim R' = get_R wim R). iauto.
    asserts_rewrite ((get_R l3 R') = (get_R wim R)). iauto.
    splits;
    apply MASK.
  }

  assert (D' = []) as DELAY'. {
    asserts_rewrite (D' = D). iauto. iauto.
  }

  assert (f_context F') as CONT'. {
    asserts_rewrite (F' = F). iauto. iauto.
  }

  assert (Z__ (Cu, Cs) (Mu, Ms, (R, F),D) [None] 1 (Mu, Ms', (R', F'),D')) as GOAL'. {
    assert (Z__ (Cu, Cs) (Mu, Ms, (R, F),D) nil 0 (Mu, Ms, (R, F),D)).
    apply Zero.
    apply (No_Event (Cu,Cs) nil 0 (Mu, Ms, (R, F),D) (Mu, Ms', (R', F'),D') (Mu, Ms, (R, F),D));
    try rewrite DELAY in *; auto.
  }
  rename Ms into Ms_.
  rename R into R_.
  rename F into F_.
  rename D into D_.
  rename Ms' into Ms.
  rename R' into R.
  rename F' into F.
  rename D' into D.
  rewrite DELAY in GOAL'.
  clear H P__ IVR MASK CSR DELAY ALIGN CONT.
  rename IVR' into IVR.
  rename MASK' into MASK.
  rename CSR' into CSR.
  rename DELAY' into DELAY.
  rename GOAL' into GOAL.
  rename ALIGN' into ALIGN.
  rename CONT' into CONT.





(* step 2 *)

  assert (not_abort Cs Ms (R,F) D) as NA. {
    unfolds.
    exists (R,F) D  (sll l3 ($1)ₙ l4).
    splits.
    - substs. auto.
    - asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4)); iauto. apply FUNC.
    - unfolds. auto.
  }

  (* to P__ *)
  assert
  (exists Ms' Q' D', P__ (Cu,Cs) ((Mu,Ms),(R,F),D) ((Mu,Ms'),Q',D')) as H. {
    apply (Exists_P_Sup Cu Cs Mu Ms (R,F) D);
    auto; try apply IVR.
  }
  destruct H as (Ms' & Q' & D' & P__).
  destruct Q' as (R' & F').
  clear NA.

  (* deal with delay *)
  rewrite DELAY in *.

  (* small changes in one step *)
  assert (R'#pc = R#npc /\ R'#npc = R#npc +ᵢ ($4) /\
          R'#cwp = R#cwp /\ R'#annul = R#annul /\ R'#et = R#et /\ R'#trap = R#trap /\ R'#s = R#s /\ R'#wim = R#wim /\
          R'#l3 = R#l3 /\ R'#l4 = R#l3 <<ᵢ ($1) /\ R'#l1 = R#l1 /\ R'#l2 = R#l2 /\ R'#fp = R#fp /\ F' = F /\ D' = D /\ Ms' = Ms). {
  inverts P__.
  (* usr_mode *) {
    false. apply (ModeDeq (R,F)); auto.
    apply IVR.
  }
  (* sup_mode *) {
    inverts H10.
    unfolds in H6.
    inverts H6.
    assert (Cs (cursor_Q (R, F)) = Some (sll l3 ($1)ₙ l4)) as INS. {
    asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4)). iauto.
    apply FUNC.
    }
    rewrite H11 in INS.
    clear H11. inverts INS.

    {
    inverts H12; try solve [false].
    inverts H5; try solve [false].
    inverts H4; repeat (split; auto); auto.
    unfold eval_OpExp in *.
    destruct (($ (-4096)) <=ᵢ ($ 1) && ($ 1) <=ᵢ ($ 4095));
    try inverts H7.
    auto.
    }

    (* annul? no !*){
    inverts H5.
    false.
    apply (AnnulDeq R).
    apply H8. apply IVR.
    }
  }
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

  {
  assert (handler_context R') as IVR'. {
    unfolds.
    splits; try unfolds; try unfolds;
    try asserts_rewrite ((get_R cwp R') = (get_R cwp R));
    try asserts_rewrite ((get_R annul R') = (get_R annul R)); 
    try asserts_rewrite ((get_R et R') = (get_R et R));
    try asserts_rewrite ((get_R trap R') = (get_R trap R));
    try asserts_rewrite ((get_R s R') = (get_R s R));
    iauto; apply IVR.
  }

  assert (align_context Ms' (R',F')) as ALIGN'. {
    unfolds.
    splits; try unfolds; try unfolds;
    try asserts_rewrite (get_R r17 R' = get_R r17 R);
    try asserts_rewrite (get_R r18 R' = get_R r18 R); 
    try asserts_rewrite (get_R r30 R' = get_R r30 R);
    try asserts_rewrite (Ms' = Ms);
    iauto; try apply ALIGN.
    {
      unfolds in ALIGN.
      unfold get_R.
      remember (left_win 2 (R, F)).
      destruct r as (R1 & F1).
      remember (left_win 2 (R', F')).
      destruct r as (R2 & F2).
      asserts_rewrite(F' = F) in Heqr0. iauto.
      unfold get_R in ALIGN.
      asserts_rewrite (R1 sp = R2 sp) in ALIGN. {
        apply (left_left_same sp R R' F R1 R2 F1 F2); iauto.
      } iauto.
    }
  }


  assert (single_mask2 R'#cwp R'#wim /\ single_mask2 (R'#cwp) (R'#l3) /\
          (R'#l4) = (R'#l3) <<ᵢ ($ 1)) as MASK'. {
    splits.
    {
    asserts_rewrite (get_R cwp R' = get_R cwp R). iauto.
    asserts_rewrite (get_R wim R' = get_R wim R). iauto.
    apply MASK.
    }
    {
    asserts_rewrite (get_R l3 R' = get_R l3 R). iauto.
    asserts_rewrite (get_R cwp R' = get_R cwp R). iauto.
    apply MASK.
    }
    {
      asserts_rewrite (get_R l3 R' = get_R l3 R). iauto.
      apply H.
    }
  }

  assert (D' = []) as DELAY'. {
    asserts_rewrite (D' = D). iauto. iauto.
  }

  assert (f_context F') as CONT'. {
    asserts_rewrite (F' = F). iauto. iauto.
  }

  assert (Z__ (Cu, Cs) (Mu, Ms_, (R_, F_),[]) [None;None] 2 (Mu, Ms', (R', F'),D')) as GOAL'. {
    apply (No_Event (Cu,Cs) [None] 1 (Mu, Ms_, (R_, F_),[]) (Mu, Ms', (R', F'),D') (Mu, Ms, (R, F),D));
    try rewrite DELAY in *; auto.
  }
  clear H P__ IVR MASK CSR DELAY ALIGN GOAL CONT.
  clear Ms R F D.
  rename Ms' into Ms.
  rename R' into R.
  rename F' into F.
  rename D' into D.
  rename IVR' into IVR.
  rename MASK' into MASK.
  rename CSR' into CSR.
  rename DELAY' into DELAY.
  rename GOAL' into GOAL.
  rename ALIGN' into ALIGN.
  rename CONT' into CONT.


(* step 3 *)

  assert (not_abort Cs Ms (R,F) D) as NA. {
    unfolds.
    exists (R,F) D  (srl l3 (Asm.N-ᵢ($1))ₙ l5).
    splits.
    - substs. auto.
    - asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4)); iauto. apply FUNC.
    - unfolds. auto.
  }

  (* to P__ *)
  assert
  (exists Ms' Q' D', P__ (Cu,Cs) ((Mu,Ms),(R,F),D) ((Mu,Ms'),Q',D')) as H. {
    apply (Exists_P_Sup Cu Cs Mu Ms (R,F) D);
    auto; try apply IVR.
  }
  destruct H as (Ms' & Q' & D' & P__).
  destruct Q' as (R' & F').
  clear NA.

  (* deal with delay *)
  rewrite DELAY in *.

  (* small changes in one step *)
  assert (R'#pc = R#npc /\ R'#npc = R#npc +ᵢ ($4) /\
          R'#cwp = R#cwp /\ R'#annul = R#annul /\ R'#et = R#et /\ R'#trap = R#trap /\ R'#s = R#s /\ R'#wim = R#wim /\
          R'#l3 = R#l3 /\ R'#l4 = R#l4 /\ R'#l5 = R#l3 >>ᵢ ($7) /\ 
          R'#g1 = R#g1 /\ R'#l1 = R#l1 /\ R'#l2 = R#l2 /\ R'#fp = R#fp /\ F' = F /\ D' = D /\ Ms' = Ms). {
  inverts P__.
  (* usr_mode *) {
    false. apply (ModeDeq (R,F)); auto.
    apply IVR.
  }
  (* sup_mode *) {
    inverts H10.
    unfolds in H6.
    inverts H6.
    assert (Cs (cursor_Q (R, F)) = Some (srl l3 (Asm.N-ᵢ($1))ₙ l5)) as INS. {
    asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4)). iauto.
    apply FUNC.
    }
    rewrite H11 in INS.
    clear H11. inverts INS.

    {
    inverts H12; try solve [false].
    inverts H5; try solve [false].
    inverts H4; repeat (split; auto); auto.
    unfold eval_OpExp in *.
    unfold Asm.N in *.
    destruct (($ (-4096)) <=ᵢ (($ 8) -ᵢ ($ 1)) && (($ 8) -ᵢ ($ 1)) <=ᵢ ($ 4095));
    try inverts H7.
    auto.
    }

    (* annul? no !*){
    inverts H5.
    false.
    apply (AnnulDeq R).
    apply H8. apply IVR.
    }
  }
  }

  assert (R'#pc = R_#pc +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) /\ normal_cursor (R',F')) as CSR'. {
    splits. {
      asserts_rewrite (get_R pc R' = get_R npc R). iauto.
      asserts_rewrite (get_R npc R = (get_R pc R) +ᵢ ($ 4)). apply CSR.
      asserts_rewrite (get_R pc R = (get_R pc R_) +ᵢ ($ 4) +ᵢ ($ 4)). apply CSR.
      auto.
    }
    {
      unfolds.
        asserts_rewrite (get_R npc R' = (get_R npc R) +ᵢ ($ 4)). iauto.
        asserts_rewrite (get_R pc R'  = get_R npc R). iauto.
        auto.
    }
  }

  {
  assert (handler_context R') as IVR'. {
    unfolds.
    splits; try unfolds; try unfolds;
    try asserts_rewrite ((get_R cwp R') = (get_R cwp R));
    try asserts_rewrite ((get_R annul R') = (get_R annul R)); 
    try asserts_rewrite ((get_R et R') = (get_R et R));
    try asserts_rewrite ((get_R trap R') = (get_R trap R));
    try asserts_rewrite ((get_R s R') = (get_R s R));
    iauto; apply IVR.
  }

  assert (align_context Ms' (R',F')) as ALIGN'. {
    unfolds.
    splits; try unfolds; try unfolds;
    try asserts_rewrite (get_R r17 R' = get_R r17 R);
    try asserts_rewrite (get_R r18 R' = get_R r18 R); 
    try asserts_rewrite (get_R r30 R' = get_R r30 R);
    try asserts_rewrite (Ms' = Ms);
    iauto; try apply ALIGN.
    {
      unfolds in ALIGN.
      unfold get_R.
      remember (left_win 2 (R, F)).
      destruct r as (R1 & F1).
      remember (left_win 2 (R', F')).
      destruct r as (R2 & F2).
      asserts_rewrite(F' = F) in Heqr0. iauto.
      unfold get_R in ALIGN.
      asserts_rewrite (R1 sp = R2 sp) in ALIGN. {
        apply (left_left_same sp R R' F R1 R2 F1 F2); iauto.
      } iauto.
    }
  }

  assert (single_mask2 R'#cwp R'#wim /\ single_mask2 R'#cwp R'#l3 /\ R'#l4 = R'#l3 <<ᵢ ($ 1) /\ R'#l5 = R'#l3 >>ᵢ ($ 7)) as MASK'. {
    splits.
    {
    asserts_rewrite (get_R wim R' = get_R wim R). iauto.
    asserts_rewrite (get_R cwp R' = get_R cwp R). iauto.
    apply MASK.
    }
    {
    asserts_rewrite (get_R l3 R' = (get_R l3 R)). iauto.
    asserts_rewrite (get_R cwp R' = get_R cwp R). iauto.
    apply MASK.
    }
    {
    asserts_rewrite (get_R l4 R' = (get_R l4 R)). iauto.
    asserts_rewrite (get_R l3 R' = (get_R l3 R)). iauto.
    apply MASK.
    }
    {
      asserts_rewrite (get_R l5 R' = (get_R l3 R) >>ᵢ ($ 7)). iauto.
      asserts_rewrite (get_R l3 R' = (get_R l3 R)). iauto.
      auto.
    }
  }

  assert (D' = []) as DELAY'. {
    asserts_rewrite (D' = D). iauto. iauto.
  }

  assert (f_context F') as CONT'. {
    asserts_rewrite (F' = F). iauto. iauto.
  }

  assert (Z__ (Cu, Cs) (Mu, Ms_, (R_, F_),[]) [None;None;None] 3 (Mu, Ms', (R', F'),D')) as GOAL'. {
    apply (No_Event (Cu,Cs) [None;None] 2 (Mu, Ms_, (R_, F_),[]) (Mu, Ms', (R', F'),D') (Mu, Ms, (R, F),D));
    try rewrite DELAY in *; auto.
  }
  clear H P__ IVR MASK CSR DELAY ALIGN GOAL CONT.
  clear Ms R F D.
  rename Ms' into Ms.
  rename R' into R.
  rename F' into F.
  rename D' into D.
  rename IVR' into IVR.
  rename MASK' into MASK.
  rename CSR' into CSR.
  rename DELAY' into DELAY.
  rename GOAL' into GOAL.
  rename ALIGN' into ALIGN.
  rename CONT' into CONT.



(* step 4 *)

  assert (not_abort Cs Ms (R,F) D) as NA. {
    unfolds.
    exists (R,F) D  (or l5 l4 ᵣ l5).
    splits.
    - substs. auto.
    - asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)); iauto. apply FUNC.
    - unfolds. auto.
  }

  (* to P__ *)
  assert
  (exists Ms' Q' D', P__ (Cu,Cs) ((Mu,Ms),(R,F),D) ((Mu,Ms'),Q',D')) as H. {
    apply (Exists_P_Sup Cu Cs Mu Ms (R,F) D);
    auto; try apply IVR.
  }
  destruct H as (Ms' & Q' & D' & P__).
  destruct Q' as (R' & F').
  clear NA.

  (* deal with delay *)
  rewrite DELAY in *.

  (* small changes in one step *)
  assert (R'#pc = R#npc /\ R'#npc = R#npc +ᵢ ($4) /\
          R'#cwp = R#cwp /\ R'#annul = R#annul /\ R'#et = R#et /\ R'#trap = R#trap /\ R'#s = R#s /\ R'#wim = R#wim /\
          R'#l5 = R#l5 |ᵢ (R#l4) /\ R'#l1 = R#l1 /\ R'#l2 = R#l2 /\ R'#fp = R#fp /\ F' = F /\ D' = D /\ Ms' = Ms). {
  inverts P__.
  (* usr_mode *) {
    false. apply (ModeDeq (R,F)); auto.
    apply IVR.
  }
  (* sup_mode *) {
    inverts H10.
    unfolds in H6.
    inverts H6.
    assert (Cs (cursor_Q (R, F)) = Some (or l5 l4 ᵣ l5)) as INS. {
    asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)). iauto.
    apply FUNC.
    }
    rewrite H11 in INS.
    clear H11. inverts INS.

    {
    inverts H12; try solve [false].
    inverts H5; try solve [false].
    inverts H4; repeat (split; auto); auto.
    unfold eval_OpExp in *.
    try inverts H7.
    auto.
    }

    (* annul? no !*){
    inverts H5.
    false.
    apply (AnnulDeq R).
    apply H8. apply IVR.
    }
  }
  }

  assert (R'#pc = R_#pc +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) /\ normal_cursor (R',F')) as CSR'. {
    splits. {
      asserts_rewrite (get_R pc R' = get_R npc R). iauto.
      asserts_rewrite (get_R npc R = (get_R pc R) +ᵢ ($ 4)). apply CSR.
      asserts_rewrite (get_R pc R = (get_R pc R_) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($4)). apply CSR.
      auto.
    }
    {
      unfolds.
        asserts_rewrite (get_R npc R' = (get_R npc R) +ᵢ ($ 4)). iauto.
        asserts_rewrite (get_R pc R'  = get_R npc R). iauto.
        auto.
    }
  }

  {
  assert (handler_context R') as IVR'. {
    unfolds.
    splits; try unfolds; try unfolds;
    try asserts_rewrite ((get_R cwp R') = (get_R cwp R));
    try asserts_rewrite ((get_R annul R') = (get_R annul R)); 
    try asserts_rewrite ((get_R et R') = (get_R et R));
    try asserts_rewrite ((get_R trap R') = (get_R trap R));
    try asserts_rewrite ((get_R s R') = (get_R s R));
    iauto; apply IVR.
  }

  assert (align_context Ms' (R',F')) as ALIGN'. {
    unfolds.
    splits; try unfolds; try unfolds;
    try asserts_rewrite (get_R r17 R' = get_R r17 R);
    try asserts_rewrite (get_R r18 R' = get_R r18 R); 
    try asserts_rewrite (get_R r30 R' = get_R r30 R);
    try asserts_rewrite (Ms' = Ms);
    iauto; try apply ALIGN.
    {
      unfolds in ALIGN.
      unfold get_R.
      remember (left_win 2 (R, F)).
      destruct r as (R1 & F1).
      remember (left_win 2 (R', F')).
      destruct r as (R2 & F2).
      asserts_rewrite(F' = F) in Heqr0. iauto.
      unfold get_R in ALIGN.
      asserts_rewrite (R1 sp = R2 sp) in ALIGN. {
        apply (left_left_same sp R R' F R1 R2 F1 F2); iauto.
      } iauto.
    }
  }

  assert (single_mask2 R'#cwp (R'#wim) /\ single_mask2 (post_cwp 1 R')(R'#l5&ᵢ($255))) as MASK'. {
    split.
    {
      asserts_rewrite (get_R cwp R' = get_R cwp R). iauto.
      asserts_rewrite (get_R wim R' = get_R wim R). iauto.
      apply MASK.
    }
    {
    unfold post_cwp.
    apply (Mask_When_Left (get_R cwp R') R#r19 R#r20 R#r21 R'#r21); iauto.
    asserts_rewrite (get_R cwp R' = get_R cwp R). iauto. apply IVR.
    asserts_rewrite (get_R cwp R' = get_R cwp R). iauto. apply MASK.
    }
  }

  assert (D' = []) as DELAY'. {
    asserts_rewrite (D' = D). iauto. iauto.
  }

  assert (f_context F') as CONT'. {
    asserts_rewrite (F' = F). iauto. iauto.
  }

  assert (Z__ (Cu, Cs) (Mu, Ms_, (R_, F_),[]) [None;None;None;None] 4 (Mu, Ms', (R', F'),D')) as GOAL'. {
    apply (No_Event (Cu,Cs) [None;None;None] 3 (Mu, Ms_, (R_, F_),[]) (Mu, Ms', (R', F'),D') (Mu, Ms, (R, F),D));
    try rewrite DELAY in *; auto.
  }
  clear H P__ IVR MASK CSR DELAY ALIGN GOAL CONT.
  clear Ms R F D.
  rename Ms' into Ms.
  rename R' into R.
  rename F' into F.
  rename D' into D.
  rename IVR' into IVR.
  rename MASK' into MASK.
  rename CSR' into CSR.
  rename DELAY' into DELAY.
  rename GOAL' into GOAL.
  rename ALIGN' into ALIGN.
  rename CONT' into CONT.



(* step 5 *)

  assert (not_abort Cs Ms (R,F) D) as NA. {
    unfolds.
    exists (R,F) D  (wr g0 l5 ᵣ wim).
    splits.
    - substs. auto.
    - asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)); iauto. apply FUNC.
    - unfolds. auto.
  }

  (* to P__ *)
  assert
  (exists Ms' Q' D', P__ (Cu,Cs) ((Mu,Ms),(R,F),D) ((Mu,Ms'),Q',D')) as H. {
    apply (Exists_P_Sup Cu Cs Mu Ms (R,F) D);
    auto; try apply IVR.
  }
  destruct H as (Ms' & Q' & D' & P__).
  destruct Q' as (R' & F').
  clear NA.

  (* deal with delay *)
  rewrite DELAY in *.

  (* small changes in one step *)
  assert (R'#pc = R#npc /\ R'#npc = R#npc +ᵢ ($4) /\
          R'#cwp = R#cwp /\ R'#annul = R#annul /\ R'#et = R#et /\ R'#trap = R#trap /\ R'#s = R#s /\ R'#wim = R#wim /\
          R'#l5 = R#l5 /\ R'#sp = R#sp /\ R'#l1 = R#l1 /\ R'#l2 = R#l2  /\ F' = F /\ D' = [(2%nat, wim, R l5)] /\ Ms' = Ms). {
  inverts P__.
  (* usr_mode *) {
    false. apply (ModeDeq (R,F)); auto.
    apply IVR.
  }
  (* sup_mode *) {
    inverts H10.
    unfolds in H6.
    inverts H6.
    assert (Cs (cursor_Q (R, F)) = Some (wr g0 l5 ᵣ wim)) as INS. {
    asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) ). iauto.
    apply FUNC.
    }
    rewrite H11 in INS.
    clear H11. inverts INS.

    {
    inverts H12; try solve [false].
    inverts H5; try solve [false].
    inverts H10; try solve [false].
    repeat (split; auto); auto.
    simpl. unfold set_delay.
    unfold eval_OpExp in *.
    try inverts H15.
    asserts_rewrite (($ 0) xor (R l5) = R l5).
    apply Int.xor_zero_l. unfold X.
    auto.
    unfold unexpected_trap in *.
    unfold trap_type in *.
    asserts_rewrite (usr_mode R = false) in H4. apply IVR.
    inverts H4.
    }

    (* annul? no !*){
    inverts H5.
    false.
    apply (AnnulDeq R).
    apply H8. apply IVR.
    }
  }
  }

  assert (R'#pc = R_#pc +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)  /\ normal_cursor (R',F')) as CSR'. {
    splits. {
      asserts_rewrite (get_R pc R' = get_R npc R). iauto.
      asserts_rewrite (get_R npc R = (get_R pc R) +ᵢ ($ 4)). apply CSR.
      asserts_rewrite (get_R pc R = (get_R pc R_) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($4)). apply CSR.
      auto.
    }
    {
      unfolds.
        asserts_rewrite (get_R npc R' = (get_R npc R) +ᵢ ($ 4)). iauto.
        asserts_rewrite (get_R pc R'  = get_R npc R). iauto.
        auto.
    }
  }

  {
  assert (handler_context R') as IVR'. {
    unfolds.
    splits; try unfolds; try unfolds;
    try asserts_rewrite ((get_R cwp R') = (get_R cwp R));
    try asserts_rewrite ((get_R annul R') = (get_R annul R)); 
    try asserts_rewrite ((get_R et R') = (get_R et R));
    try asserts_rewrite ((get_R trap R') = (get_R trap R));
    try asserts_rewrite ((get_R s R') = (get_R s R));
    iauto; apply IVR.
  }

  assert (align_context Ms' (R',F')) as ALIGN'. {
    unfolds.
    splits; try unfolds; try unfolds;
    try asserts_rewrite (get_R r17 R' = get_R r17 R);
    try asserts_rewrite (get_R r18 R' = get_R r18 R); 
    try asserts_rewrite (get_R r30 R' = get_R r30 R);
    try asserts_rewrite (Ms' = Ms);
    iauto; try apply ALIGN.
    {
      unfolds in ALIGN.
      unfold get_R.
      remember (left_win 2 (R, F)).
      destruct r as (R1 & F1).
      remember (left_win 2 (R', F')).
      destruct r as (R2 & F2).
      asserts_rewrite(F' = F) in Heqr0. iauto.
      unfold get_R in ALIGN.
      asserts_rewrite (R1 sp = R2 sp) in ALIGN. {
        apply (left_left_same sp R R' F R1 R2 F1 F2); iauto.
      } iauto.
    }
  }

  assert (single_mask2  (post_cwp 1 R') (R'#l5&ᵢ($255))) as MASK'. {
    unfold post_cwp.
    asserts_rewrite (get_R cwp R' = get_R cwp R). iauto.
    asserts_rewrite (get_R l5 R' = get_R l5 R). iauto.
    apply MASK.
  }

  assert (D' = [(2%nat, wim, R' l5)]) as DELAY'. {
    asserts_rewrite (R' l5 = get_R l5 R). iauto.
    iauto.
  }

  assert (f_context F') as CONT'. {
    asserts_rewrite (F' = F). iauto. iauto.
  }

  assert (Z__ (Cu, Cs) (Mu, Ms_, (R_, F_),[]) [None;None;None;None;None] 5 (Mu, Ms', (R', F'),D')) as GOAL'. {
    apply (No_Event (Cu,Cs) [None;None;None;None] 4 (Mu, Ms_, (R_, F_),[]) (Mu, Ms', (R', F'),D') (Mu, Ms, (R, F),D));
    try rewrite DELAY in *; auto.
  }
  clear H P__ IVR MASK CSR DELAY ALIGN GOAL CONT.
  clear Ms R F D.
  rename Ms' into Ms.
  rename R' into R.
  rename F' into F.
  rename D' into D.
  rename IVR' into IVR.
  rename MASK' into MASK.
  rename CSR' into CSR.
  rename DELAY' into DELAY.
  rename GOAL' into GOAL.
  rename ALIGN' into ALIGN.
  rename CONT' into CONT.


(* step 6 *)

  assert (not_abort Cs Ms (R,F) D) as NA. {
    unfolds.
    exists (R,F) [(1%nat, wim, R l5)] (nop).
    splits.
    - substs. auto.
    - asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)); iauto. apply FUNC.
    - unfolds. auto.
  }

  (* to P__ *)
  assert
  (exists Ms' Q' D', P__ (Cu,Cs) ((Mu,Ms),(R,F),D) ((Mu,Ms'),Q',D')) as H. {
    apply (Exists_P_Sup Cu Cs Mu Ms (R,F) D);
    auto; try apply IVR.
  }
  destruct H as (Ms' & Q' & D' & P__).
  destruct Q' as (R' & F').
  clear NA.

  (* deal with delay *)
  rewrite DELAY in *.

  (* small changes in one step *)
  assert (R'#pc = R#npc /\ R'#npc = R#npc +ᵢ ($4) /\
          R'#cwp = R#cwp /\ R'#annul = R#annul /\ R'#et = R#et /\ R'#trap = R#trap /\ R'#s = R#s /\ R'#wim = R#wim /\
          R'#l5 = R#l5 /\ R'#sp = R#sp /\ R'#l1 = R#l1 /\ R'#l2 = R#l2  /\ F' = F /\ D' = [(1%nat, wim, R l5)] /\ Ms' = Ms). {
  inverts P__.
  (* usr_mode *) {
    false. apply (ModeDeq (R,F)); auto.
    apply IVR.
  }
  (* sup_mode *) {
    inverts H10.
    unfolds in H6.
    inverts H6.
    assert (Cs (cursor_Q (R, F)) = Some (nop)) as INS. {
    asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4)). iauto.
    apply FUNC.
    }
    rewrite H11 in INS.
    clear H11. inverts INS.

    {
    inverts H12; try solve [false].
    inverts H5; try solve [false].
    repeat (split; auto); auto.
    }

    (* annul? no !*){
    inverts H5.
    false.
    apply (AnnulDeq R).
    apply H8. apply IVR.
    }
  }
  }

  assert (R'#pc = R_#pc +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) /\ normal_cursor (R',F')) as CSR'. {
    splits. {
      asserts_rewrite (get_R pc R' = get_R npc R). iauto.
      asserts_rewrite (get_R npc R = (get_R pc R) +ᵢ ($ 4)). apply CSR.
      asserts_rewrite (get_R pc R = (get_R pc R_) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)). apply CSR.
      auto.
    }
    {
      unfolds.
        asserts_rewrite (get_R npc R' = (get_R npc R) +ᵢ ($ 4)). iauto.
        asserts_rewrite (get_R pc R'  = get_R npc R). iauto.
        auto.
    }
  }

  {
  assert (handler_context R') as IVR'. {
    unfolds.
    splits; try unfolds; try unfolds;
    try asserts_rewrite ((get_R cwp R') = (get_R cwp R));
    try asserts_rewrite ((get_R annul R') = (get_R annul R)); 
    try asserts_rewrite ((get_R et R') = (get_R et R));
    try asserts_rewrite ((get_R trap R') = (get_R trap R));
    try asserts_rewrite ((get_R s R') = (get_R s R));
    iauto; apply IVR.
  }

  assert (align_context Ms' (R',F')) as ALIGN'. {
    unfolds.
    splits; try unfolds; try unfolds;
    try asserts_rewrite (get_R r17 R' = get_R r17 R);
    try asserts_rewrite (get_R r18 R' = get_R r18 R); 
    try asserts_rewrite (get_R r30 R' = get_R r30 R);
    try asserts_rewrite (Ms' = Ms);
    iauto; try apply ALIGN.
    {
      unfolds in ALIGN.
      unfold get_R.
      remember (left_win 2 (R, F)).
      destruct r as (R1 & F1).
      remember (left_win 2 (R', F')).
      destruct r as (R2 & F2).
      asserts_rewrite(F' = F) in Heqr0. iauto.
      unfold get_R in ALIGN.
      asserts_rewrite (R1 sp = R2 sp) in ALIGN. {
        apply (left_left_same sp R R' F R1 R2 F1 F2); iauto.
      } iauto.
    }
  }


 assert (single_mask2  (post_cwp 1 R') (R'#l5&ᵢ($255))) as MASK'. {
    unfold post_cwp.
    asserts_rewrite (get_R cwp R' = get_R cwp R). iauto.
    asserts_rewrite (get_R l5 R' = get_R l5 R). iauto.
    apply MASK.
  }

  assert (D' = [(1%nat, wim, R' l5)]) as DELAY'. {
    asserts_rewrite (R' l5 = get_R l5 R). iauto.
    iauto.
  }

  assert (f_context F') as CONT'. {
    asserts_rewrite (F' = F). iauto. iauto.
  }


  assert (Z__ (Cu, Cs) (Mu, Ms_, (R_, F_),[]) [None;None;None;None;None;None] 6 (Mu, Ms', (R', F'),D')) as GOAL'. {
    apply (No_Event (Cu,Cs) [None;None;None;None;None] 5 (Mu, Ms_, (R_, F_),[]) (Mu, Ms', (R', F'),D') (Mu, Ms, (R, F),D));
    try rewrite DELAY in *; auto.
  }
  clear H P__ IVR MASK CSR DELAY GOAL CONT ALIGN.
  clear Ms R F D.
  rename Ms' into Ms.
  rename R' into R.
  rename F' into F.
  rename D' into D.
  rename IVR' into IVR.
  rename MASK' into MASK.
  rename CSR' into CSR.
  rename DELAY' into DELAY.
  rename GOAL' into GOAL.
  rename ALIGN' into ALIGN.
  rename CONT' into CONT.



(* step 7 *)

  assert (not_abort Cs Ms (R,F) D) as NA. {
    unfolds.
    exists (R,F) [(0%nat, wim, R l5)] (nop).
    splits.
    - substs. auto.
    - asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)); iauto. apply FUNC.
    - unfolds. auto.
  }

  (* to P__ *)
  assert
  (exists Ms' Q' D', P__ (Cu,Cs) ((Mu,Ms),(R,F),D) ((Mu,Ms'),Q',D')) as H. {
    apply (Exists_P_Sup Cu Cs Mu Ms (R,F) D);
    auto; try apply IVR.
  }
  destruct H as (Ms' & Q' & D' & P__).
  destruct Q' as (R' & F').
  clear NA.

  (* deal with delay *)
  rewrite DELAY in *.

  (* small changes in one step *)
  assert (R'#pc = R#npc /\ R'#npc = R#npc +ᵢ ($4) /\
          R'#cwp = R#cwp /\ R'#annul = R#annul /\ R'#et = R#et /\ R'#trap = R#trap /\ R'#s = R#s /\ R'#wim = R#wim /\
          R'#l5 = R#l5 /\ R'#sp = R#sp /\ R'#l1 = R#l1 /\ R'#l2 = R#l2 /\ F' = F /\ D' = [(0%nat, wim, R l5)] /\ Ms' = Ms). {
  inverts P__.
  (* usr_mode *) {
    false. apply (ModeDeq (R,F)); auto.
    apply IVR.
  }
  (* sup_mode *) {
    inverts H10.
    unfolds in H6.
    inverts H6.
    assert (Cs (cursor_Q (R, F)) = Some (nop)) as INS. {
    asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4)). iauto.
    apply FUNC.
    }
    rewrite H11 in INS.
    clear H11. inverts INS.

    {
    inverts H12; try solve [false].
    inverts H5; try solve [false].
    repeat (split; auto); auto.
    }

    (* annul? no !*){
    inverts H5.
    false.
    apply (AnnulDeq R).
    apply H8. apply IVR.
    }
  }
  }

  assert (R'#pc = R_#pc +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) /\ normal_cursor (R',F')) as CSR'. {
    splits. {
      asserts_rewrite (get_R pc R' = get_R npc R). iauto.
      asserts_rewrite (get_R npc R = (get_R pc R) +ᵢ ($ 4)). apply CSR.
      asserts_rewrite (get_R pc R = (get_R pc R_) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)). apply CSR.
      auto.
    }
    {
      unfolds.
        asserts_rewrite (get_R npc R' = (get_R npc R) +ᵢ ($ 4)). iauto.
        asserts_rewrite (get_R pc R'  = get_R npc R). iauto.
        auto.
    }
  }

  {
  assert (handler_context R') as IVR'. {
    unfolds.
    splits; try unfolds; try unfolds;
    try asserts_rewrite ((get_R cwp R') = (get_R cwp R));
    try asserts_rewrite ((get_R annul R') = (get_R annul R)); 
    try asserts_rewrite ((get_R et R') = (get_R et R));
    try asserts_rewrite ((get_R trap R') = (get_R trap R));
    try asserts_rewrite ((get_R s R') = (get_R s R));
    iauto; apply IVR.
  }

  assert (align_context  Ms' (R',F')) as ALIGN'. {
    unfolds.
    splits; try unfolds; try unfolds;
    try asserts_rewrite (get_R r17 R' = get_R r17 R);
    try asserts_rewrite (get_R r18 R' = get_R r18 R); 
    try asserts_rewrite (get_R r30 R' = get_R r30 R);
    try asserts_rewrite (Ms' = Ms);
    iauto; try apply ALIGN.
    {
      unfolds in ALIGN.
      unfold get_R.
      remember (left_win 2 (R, F)).
      destruct r as (R1 & F1).
      remember (left_win 2 (R', F')).
      destruct r as (R2 & F2).
      asserts_rewrite(F' = F) in Heqr0. iauto.
      unfold get_R in ALIGN.
      asserts_rewrite (R1 sp = R2 sp) in ALIGN. {
        apply (left_left_same sp R R' F R1 R2 F1 F2); iauto.
      } iauto.
    }
  }


 assert (single_mask2  (post_cwp 1 R') (R'#l5&ᵢ($255))) as MASK'. {
    unfold post_cwp.
    asserts_rewrite (get_R cwp R' = get_R cwp R). iauto.
    asserts_rewrite (get_R l5 R' = get_R l5 R). iauto.
    apply MASK.
  }

  assert (D' = [(0%nat, wim, R' l5)]) as DELAY'. {
    asserts_rewrite (R' l5 = get_R l5 R). iauto.
    iauto.
  }

  assert (f_context F') as CONT'. {
    asserts_rewrite (F' = F). iauto. iauto.
  }


  assert (Z__ (Cu, Cs) (Mu, Ms_, (R_, F_),[]) [None;None;None;None;None;None;None] 7 (Mu, Ms', (R', F'),D')) as GOAL'. {
    apply (No_Event (Cu,Cs) [None;None;None;None;None;None] 6 (Mu, Ms_, (R_, F_),[]) (Mu, Ms', (R', F'),D') (Mu, Ms, (R, F),D));
    try rewrite DELAY in *; auto.
  }
  clear H P__ IVR MASK CSR DELAY GOAL CONT ALIGN.
  clear Ms R F D.
  rename Ms' into Ms.
  rename R' into R.
  rename F' into F.
  rename D' into D.
  rename IVR' into IVR.
  rename MASK' into MASK.
  rename CSR' into CSR.
  rename DELAY' into DELAY.
  rename GOAL' into GOAL.
  rename ALIGN' into ALIGN.
  rename CONT' into CONT.


(* step 8 *)

  assert (not_abort Cs Ms (R,F) D) as NA. {
    unfolds.
    remember (exe_delay (R, F) D).
    destruct p.
    exists r d (nop).
    splits.
    - substs. auto.
    - rewrite DELAY in Heqp. unfold exe_delay in Heqp.
      remember (R # wim <- (R l5)).
      inverts Heqp.
      rewrite Heqr0.
      asserts_rewrite (cursor_Q (R # wim <- (R l5), F) = cursor_Q (R, F)). iauto.
      asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)); iauto. apply FUNC.
    - unfolds. destruct r. auto.
  }

  (* to P__ *)
  assert
  (exists Ms' Q' D', P__ (Cu,Cs) ((Mu,Ms),(R,F),D) ((Mu,Ms'),Q',D')) as H. {
    apply (Exists_P_Sup Cu Cs Mu Ms (R,F) D);
    auto; try apply IVR.
  }
  destruct H as (Ms' & Q' & D' & P__).
  destruct Q' as (R' & F').
  clear NA.

  (* deal with delay *)
  rewrite DELAY in *.

  (* small changes in one step *)
  assert (R'#pc = R#npc /\ R'#npc = R#npc +ᵢ ($4) /\
          R'#cwp = R#cwp /\ R'#annul = R#annul /\ R'#et = R#et /\ R'#trap = R#trap /\ R'#s = R#s /\ R'#wim = (R#l5)&ᵢ ($ 255) /\
          R'#l5 = R#l5  /\ R'#l1 = R#l1 /\ R'#l2 = R#l2  /\ R'#sp = R#sp /\ F' = F /\ D' = [] /\ Ms' = Ms). {
  inverts P__.
  (* usr_mode *) {
    false. apply (ModeDeq (R,F)); auto.
    apply IVR.
  }
  (* sup_mode *) {
    inverts H10.
    unfolds in H6.
    remember (R # wim <- (R l5)).
    inverts H6.
    assert (Cs (cursor_Q (R, F)) = Some (nop)) as INS. {
    asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4) ). iauto.
    apply FUNC.
    }
    rewrite Heqr in H11.
    asserts_rewrite (cursor_Q (R # wim <- (R l5), F) = cursor_Q (R, F)) in H11. iauto.
    rewrite H11 in INS.
    clear H11. inverts INS.

    {
    inverts H12; try solve [false].
    inverts H5; try solve [false].
    repeat (split; auto); try rewrite Heqr; auto.
    }

    (* annul? no !*){
    inverts H5.
    false.
    apply (AnnulDeq R).
    apply H8. apply IVR.
    }
  }
  }

  assert (R'#pc = R_#pc +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) /\ normal_cursor (R',F')) as CSR'. {
    splits. {
      asserts_rewrite (get_R pc R' = get_R npc R). iauto.
      asserts_rewrite (get_R npc R = (get_R pc R) +ᵢ ($ 4)). apply CSR.
      asserts_rewrite (get_R pc R = (get_R pc R_) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)). apply CSR.
      auto.
    }
    {
      unfolds.
        asserts_rewrite (get_R npc R' = (get_R npc R) +ᵢ ($ 4)). iauto.
        asserts_rewrite (get_R pc R'  = get_R npc R). iauto.
        auto.
    }
  }

  {
  assert (handler_context R') as IVR'. {
    unfolds.
    splits; try unfolds; try unfolds;
    try asserts_rewrite ((get_R cwp R') = (get_R cwp R));
    try asserts_rewrite ((get_R annul R') = (get_R annul R)); 
    try asserts_rewrite ((get_R et R') = (get_R et R));
    try asserts_rewrite ((get_R trap R') = (get_R trap R));
    try asserts_rewrite ((get_R s R') = (get_R s R));
    iauto; apply IVR.
  }

  assert (align_context Ms' (R',F')) as ALIGN'. {
    unfolds.
    splits; try unfolds; try unfolds;
    try asserts_rewrite (get_R r17 R' = get_R r17 R);
    try asserts_rewrite (get_R r18 R' = get_R r18 R); 
    try asserts_rewrite (get_R r30 R' = get_R r30 R);
    try asserts_rewrite (Ms' = Ms);
    iauto; try apply ALIGN.
    {
      unfolds in ALIGN.
      unfold get_R.
      remember (left_win 2 (R, F)).
      destruct r as (R1 & F1).
      remember (left_win 2 (R', F')).
      destruct r as (R2 & F2).
      asserts_rewrite(F' = F) in Heqr0. iauto.
      unfold get_R in ALIGN.
      asserts_rewrite (R1 sp = R2 sp) in ALIGN. {
        apply (left_left_same sp R R' F R1 R2 F1 F2); iauto.
      } iauto.
    }
  }

 assert (single_mask2  (post_cwp 1 R') (R'#wim)) as MASK'. {
    unfold post_cwp.
    asserts_rewrite (get_R cwp R' = get_R cwp R). iauto.
    asserts_rewrite (get_R wim R' = (get_R l5 R) &ᵢ ($ 255)). iauto.
    apply MASK.
  }

  assert (D' = []) as DELAY'. {
    iauto.
  }

  assert (f_context F') as CONT'. {
    asserts_rewrite (F' = F). iauto. iauto.
  }

  assert (Z__ (Cu, Cs) (Mu, Ms_, (R_, F_),[]) [None;None;None;None;None;None;None;None]8 (Mu, Ms', (R', F'),D')) as GOAL'. {
    apply (No_Event (Cu,Cs) [None;None;None;None;None;None;None] 7 (Mu, Ms_, (R_, F_),[]) (Mu, Ms', (R', F'),D') (Mu, Ms, (R, F),D));
    try rewrite DELAY in *; auto.
  }
  clear H P__ IVR MASK CSR DELAY GOAL CONT ALIGN.
  clear Ms R F D.
  rename Ms' into Ms.
  rename R' into R.
  rename F' into F.
  rename D' into D.
  rename IVR' into IVR.
  rename MASK' into MASK.
  rename CSR' into CSR.
  rename DELAY' into DELAY.
  rename GOAL' into GOAL.
  rename ALIGN' into ALIGN.
  rename CONT' into CONT.



(* step 9 *)

  assert (not_abort Cs Ms (R,F) D) as NA. {
    unfolds.
    exists (R,F) D  (restore g0 g0 ᵣ g0).
    splits.
    - substs. auto.
    - asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4)  +ᵢ ($ 4)  +ᵢ ($ 4)  +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)); iauto. apply FUNC.
    - unfolds. auto.
  }

  (* to P__ *)
  assert
  (exists Ms' Q' D', P__ (Cu,Cs) ((Mu,Ms),(R,F),D) ((Mu,Ms'),Q',D')) as H. {
    apply (Exists_P_Sup Cu Cs Mu Ms (R,F) D);
    auto; try apply IVR.
  }
  destruct H as (Ms' & Q' & D' & P__).
  destruct Q' as (R' & F').
  clear NA.

  (* deal with delay *)
  rewrite DELAY in *.

  (* small changes in one step *)
  assert (R'#pc = R#npc /\ R'#npc = R#npc +ᵢ ($4) /\
         R'#annul = R#annul /\ R'#et = R#et /\ R'#trap = R#trap /\ R'#s = R#s /\ R'#wim = R#wim /\
           R'#cwp = (post_cwp 1 R) /\ D' = D /\ (let (R_Save,F_Save) := left_win 1 (R,F) in R'#l1 = R_Save#l1 /\ R'#l2 = R_Save#l2 /\ R'#o6 = R_Save#o6 /\ R'#r30 = R_Save#r30 /\ F' = F_Save) /\ Ms' = Ms). {
  inverts P__.
  (* usr_mode *) {
    false. apply (ModeDeq (R,F)); auto.
    apply IVR.
  }
  (* sup_mode *) {
    inverts H10.
    unfolds in H6.
    inverts H6.
    assert (Cs (cursor_Q (R, F)) = Some (restore g0 g0 ᵣ g0)) as INS. {
    asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) ). iauto.
    apply FUNC.
    }
    rewrite H11 in INS.
    clear H11. inverts INS.

    {
    inverts H12; try solve [false].
    inverts H5; try solve [false].
    inverts H6.
    unfold inc_win in *.
    destruct (win_masked (post_cwp 1 R) R).
    simpl in H13. try false.
    unfold negb in H13.
    remember (left_win 1 (R, F)).
    destruct r.
    inverts H13.
    rename Heqr into LWIN.
    assert (some_reg_eq R R'0). {
      apply (Hold_Sth_LeftWin R R'0 F F' 1); iauto.
    }
    unfolds in H. simpl in H.
    splits.
    simpl. asserts_rewrite (R npc = R'0 npc). iauto. auto.
    simpl. asserts_rewrite (R npc = R'0 npc). iauto. auto.
    simpl. asserts_rewrite (R annul = R'0 annul). iauto. auto.
    simpl. asserts_rewrite (R et = R'0 et). iauto. auto.
    simpl. asserts_rewrite (R trap = R'0 trap). iauto. auto.
    simpl. asserts_rewrite (R s = R'0 s). iauto. auto.
    simpl. asserts_rewrite (R Rwim = R'0 Rwim). iauto. auto.
    splits.
    simpl. asserts_rewrite (post_cwp 1 R = R'0 cwp). {
      symmetry. apply (left_cwp R R'0 F F'); iauto.
    } 
    iauto.
    iauto.
    asserts_rewrite (get_R r17 (next R'0 # r0 <- ((get_R r0 R) +ᵢ a)) = get_R r17 R'0). iauto. auto. auto.
    (* trap? no !*){
    inverts H4.
    asserts_rewrite (win_masked (post_cwp 1 R) R = false) in H0. {
      apply (mask_cwp_post R); iauto. apply IVR.
    }
    simpl in H0.
    inverts H0.
    }
    }
    (* annul? no !*){
    inverts H5.
    false.
    apply (AnnulDeq R).
    apply H8. apply IVR.
    }
  }
  }

  assert (R'#pc = R_#pc +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)  +ᵢ ($4) /\ normal_cursor (R',F')) as CSR'. {
    splits. {
      asserts_rewrite (get_R pc R' = get_R npc R). iauto.
      asserts_rewrite (get_R npc R = (get_R pc R) +ᵢ ($ 4)). apply CSR.
      asserts_rewrite (get_R pc R = (get_R pc R_) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)). apply CSR.
      auto.
    }
    {
      unfolds.
        asserts_rewrite (get_R npc R' = (get_R npc R) +ᵢ ($ 4)). iauto.
        asserts_rewrite (get_R pc R'  = get_R npc R). iauto.
        auto.
    }
  }

  {
  assert (handler_context R') as IVR'. {
    unfolds.
    splits; try unfolds; try unfolds;
    try asserts_rewrite ((get_R annul R') = (get_R annul R)); 
    try asserts_rewrite ((get_R et R') = (get_R et R));
    try asserts_rewrite ((get_R trap R') = (get_R trap R));
    try asserts_rewrite ((get_R s R') = (get_R s R));
    iauto; try apply IVR.
    unfolds in IVR.
    asserts_rewrite(Int.unsigned Asm.N - 1 = 7). {
      unfold Asm.N. mauto.
    }
    asserts_rewrite((get_R cwp R') = post_cwp 1 R). iauto.
    apply (cwp_cycle_post R). apply IVR.
  }

  assert (
   (let (Rl,Fl) := left_win 1 (R',F') in word_aligned_R Rl#sp /\ memort_context Rl#sp Ms') /\ 
   (let (Rr,Fr) := right_win 1 (R',F') in word_aligned_R Rr#l1 /\ word_aligned_R Rr#l2) ) as ALIGN'. {
    unfold align_context in ALIGN.
    splits.
    {
      asserts_rewrite (Ms' = Ms). iauto.
      remember (left_win 1 (R', F')) as K.
      destruct K as (Rl,Fl).
      remember (left_win 1 (R, F)) as K.
      destruct K as (Rl',Fl').
      remember (left_win 2 (R, F)) as K.
      destruct K as (Rll,Fll).
      asserts_rewrite ((get_R r14 Rll) = (get_R r14 Rl)) in ALIGN. {
        apply (Left_Left_is_Left2 R Rl' R' Rl Rll F Fl' F' Fl Fll); iauto.
      }
      iauto.
    }
    {
      remember (right_win 1 (R', F')) as K.
      destruct K as (Rr,Fr).
      remember (left_win 1 (R, F)) as K.
      destruct K as (Rl,Fl).
      asserts_rewrite ((get_R r17 Rr)  = (get_R r17 R)). {
      apply (Left_Right_is_Nothing R R' Rl Rr F F' Fl Fr); iauto.
      }
      asserts_rewrite ((get_R r18 Rr)  = (get_R r18 R)). {
      apply (Left_Right_is_Nothing R R' Rl Rr F F' Fl Fr); iauto.
      }
      splits;
      iauto.
    }  
  }

  assert (single_mask2 R'#cwp (get_R wim R')) as MASK'. {
    asserts_rewrite ((get_R wim R') = (get_R wim R)). iauto.
    apply (Post3_minus_1_is_2 R R'); iauto.
    apply IVR.
  }

  assert (D' = []) as DELAY'. {
    asserts_rewrite (D' = D). iauto. iauto.
  }


  assert (f_context F /\ f_context F') as CONT'. {
    splits; iauto.
    remember (left_win 1 (R, F)) as K.
      destruct K as (Rl,Fl).
    asserts_rewrite(F' = Fl). iauto.
    apply (hold_context_left R Rl F Fl); iauto. 
  }


  assert (Z__ (Cu, Cs) (Mu, Ms_, (R_, F_),[]) [None;None;None;None;None;None;None;None;None] 9 (Mu, Ms', (R', F'),D')) as GOAL'. {
    apply (No_Event (Cu,Cs) [None;None;None;None;None;None;None;None] 8 (Mu, Ms_, (R_, F_),[]) (Mu, Ms', (R', F'),D') (Mu, Ms, (R, F),D));
    try rewrite DELAY in *; auto.
  }
  clear H P__ IVR MASK CSR DELAY ALIGN GOAL CONT R.
  clear Ms D.
  rename F into F_restore.
  rename Ms' into Ms.
  rename R' into R.
  rename F' into F.
  rename D' into D.
  rename IVR' into IVR.
  rename MASK' into MASK.
  rename CSR' into CSR.
  rename DELAY' into DELAY.
  rename GOAL' into GOAL.
  rename ALIGN' into ALIGN.
  rename CONT' into CONT.





(* step 10 *)

  assert (not_abort Cs Ms (R,F) D) as NA. {
    unfolds.
    exists (R,F) D  (restore g0 g0 ᵣ g0).
    splits.
    - substs. auto.
    - asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4)  +ᵢ ($ 4) +ᵢ ($ 4)  +ᵢ ($ 4)  +ᵢ ($ 4)  +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)); iauto. apply FUNC.
    - unfolds. auto.
  }

  (* to P__ *)
  assert
  (exists Ms' Q' D', P__ (Cu,Cs) ((Mu,Ms),(R,F),D) ((Mu,Ms'),Q',D')) as H. {
    apply (Exists_P_Sup Cu Cs Mu Ms (R,F) D);
    auto; try apply IVR.
  }
  destruct H as (Ms' & Q' & D' & P__).
  destruct Q' as (R' & F').
  clear NA.

  (* deal with delay *)
  rewrite DELAY in *.

  (* small changes in one step *)
  assert (R'#pc = R#npc /\ R'#npc = R#npc +ᵢ ($4) /\
         R'#annul = R#annul /\ R'#et = R#et /\ R'#trap = R#trap /\ R'#s = R#s /\ R'#wim = R#wim /\
           R'#cwp = (post_cwp 1 R) /\ D' = D /\ (let (R_Save,F_Save) := left_win 1 (R,F) in R'#l1 = R_Save#l1 /\ R'#l2 = R_Save#l2 /\ R'#r14 = R_Save#r14 /\ F' = F_Save) /\ Ms' = Ms). {
  inverts P__.
  (* usr_mode *) {
    false. apply (ModeDeq (R,F)); auto.
    apply IVR.
  }
  (* sup_mode *) {
    inverts H10.
    unfolds in H6.
    inverts H6.
    assert (Cs (cursor_Q (R, F)) = Some (restore g0 g0 ᵣ g0)) as INS. {
    asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) ). iauto.
    apply FUNC.
    }
    rewrite H11 in INS.
    clear H11. inverts INS.

    {
    inverts H12; try solve [false].
    inverts H5; try solve [false].
    inverts H6.
    unfold inc_win in *.
    destruct (win_masked (post_cwp 1 R) R).
    simpl in H13. try false.
    unfold negb in H13.
    remember (left_win 1 (R, F)).
    destruct r.
    inverts H13.
    rename Heqr into LWIN.
    assert (some_reg_eq R R'0). {
      apply (Hold_Sth_LeftWin R R'0 F F' 1); iauto.
    }
    unfolds in H. simpl in H.
    splits.
    simpl. asserts_rewrite (R npc = R'0 npc). iauto. auto.
    simpl. asserts_rewrite (R npc = R'0 npc). iauto. auto.
    simpl. asserts_rewrite (R annul = R'0 annul). iauto. auto.
    simpl. asserts_rewrite (R et = R'0 et). iauto. auto.
    simpl. asserts_rewrite (R trap = R'0 trap). iauto. auto.
    simpl. asserts_rewrite (R s = R'0 s). iauto. auto.
    simpl. asserts_rewrite (R Rwim = R'0 Rwim). iauto. auto.
    splits.
    simpl. asserts_rewrite (post_cwp 1 R = R'0 cwp). {
      symmetry. apply (left_cwp R R'0 F F'); iauto.
    } 
    iauto.
    iauto.
    asserts_rewrite (get_R r17 (next R'0 # r0 <- ((get_R r0 R) +ᵢ a)) = get_R r17 R'0). iauto. auto. auto.
    (* trap? no !*){
    inverts H4.
    asserts_rewrite (win_masked (post_cwp 1 R) R = false) in H0. {
      apply (mask_cwp_post2 R); iauto. apply IVR.
    }
    simpl in H0.
    inverts H0.
    }
    }
    (* annul? no !*){
    inverts H5.
    false.
    apply (AnnulDeq R).
    apply H8. apply IVR.
    }
  }
  }

  assert (R'#pc = R_#pc +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)  +ᵢ ($4) /\ normal_cursor (R',F')) as CSR'. {
    splits. {
      asserts_rewrite (get_R pc R' = get_R npc R). iauto.
      asserts_rewrite (get_R npc R = (get_R pc R) +ᵢ ($ 4)). apply CSR.
      asserts_rewrite (get_R pc R = (get_R pc R_) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)). apply CSR.
      auto.
    }
    {
      unfolds.
        asserts_rewrite (get_R npc R' = (get_R npc R) +ᵢ ($ 4)). iauto.
        asserts_rewrite (get_R pc R'  = get_R npc R). iauto.
        auto.
    }
  }

  {
  assert (handler_context R') as IVR'. {
    unfolds.
    splits; try unfolds; try unfolds;
    try asserts_rewrite ((get_R annul R') = (get_R annul R)); 
    try asserts_rewrite ((get_R et R') = (get_R et R));
    try asserts_rewrite ((get_R trap R') = (get_R trap R));
    try asserts_rewrite ((get_R s R') = (get_R s R));
    iauto; try apply IVR.
    unfolds in IVR.
    asserts_rewrite(Int.unsigned Asm.N - 1 = 7). {
      unfold Asm.N. mauto.
    }
    asserts_rewrite((get_R cwp R') = post_cwp 1 R). iauto.
    apply (cwp_cycle_post R). apply IVR.
  }

  assert (
   word_aligned_R R'#sp /\ memort_context R'#sp Ms' /\
   (let (Rr,Fr) := right_win 2 (R',F') in word_aligned_R Rr#l1 /\ word_aligned_R Rr#l2) ) as ALIGN'. {
    unfold align_context in ALIGN.
    splits.
    {
      remember (left_win 1 (R, F)) as K.
      destruct K as (Rl',Fl').
      asserts_rewrite ((get_R r14 R') = (get_R r14 Rl')). iauto. iauto.
    }
    {
      asserts_rewrite (Ms' = Ms). iauto.
      remember (left_win 1 (R, F)) as K.
      destruct K as (Rl',Fl').
      asserts_rewrite ((get_R r14 R') = (get_R r14 Rl')). iauto. iauto.
    }
    {
      remember (right_win 2 (R', F')) as K.
      destruct K as (Rrr,Frr).
      remember (left_win 1 (R, F)) as K.
      destruct K as (Rl,Fl).
      remember (right_win 1 (R, F)) as K.
      destruct K as (Rr,Fr).

      asserts_rewrite ((get_R r17 Rrr)  = (get_R r17 Rr)). {
      apply (Left1_Right2_is_Right1  R Rl R' Rr Rrr F Fl F' Fr Frr); iauto.
      }
      asserts_rewrite ((get_R r18 Rrr)  = (get_R r18 Rr)). {
      apply (Left1_Right2_is_Right1  R Rl R' Rr Rrr F Fl F' Fr Frr); iauto.
      }
      iauto.
    }
  }

  assert (single_mask (post_cwp 1 R') (get_R wim R')) as MASK'. {
    asserts_rewrite ((get_R wim R') = (get_R wim R)). iauto.
    apply Post2_minus_1_is_1; iauto. apply IVR.
  }


  assert (D' = []) as DELAY'. {
    asserts_rewrite (D' = D). iauto. iauto.
  }


  assert (f_context F_restore /\ f_context F /\ f_context F') as CONT'. {
    splits; iauto.
    remember (left_win 1 (R, F)) as K.
      destruct K as (Rl,Fl).
    asserts_rewrite(F' = Fl). iauto.
    apply (hold_context_left R Rl F Fl); iauto. 
  }


  assert (Z__ (Cu, Cs) (Mu, Ms_, (R_, F_),[]) [None;None;None;None;None;None;None;None;None;None] 10 (Mu, Ms', (R', F'),D')) as GOAL'. {
    apply (No_Event (Cu,Cs) [None;None;None;None;None;None;None;None;None] 9 (Mu, Ms_, (R_, F_),[]) (Mu, Ms', (R', F'),D') (Mu, Ms, (R, F),D));
    try rewrite DELAY in *; auto.
  }
  clear H P__ IVR MASK CSR DELAY ALIGN GOAL CONT R.
  clear Ms D.
  rename F into F_restore_restore.
  rename Ms' into Ms.
  rename R' into R.
  rename F' into F.
  rename D' into D.
  rename IVR' into IVR.
  rename MASK' into MASK.
  rename CSR' into CSR.
  rename DELAY' into DELAY.
  rename GOAL' into GOAL.
  rename ALIGN' into ALIGN.
  rename CONT' into CONT.


(* step 11 *)

  assert (not_abort Cs Ms (R,F) D) as NA. {
    unfolds.
    exists (R,F) D  (ld sp ₐᵣ  l0).
    splits.
    - substs. auto.
    - asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4)  +ᵢ ($ 4) +ᵢ ($ 4)  +ᵢ ($ 4)  +ᵢ ($ 4)  +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)); iauto. apply FUNC.
    - unfolds. simpl. auto.
      assert (exists v, Ms (R r14) = Some v). {
      assert ( memort_context (get_R r14 R) Ms). iauto.
      unfold memort_context in H.
      destruct H as (v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & v15 & v16 & H).
      exists v1.
      apply H.
      }
      inverts H.
      rewrite H0. auto.
  }

  (* to P__ *)
  assert
  (exists Ms' Q' D', P__ (Cu,Cs) ((Mu,Ms),(R,F),D) ((Mu,Ms'),Q',D')) as H. {
    apply (Exists_P_Sup Cu Cs Mu Ms (R,F) D);
    auto; try apply IVR.
  }
  destruct H as (Ms' & Q' & D' & P__).
  destruct Q' as (R' & F').
  clear NA.

  (* deal with delay *)
  rewrite DELAY in *.

  (* small changes in one step *)
  assert (R'#pc = R#npc /\ R'#npc = R#npc +ᵢ ($4) /\
          R'#cwp = R#cwp /\ R'#annul = R#annul /\ R'#et = R#et /\ R'#trap = R#trap /\ R'#s = R#s /\ R'#wim = R#wim /\
          R'#sp = R#sp /\ F' = F /\ D' = [] /\ Ms' = Ms). {
  inverts P__.
  (* usr_mode *) {
    false. apply (ModeDeq (R,F)); auto.
    apply IVR.
  }

  (* sup_mode *) {
    inverts H10.
    unfolds in H6.
    inverts H6.
    assert (Cs (cursor_Q (R, F)) = Some (ld sp ₐᵣ  l0)) as INS. {
    asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) ). iauto.
    apply FUNC.
    }
    rewrite H11 in INS.
    clear H11. inverts INS.

    {
    inverts H12; try solve [false].
    inverts H5; try solve [false].
    inverts H6.
    splits;inverts H4;iauto.
    (* trap? no !*){
    inverts H4.
    asserts_rewrite (word_aligned (R r14) = true) in H0. {
      apply ALIGN.
    }
    simpl in H0.
    inverts H0.
    }
    }
    (* annul? no !*){
    inverts H5.
    false.
    apply (AnnulDeq R).
    apply H8. apply IVR.
    }
  }
  }



  assert (R'#pc = R_#pc +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) /\ normal_cursor (R',F')) as CSR'. {
    splits. {
      asserts_rewrite (get_R pc R' = get_R npc R). iauto.
      asserts_rewrite (get_R npc R = (get_R pc R) +ᵢ ($ 4)). apply CSR.
      asserts_rewrite (get_R pc R = (get_R pc R_) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)). apply CSR.
      auto.
    }
    {
      unfolds.
        asserts_rewrite (get_R npc R' = (get_R npc R) +ᵢ ($ 4)). iauto.
        asserts_rewrite (get_R pc R'  = get_R npc R). iauto.
        auto.
    }
  }

  {
  assert (handler_context R') as IVR'. {
    unfolds.
    splits; try unfolds; try unfolds;
    try asserts_rewrite ((get_R cwp R') = (get_R cwp R));
    try asserts_rewrite ((get_R annul R') = (get_R annul R)); 
    try asserts_rewrite ((get_R et R') = (get_R et R));
    try asserts_rewrite ((get_R trap R') = (get_R trap R));
    try asserts_rewrite ((get_R s R') = (get_R s R));
    iauto; apply IVR.
  }

  assert (
   word_aligned_R R'#sp /\ memort_context R'#sp Ms' /\
   (let (Rr,Fr) := right_win 2 (R',F') in word_aligned_R Rr#l1 /\ word_aligned_R Rr#l2) ) as ALIGN'. {
    unfold align_context in ALIGN.
    splits.
    {
      asserts_rewrite ((get_R r14 R') = (get_R r14 R)). iauto. iauto.
    }
    {
      asserts_rewrite (Ms' = Ms). iauto.
      asserts_rewrite ((get_R r14 R') = (get_R r14 R)). iauto. iauto.
    }
    {

      remember (right_win 2 (R', F')) as K.
      destruct K as (Rrr',Frr').
      remember (right_win 2 (R, F)) as K.
      destruct K as (Rrr,Frr).
      asserts_rewrite ((get_R r17 Rrr')  = (get_R r17 Rrr)). {
        apply (Right2_Right2_Same R R' Rrr Rrr' F F' Frr Frr'); iauto.
      }
      asserts_rewrite ((get_R r18 Rrr')  = (get_R r18 Rrr)). {
        apply (Right2_Right2_Same R R' Rrr Rrr' F F' Frr Frr'); iauto.
      }
      iauto.
    }
  }

  assert (single_mask (post_cwp 1 R') (get_R wim R')) as MASK'. {
    asserts_rewrite ((get_R wim R') = (get_R wim R)). iauto.
    unfold post_cwp.
    unfold post_cwp in MASK.
    asserts_rewrite ((get_R cwp R') = (get_R cwp R)). iauto.
    iauto.
  }


  assert (D' = []) as DELAY'. {
    iauto.
  }


  assert (f_context F_restore /\ f_context F_restore_restore /\ f_context F') as CONT'. {
    splits; iauto.
    asserts_rewrite(F' = F). iauto.
    iauto.
  }

  assert (Z__ (Cu, Cs) (Mu, Ms_, (R_, F_),[]) [None;None;None;None;None;None;None;None;None;None;None] 11 (Mu, Ms', (R', F'),D')) as GOAL'. {
    apply (No_Event (Cu,Cs) [None;None;None;None;None;None;None;None;None;None] 10 (Mu, Ms_, (R_, F_),[]) (Mu, Ms', (R', F'),D') (Mu, Ms, (R, F),D));
    try rewrite DELAY in *; auto.
  }
  clear H P__ IVR MASK CSR DELAY ALIGN GOAL CONT.
  clear Ms R F D.
  rename Ms' into Ms.
  rename R' into R.
  rename F' into F.
  rename D' into D.
  rename IVR' into IVR.
  rename MASK' into MASK.
  rename CSR' into CSR.
  rename DELAY' into DELAY.
  rename GOAL' into GOAL.
  rename ALIGN' into ALIGN.
  rename CONT' into CONT.





(* step 12 *)

  assert (not_abort Cs Ms (R,F) D) as NA. {
    unfolds.
    exists (R,F) D  (ld (sp+ₐₙ($4)) l1).
    splits.
    - substs. auto.
    - asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)  +ᵢ ($ 4) +ᵢ ($ 4)  +ᵢ ($ 4)  +ᵢ ($ 4)  +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)); iauto. apply FUNC.
    - unfolds. simpl. auto.
      asserts_rewrite(($ (-4096)) <=ᵢ ($ 4) && ($ 4) <=ᵢ ($ 4095) = true). {
        unfolds.
        asserts_rewrite (($ (-4096)) <=ᵢ ($ 4) = true). unfolds.
        asserts_rewrite (($ 4) >ᵢ ($ (-4096)) = true). mauto. auto. mauto. 
      }
      assert (exists v, Ms (R r14) +ᵢ ($ 4) = Some v). {
      assert ( memort_context (get_R r14 R) Ms). iauto.
      unfold memort_context in H.
      destruct H as (v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & v15 & v16 & H).
      exists v2.
      apply H.
      }
      inverts H.
      rewrite H0. auto.
  }

  (* to P__ *)
  assert
  (exists Ms' Q' D', P__ (Cu,Cs) ((Mu,Ms),(R,F),D) ((Mu,Ms'),Q',D')) as H. {
    apply (Exists_P_Sup Cu Cs Mu Ms (R,F) D);
    auto; try apply IVR.
  }
  destruct H as (Ms' & Q' & D' & P__).
  destruct Q' as (R' & F').
  clear NA.

  (* deal with delay *)
  rewrite DELAY in *.

  (* align *)
  assert (word_aligned_R (get_R r14 R)+ᵢ ($4)) as TMP. {
        apply align_plus4. iauto.
  }


  (* small changes in one step *)
  assert (R'#pc = R#npc /\ R'#npc = R#npc +ᵢ ($4) /\
          R'#cwp = R#cwp /\ R'#annul = R#annul /\ R'#et = R#et /\ R'#trap = R#trap /\ R'#s = R#s /\ R'#wim = R#wim /\
          R'#sp = R#sp /\ F' = F /\ D' = [] /\ Ms' = Ms). {
  inverts P__.
  (* usr_mode *) {
    false. apply (ModeDeq (R,F)); auto.
    apply IVR.
  }

  (* sup_mode *) {
    inverts H10.
    unfolds in H6.
    inverts H6.
    assert (Cs (cursor_Q (R, F)) = Some (ld (sp+ₐₙ($4)) l1)) as INS. {
    asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) ). iauto.
    apply FUNC.
    }
    rewrite H11 in INS.
    clear H11. inverts INS.

    {
    inverts H12; try solve [false].
    inverts H5; try solve [false].
    inverts H6.
    splits;inverts H4;iauto.
    (* trap? no !*){
    inverts H4.
    asserts_rewrite(($ (-4096)) <=ᵢ ($ 4) && ($ 4) <=ᵢ ($ 4095) = true) in H0. {
       unfolds.
       asserts_rewrite (($ (-4096)) <=ᵢ ($ 4) = true). unfolds.
       asserts_rewrite (($ 4) >ᵢ ($ (-4096)) = true). mauto. auto. mauto. 
    }
    asserts_rewrite (word_aligned (R r14) +ᵢ ($ 4) = true) in H0. iauto.
    simpl in H0.
    inverts H0.
    }
    }
    (* annul? no !*){
    inverts H5.
    false.
    apply (AnnulDeq R).
    apply H8. apply IVR.
    }
  }
  }



  assert (R'#pc = R_#pc +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) /\ normal_cursor (R',F')) as CSR'. {
    splits. {
      asserts_rewrite (get_R pc R' = get_R npc R). iauto.
      asserts_rewrite (get_R npc R = (get_R pc R) +ᵢ ($ 4)). apply CSR.
      asserts_rewrite (get_R pc R = (get_R pc R_) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)). apply CSR.
      auto.
    }
    {
      unfolds.
        asserts_rewrite (get_R npc R' = (get_R npc R) +ᵢ ($ 4)). iauto.
        asserts_rewrite (get_R pc R'  = get_R npc R). iauto.
        auto.
    }
  }

  {
  assert (handler_context R') as IVR'. {
    unfolds.
    splits; try unfolds; try unfolds;
    try asserts_rewrite ((get_R cwp R') = (get_R cwp R));
    try asserts_rewrite ((get_R annul R') = (get_R annul R)); 
    try asserts_rewrite ((get_R et R') = (get_R et R));
    try asserts_rewrite ((get_R trap R') = (get_R trap R));
    try asserts_rewrite ((get_R s R') = (get_R s R));
    iauto; apply IVR.
  }

  assert (
   word_aligned_R R'#sp /\ memort_context R'#sp Ms' /\
   (let (Rr,Fr) := right_win 2 (R',F') in word_aligned_R Rr#l1 /\ word_aligned_R Rr#l2) /\ word_aligned_R (get_R r14 R') +ᵢ ($ 4) ) as ALIGN'. {
    unfold align_context in ALIGN.
    splits.
    {
      asserts_rewrite ((get_R r14 R') = (get_R r14 R)). iauto. iauto.
    }
    {
      asserts_rewrite (Ms' = Ms). iauto.
      asserts_rewrite ((get_R r14 R') = (get_R r14 R)). iauto. iauto.
    }
    {

      remember (right_win 2 (R', F')) as K.
      destruct K as (Rrr',Frr').
      remember (right_win 2 (R, F)) as K.
      destruct K as (Rrr,Frr).
      asserts_rewrite ((get_R r17 Rrr')  = (get_R r17 Rrr)). {
        apply (Right2_Right2_Same R R' Rrr Rrr' F F' Frr Frr'); iauto.
      }
      asserts_rewrite ((get_R r18 Rrr')  = (get_R r18 Rrr)). {
        apply (Right2_Right2_Same R R' Rrr Rrr' F F' Frr Frr'); iauto.
      }
      iauto.
    }
    asserts_rewrite (get_R r14 R' = get_R r14 R). iauto. iauto.
  }

  assert (single_mask (post_cwp 1 R') (get_R wim R')) as MASK'. {
    asserts_rewrite ((get_R wim R') = (get_R wim R)). iauto.
    unfold post_cwp.
    unfold post_cwp in MASK.
    asserts_rewrite ((get_R cwp R') = (get_R cwp R)). iauto.
    iauto.
  }


  assert (D' = []) as DELAY'. {
    iauto.
  }


  assert (f_context F_restore /\ f_context F_restore_restore /\ f_context F') as CONT'. {
    splits; iauto.
    asserts_rewrite(F' = F). iauto.
    iauto.
  }

  assert (Z__ (Cu, Cs) (Mu, Ms_, (R_, F_),[]) [None;None;None;None;None;None;None;None;None;None;None;None] 12 (Mu, Ms', (R', F'),D')) as GOAL'. {
    apply (No_Event (Cu,Cs) [None;None;None;None;None;None;None;None;None;None;None] 11 (Mu, Ms_, (R_, F_),[]) (Mu, Ms', (R', F'),D') (Mu, Ms, (R, F),D));
    try rewrite DELAY in *; auto.
  }
  clear H P__ IVR MASK CSR DELAY ALIGN GOAL CONT TMP.
  clear Ms R F D.
  rename Ms' into Ms.
  rename R' into R.
  rename F' into F.
  rename D' into D.
  rename IVR' into IVR.
  rename MASK' into MASK.
  rename CSR' into CSR.
  rename DELAY' into DELAY.
  rename GOAL' into GOAL.
  rename ALIGN' into ALIGN.
  rename CONT' into CONT.





(* step 13 *)

  assert (not_abort Cs Ms (R,F) D) as NA. {
    unfolds.
    exists (R,F) D  (ld (sp+ₐₙ($8)) l2).
    splits.
    - substs. auto.
    - asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)  +ᵢ ($ 4) +ᵢ ($ 4)  +ᵢ ($ 4)  +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)); iauto. apply FUNC.
    - unfolds. simpl. auto.
      asserts_rewrite(($ (-4096)) <=ᵢ ($ 8) && ($ 8) <=ᵢ ($ 4095) = true). {
        unfolds.
        asserts_rewrite (($ (-4096)) <=ᵢ ($ 8) = true). unfolds.
        asserts_rewrite (($ 8) >ᵢ ($ (-4096)) = true). mauto. auto. mauto. 
      }
      assert (exists v, Ms (R r14) +ᵢ ($ 8) = Some v). {
      assert ( memort_context (get_R r14 R) Ms). iauto.
      unfold memort_context in H.
      destruct H as (v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & v15 & v16 & H).
      exists v3.
      apply H.
      }
      inverts H.
      rewrite H0. auto.
  }

  (* to P__ *)
  assert
  (exists Ms' Q' D', P__ (Cu,Cs) ((Mu,Ms),(R,F),D) ((Mu,Ms'),Q',D')) as H. {
    apply (Exists_P_Sup Cu Cs Mu Ms (R,F) D);
    auto; try apply IVR.
  }
  destruct H as (Ms' & Q' & D' & P__).
  destruct Q' as (R' & F').
  clear NA.

  (* deal with delay *)
  rewrite DELAY in *.

  (* align *)
  assert (word_aligned_R (get_R r14 R)+ᵢ ($8)) as TMP. {
     asserts_rewrite (($ 8) = ($ 4) +ᵢ ($ 4)). {
      clear CSR. int auto.
    }
    rewrite <- Int.add_assoc.
    apply align_plus4. iauto.
  }


  (* small changes in one step *)
  assert (R'#pc = R#npc /\ R'#npc = R#npc +ᵢ ($4) /\
          R'#cwp = R#cwp /\ R'#annul = R#annul /\ R'#et = R#et /\ R'#trap = R#trap /\ R'#s = R#s /\ R'#wim = R#wim /\
          R'#sp = R#sp /\ F' = F /\ D' = [] /\ Ms' = Ms). {
  inverts P__.
  (* usr_mode *) {
    false. apply (ModeDeq (R,F)); auto.
    apply IVR.
  }

  (* sup_mode *) {
    inverts H10.
    unfolds in H6.
    inverts H6.
    assert (Cs (cursor_Q (R, F)) = Some (ld (sp+ₐₙ($8)) l2)) as INS. {
    asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)  +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) ). iauto.
    apply FUNC.
    }
    rewrite H11 in INS.
    clear H11. inverts INS.

    {
    inverts H12; try solve [false].
    inverts H5; try solve [false].
    inverts H6.
    splits;inverts H4;iauto.
    (* trap? no !*){
    inverts H4.
    asserts_rewrite(($ (-4096)) <=ᵢ ($ 8) && ($ 8) <=ᵢ ($ 4095) = true) in H0. {
       unfolds.
       asserts_rewrite (($ (-4096)) <=ᵢ ($ 8) = true). unfolds.
       asserts_rewrite (($ 8) >ᵢ ($ (-4096)) = true). mauto. auto. mauto. 
    }
    asserts_rewrite (word_aligned (R r14) +ᵢ ($ 8) = true) in H0. iauto.
    simpl in H0.
    inverts H0.
    }
    }
    (* annul? no !*){
    inverts H5.
    false.
    apply (AnnulDeq R).
    apply H8. apply IVR.
    }
  }
  }



  assert (R'#pc = R_#pc +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) /\ normal_cursor (R',F')) as CSR'. {
    splits. {
      asserts_rewrite (get_R pc R' = get_R npc R). iauto.
      asserts_rewrite (get_R npc R = (get_R pc R) +ᵢ ($ 4)). apply CSR.
      asserts_rewrite (get_R pc R = (get_R pc R_) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)). apply CSR.
      auto.
    }
    {
      unfolds.
        asserts_rewrite (get_R npc R' = (get_R npc R) +ᵢ ($ 4)). iauto.
        asserts_rewrite (get_R pc R'  = get_R npc R). iauto.
        auto.
    }
  }

  {
  assert (handler_context R') as IVR'. {
    unfolds.
    splits; try unfolds; try unfolds;
    try asserts_rewrite ((get_R cwp R') = (get_R cwp R));
    try asserts_rewrite ((get_R annul R') = (get_R annul R)); 
    try asserts_rewrite ((get_R et R') = (get_R et R));
    try asserts_rewrite ((get_R trap R') = (get_R trap R));
    try asserts_rewrite ((get_R s R') = (get_R s R));
    iauto; apply IVR.
  }

  assert (
   word_aligned_R R'#sp /\ memort_context R'#sp Ms' /\
   (let (Rr,Fr) := right_win 2 (R',F') in word_aligned_R Rr#l1 /\ word_aligned_R Rr#l2) /\ word_aligned_R (get_R r14 R') +ᵢ ($ 8)) as ALIGN'. {
    unfold align_context in ALIGN.
    splits.
    {
      asserts_rewrite ((get_R r14 R') = (get_R r14 R)). iauto. iauto.
    }
    {
      asserts_rewrite (Ms' = Ms). iauto.
      asserts_rewrite ((get_R r14 R') = (get_R r14 R)). iauto. iauto.
    }
    {

      remember (right_win 2 (R', F')) as K.
      destruct K as (Rrr',Frr').
      remember (right_win 2 (R, F)) as K.
      destruct K as (Rrr,Frr).
      asserts_rewrite ((get_R r17 Rrr')  = (get_R r17 Rrr)). {
        apply (Right2_Right2_Same R R' Rrr Rrr' F F' Frr Frr'); iauto.
      }
      asserts_rewrite ((get_R r18 Rrr')  = (get_R r18 Rrr)). {
        apply (Right2_Right2_Same R R' Rrr Rrr' F F' Frr Frr'); iauto.
      }
      iauto.
    }
    asserts_rewrite (get_R r14 R' = get_R r14 R). iauto. iauto.
  }

  assert (single_mask (post_cwp 1 R') (get_R wim R')) as MASK'. {
    asserts_rewrite ((get_R wim R') = (get_R wim R)). iauto.
    unfold post_cwp.
    unfold post_cwp in MASK.
    asserts_rewrite ((get_R cwp R') = (get_R cwp R)). iauto.
    iauto.
  }


  assert (D' = []) as DELAY'. {
    iauto.
  }


  assert (f_context F_restore /\ f_context F_restore_restore /\ f_context F') as CONT'. {
    splits; iauto.
    asserts_rewrite(F' = F). iauto.
    iauto.
  }

  assert (Z__ (Cu, Cs) (Mu, Ms_, (R_, F_),[]) [None;None;None;None;None;None;None;None;None;None;None;None;None] 13 (Mu, Ms', (R', F'),D')) as GOAL'. {
    apply (No_Event (Cu,Cs) [None;None;None;None;None;None;None;None;None;None;None;None] 12 (Mu, Ms_, (R_, F_),[]) (Mu, Ms', (R', F'),D') (Mu, Ms, (R, F),D));
    try rewrite DELAY in *; auto.
  }
  clear H P__ IVR MASK CSR DELAY ALIGN GOAL CONT TMP.
  clear Ms R F D.
  rename Ms' into Ms.
  rename R' into R.
  rename F' into F.
  rename D' into D.
  rename IVR' into IVR.
  rename MASK' into MASK.
  rename CSR' into CSR.
  rename DELAY' into DELAY.
  rename GOAL' into GOAL.
  rename ALIGN' into ALIGN.
  rename CONT' into CONT.





(* step 14 *)

  assert (not_abort Cs Ms (R,F) D) as NA. {
    unfolds.
    exists (R,F) D  (ld (sp+ₐₙ($12)) l3).
    splits.
    - substs. auto.
    - asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)  +ᵢ ($ 4) +ᵢ ($ 4)  +ᵢ ($ 4)  +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)); iauto. apply FUNC.
    - unfolds. simpl. auto.
      asserts_rewrite(($ (-4096)) <=ᵢ ($ 12) && ($ 12) <=ᵢ ($ 4095) = true). {
        unfolds.
        asserts_rewrite (($ (-4096)) <=ᵢ ($ 12) = true). unfolds.
        asserts_rewrite (($ 12) >ᵢ ($ (-4096)) = true). mauto. auto. mauto. 
      }
      assert (exists v, Ms (R r14) +ᵢ ($ 12) = Some v). {
      assert ( memort_context (get_R r14 R) Ms). iauto.
      unfold memort_context in H.
      destruct H as (v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & v15 & v16 & H).
      exists v4.
      apply H.
      }
      inverts H.
      rewrite H0. auto.
  }

  (* to P__ *)
  assert
  (exists Ms' Q' D', P__ (Cu,Cs) ((Mu,Ms),(R,F),D) ((Mu,Ms'),Q',D')) as H. {
    apply (Exists_P_Sup Cu Cs Mu Ms (R,F) D);
    auto; try apply IVR.
  }
  destruct H as (Ms' & Q' & D' & P__).
  destruct Q' as (R' & F').
  clear NA.

  (* deal with delay *)
  rewrite DELAY in *.

  (* align *)
  assert (word_aligned_R (get_R r14 R)+ᵢ ($12)) as TMP. {
     asserts_rewrite (($ 12) = ($ 8) +ᵢ ($ 4)). {
      clear CSR. int auto.
    }
    rewrite <- Int.add_assoc.
    apply align_plus4. iauto.
  }


  (* small changes in one step *)
  assert (R'#pc = R#npc /\ R'#npc = R#npc +ᵢ ($4) /\
          R'#cwp = R#cwp /\ R'#annul = R#annul /\ R'#et = R#et /\ R'#trap = R#trap /\ R'#s = R#s /\ R'#wim = R#wim /\
          R'#sp = R#sp /\ F' = F /\ D' = [] /\ Ms' = Ms). {
  inverts P__.
  (* usr_mode *) {
    false. apply (ModeDeq (R,F)); auto.
    apply IVR.
  }

  (* sup_mode *) {
    inverts H10.
    unfolds in H6.
    inverts H6.
    assert (Cs (cursor_Q (R, F)) = Some (ld (sp+ₐₙ($12)) l3)) as INS. {
    asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)  +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) ). iauto.
    apply FUNC.
    }
    rewrite H11 in INS.
    clear H11. inverts INS.

    {
    inverts H12; try solve [false].
    inverts H5; try solve [false].
    inverts H6.
    splits;inverts H4;iauto.
    (* trap? no !*){
    inverts H4.
    asserts_rewrite(($ (-4096)) <=ᵢ ($ 12) && ($ 12) <=ᵢ ($ 4095) = true) in H0. {
       unfolds.
       asserts_rewrite (($ (-4096)) <=ᵢ ($ 12) = true). unfolds.
       asserts_rewrite (($ 12) >ᵢ ($ (-4096)) = true). mauto. auto. mauto. 
    }
    asserts_rewrite (word_aligned (R r14) +ᵢ ($ 12) = true) in H0. iauto.
    simpl in H0.
    inverts H0.
    }
    }
    (* annul? no !*){
    inverts H5.
    false.
    apply (AnnulDeq R).
    apply H8. apply IVR.
    }
  }
  }



  assert (R'#pc = R_#pc +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) /\ normal_cursor (R',F')) as CSR'. {
    splits. {
      asserts_rewrite (get_R pc R' = get_R npc R). iauto.
      asserts_rewrite (get_R npc R = (get_R pc R) +ᵢ ($ 4)). apply CSR.
      asserts_rewrite (get_R pc R = (get_R pc R_) +ᵢ ($4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)). apply CSR.
      auto.
    }
    {
      unfolds.
        asserts_rewrite (get_R npc R' = (get_R npc R) +ᵢ ($ 4)). iauto.
        asserts_rewrite (get_R pc R'  = get_R npc R). iauto.
        auto.
    }
  }

  {
  assert (handler_context R') as IVR'. {
    unfolds.
    splits; try unfolds; try unfolds;
    try asserts_rewrite ((get_R cwp R') = (get_R cwp R));
    try asserts_rewrite ((get_R annul R') = (get_R annul R)); 
    try asserts_rewrite ((get_R et R') = (get_R et R));
    try asserts_rewrite ((get_R trap R') = (get_R trap R));
    try asserts_rewrite ((get_R s R') = (get_R s R));
    iauto; apply IVR.
  }

  assert (
   word_aligned_R R'#sp /\ memort_context R'#sp Ms' /\
   (let (Rr,Fr) := right_win 2 (R',F') in word_aligned_R Rr#l1 /\ word_aligned_R Rr#l2) /\ word_aligned_R (get_R r14 R') +ᵢ ($ 12)) as ALIGN'. {
    unfold align_context in ALIGN.
    splits.
    {
      asserts_rewrite ((get_R r14 R') = (get_R r14 R)). iauto. iauto.
    }
    {
      asserts_rewrite (Ms' = Ms). iauto.
      asserts_rewrite ((get_R r14 R') = (get_R r14 R)). iauto. iauto.
    }
    {

      remember (right_win 2 (R', F')) as K.
      destruct K as (Rrr',Frr').
      remember (right_win 2 (R, F)) as K.
      destruct K as (Rrr,Frr).
      asserts_rewrite ((get_R r17 Rrr')  = (get_R r17 Rrr)). {
        apply (Right2_Right2_Same R R' Rrr Rrr' F F' Frr Frr'); iauto.
      }
      asserts_rewrite ((get_R r18 Rrr')  = (get_R r18 Rrr)). {
        apply (Right2_Right2_Same R R' Rrr Rrr' F F' Frr Frr'); iauto.
      }
      iauto.
    }
    asserts_rewrite (get_R r14 R' = get_R r14 R). iauto. iauto.
  }

  assert (single_mask (post_cwp 1 R') (get_R wim R')) as MASK'. {
    asserts_rewrite ((get_R wim R') = (get_R wim R)). iauto.
    unfold post_cwp.
    unfold post_cwp in MASK.
    asserts_rewrite ((get_R cwp R') = (get_R cwp R)). iauto.
    iauto.
  }


  assert (D' = []) as DELAY'. {
    iauto.
  }


  assert (f_context F_restore /\ f_context F_restore_restore /\ f_context F') as CONT'. {
    splits; iauto.
    asserts_rewrite(F' = F). iauto.
    iauto.
  }

  assert (Z__ (Cu, Cs) (Mu, Ms_, (R_, F_),[]) [None;None;None;None;None;None;None;None;None;None;None;None;None;None] 14 (Mu, Ms', (R', F'),D')) as GOAL'. {
    apply (No_Event (Cu,Cs) [None;None;None;None;None;None;None;None;None;None;None;None;None] 13 (Mu, Ms_, (R_, F_),[]) (Mu, Ms', (R', F'),D') (Mu, Ms, (R, F),D));
    try rewrite DELAY in *; auto.
  }
  clear H P__ IVR MASK CSR DELAY ALIGN GOAL CONT TMP.
  clear Ms R F D.
  rename Ms' into Ms.
  rename R' into R.
  rename F' into F.
  rename D' into D.
  rename IVR' into IVR.
  rename MASK' into MASK.
  rename CSR' into CSR.
  rename DELAY' into DELAY.
  rename GOAL' into GOAL.
  rename ALIGN' into ALIGN.
  rename CONT' into CONT.


(* step 15 *)

  assert (not_abort Cs Ms (R,F) D) as NA. {
    unfolds.
    exists (R,F) D  (ld (sp+ₐₙ($16)) l4).
    splits.
    - substs. auto.
    - asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)  +ᵢ ($ 4) +ᵢ ($ 4)  +ᵢ ($ 4)  +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)); iauto. apply FUNC.
    - unfolds. simpl. auto.
      asserts_rewrite(($ (-4096)) <=ᵢ ($ 16) && ($ 16) <=ᵢ ($ 4095) = true). {
        unfolds.
        asserts_rewrite (($ (-4096)) <=ᵢ ($ 16) = true). unfolds.
        asserts_rewrite (($ 16) >ᵢ ($ (-4096)) = true). mauto. auto. mauto. 
      }
      assert (exists v, Ms (R r14) +ᵢ ($ 16) = Some v). {
      assert ( memort_context (get_R r14 R) Ms). iauto.
      unfold memort_context in H.
      destruct H as (v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & v15 & v16 & H).
      exists v5.
      apply H.
      }
      inverts H.
      rewrite H0. auto.
  }

  (* to P__ *)
  assert
  (exists Ms' Q' D', P__ (Cu,Cs) ((Mu,Ms),(R,F),D) ((Mu,Ms'),Q',D')) as H. {
    apply (Exists_P_Sup Cu Cs Mu Ms (R,F) D);
    auto; try apply IVR.
  }
  destruct H as (Ms' & Q' & D' & P__).
  destruct Q' as (R' & F').
  clear NA.

  (* deal with delay *)
  rewrite DELAY in *.

  (* align *)
  assert (word_aligned_R (get_R r14 R)+ᵢ ($16)) as TMP. {
     asserts_rewrite (($ 16) = ($ 12) +ᵢ ($ 4)). {
      clear CSR. int auto.
    }
    rewrite <- Int.add_assoc.
    apply align_plus4. iauto.
  }


  (* small changes in one step *)
  assert (R'#pc = R#npc /\ R'#npc = R#npc +ᵢ ($4) /\
          R'#cwp = R#cwp /\ R'#annul = R#annul /\ R'#et = R#et /\ R'#trap = R#trap /\ R'#s = R#s /\ R'#wim = R#wim /\
          R'#sp = R#sp /\ F' = F /\ D' = [] /\ Ms' = Ms). {
  inverts P__.
  (* usr_mode *) {
    false. apply (ModeDeq (R,F)); auto.
    apply IVR.
  }

  (* sup_mode *) {
    inverts H10.
    unfolds in H6.
    inverts H6.
    assert (Cs (cursor_Q (R, F)) = Some (ld (sp+ₐₙ($16)) l4)) as INS. {
    asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)  +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) ). iauto.
    apply FUNC.
    }
    rewrite H11 in INS.
    clear H11. inverts INS.

    {
    inverts H12; try solve [false].
    inverts H5; try solve [false].
    inverts H6.
    splits;inverts H4;iauto.
    (* trap? no !*){
    inverts H4.
    asserts_rewrite(($ (-4096)) <=ᵢ ($ 16) && ($ 16) <=ᵢ ($ 4095) = true) in H0. {
       unfolds.
       asserts_rewrite (($ (-4096)) <=ᵢ ($ 16) = true). unfolds.
       asserts_rewrite (($ 16) >ᵢ ($ (-4096)) = true). mauto. auto. mauto. 
    }
    asserts_rewrite (word_aligned (R r14) +ᵢ ($ 16) = true) in H0. iauto.
    simpl in H0.
    inverts H0.
    }
    }
    (* annul? no !*){
    inverts H5.
    false.
    apply (AnnulDeq R).
    apply H8. apply IVR.
    }
  }
  }



  assert (R'#pc = R_#pc +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) /\ normal_cursor (R',F')) as CSR'. {
    splits. {
      asserts_rewrite (get_R pc R' = get_R npc R). iauto.
      asserts_rewrite (get_R npc R = (get_R pc R) +ᵢ ($ 4)). apply CSR.
      asserts_rewrite (get_R pc R = (get_R pc R_) +ᵢ ($4) +ᵢ ($4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)). apply CSR.
      auto.
    }
    {
      unfolds.
        asserts_rewrite (get_R npc R' = (get_R npc R) +ᵢ ($ 4)). iauto.
        asserts_rewrite (get_R pc R'  = get_R npc R). iauto.
        auto.
    }
  }

  {
  assert (handler_context R') as IVR'. {
    unfolds.
    splits; try unfolds; try unfolds;
    try asserts_rewrite ((get_R cwp R') = (get_R cwp R));
    try asserts_rewrite ((get_R annul R') = (get_R annul R)); 
    try asserts_rewrite ((get_R et R') = (get_R et R));
    try asserts_rewrite ((get_R trap R') = (get_R trap R));
    try asserts_rewrite ((get_R s R') = (get_R s R));
    iauto; apply IVR.
  }

  assert (
   word_aligned_R R'#sp /\ memort_context R'#sp Ms' /\
   (let (Rr,Fr) := right_win 2 (R',F') in word_aligned_R Rr#l1 /\ word_aligned_R Rr#l2) /\ word_aligned_R (get_R r14 R') +ᵢ ($ 16)) as ALIGN'. {
    unfold align_context in ALIGN.
    splits.
    {
      asserts_rewrite ((get_R r14 R') = (get_R r14 R)). iauto. iauto.
    }
    {
      asserts_rewrite (Ms' = Ms). iauto.
      asserts_rewrite ((get_R r14 R') = (get_R r14 R)). iauto. iauto.
    }
    {

      remember (right_win 2 (R', F')) as K.
      destruct K as (Rrr',Frr').
      remember (right_win 2 (R, F)) as K.
      destruct K as (Rrr,Frr).
      asserts_rewrite ((get_R r17 Rrr')  = (get_R r17 Rrr)). {
        apply (Right2_Right2_Same R R' Rrr Rrr' F F' Frr Frr'); iauto.
      }
      asserts_rewrite ((get_R r18 Rrr')  = (get_R r18 Rrr)). {
        apply (Right2_Right2_Same R R' Rrr Rrr' F F' Frr Frr'); iauto.
      }
      iauto.
    }
    asserts_rewrite (get_R r14 R' = get_R r14 R). iauto. iauto.
  }

  assert (single_mask (post_cwp 1 R') (get_R wim R')) as MASK'. {
    asserts_rewrite ((get_R wim R') = (get_R wim R)). iauto.
    unfold post_cwp.
    unfold post_cwp in MASK.
    asserts_rewrite ((get_R cwp R') = (get_R cwp R)). iauto.
    iauto.
  }


  assert (D' = []) as DELAY'. {
    iauto.
  }


  assert (f_context F_restore /\ f_context F_restore_restore /\ f_context F') as CONT'. {
    splits; iauto.
    asserts_rewrite(F' = F). iauto.
    iauto.
  }

  assert (Z__ (Cu, Cs) (Mu, Ms_, (R_, F_),[]) [None;None;None;None;None;None;None;None;None;None;None;None;None;None;None] 15 (Mu, Ms', (R', F'),D')) as GOAL'. {
    apply (No_Event (Cu,Cs) [None;None;None;None;None;None;None;None;None;None;None;None;None;None] 14 (Mu, Ms_, (R_, F_),[]) (Mu, Ms', (R', F'),D') (Mu, Ms, (R, F),D));
    try rewrite DELAY in *; auto.
  }
  clear H P__ IVR MASK CSR DELAY ALIGN GOAL CONT TMP.
  clear Ms R F D.
  rename Ms' into Ms.
  rename R' into R.
  rename F' into F.
  rename D' into D.
  rename IVR' into IVR.
  rename MASK' into MASK.
  rename CSR' into CSR.
  rename DELAY' into DELAY.
  rename GOAL' into GOAL.
  rename ALIGN' into ALIGN.
  rename CONT' into CONT.



(* step 16 *)

  assert (not_abort Cs Ms (R,F) D) as NA. {
    unfolds.
    exists (R,F) D  (ld (sp+ₐₙ($20)) l5).
    splits.
    - substs. auto.
    - asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)  +ᵢ ($ 4) +ᵢ ($ 4)  +ᵢ ($ 4)  +ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)); iauto. apply FUNC.
    - unfolds. simpl. auto.
      asserts_rewrite(($ (-4096)) <=ᵢ ($ 20) && ($ 20) <=ᵢ ($ 4095) = true). {
        unfolds.
        asserts_rewrite (($ (-4096)) <=ᵢ ($ 20) = true). unfolds.
        asserts_rewrite (($ 20) >ᵢ ($ (-4096)) = true). mauto. auto. mauto. 
      }
      assert (exists v, Ms (R r14) +ᵢ ($ 20) = Some v). {
      assert ( memort_context (get_R r14 R) Ms). iauto.
      unfold memort_context in H.
      destruct H as (v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & v15 & v16 & H).
      exists v6.
      apply H.
      }
      inverts H.
      rewrite H0. auto.
  }

  (* to P__ *)
  assert
  (exists Ms' Q' D', P__ (Cu,Cs) ((Mu,Ms),(R,F),D) ((Mu,Ms'),Q',D')) as H. {
    apply (Exists_P_Sup Cu Cs Mu Ms (R,F) D);
    auto; try apply IVR.
  }
  destruct H as (Ms' & Q' & D' & P__).
  destruct Q' as (R' & F').
  clear NA.

  (* deal with delay *)
  rewrite DELAY in *.

  (* align *)
  assert (word_aligned_R (get_R r14 R)+ᵢ ($20)) as TMP. {
     asserts_rewrite (($ 20) = ($ 16) +ᵢ ($ 4)). {
      clear CSR. int auto.
    }
    rewrite <- Int.add_assoc.
    apply align_plus4. iauto.
  }


  (* small changes in one step *)
  assert (R'#pc = R#npc /\ R'#npc = R#npc +ᵢ ($4) /\
          R'#cwp = R#cwp /\ R'#annul = R#annul /\ R'#et = R#et /\ R'#trap = R#trap /\ R'#s = R#s /\ R'#wim = R#wim /\
          R'#sp = R#sp /\ F' = F /\ D' = [] /\ Ms' = Ms). {
  inverts P__.
  (* usr_mode *) {
    false. apply (ModeDeq (R,F)); auto.
    apply IVR.
  }

  (* sup_mode *) {
    inverts H10.
    unfolds in H6.
    inverts H6.
    assert (Cs (cursor_Q (R, F)) = Some (ld (sp+ₐₙ($20)) l5)) as INS. {
    asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4)  +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)  +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) ). iauto.
    apply FUNC.
    }
    rewrite H11 in INS.
    clear H11. inverts INS.

    {
    inverts H12; try solve [false].
    inverts H5; try solve [false].
    inverts H6.
    splits;inverts H4;iauto.
    (* trap? no !*){
    inverts H4.
    asserts_rewrite(($ (-4096)) <=ᵢ ($ 20) && ($ 20) <=ᵢ ($ 4095) = true) in H0. {
       unfolds.
       asserts_rewrite (($ (-4096)) <=ᵢ ($ 20) = true). unfolds.
       asserts_rewrite (($ 20) >ᵢ ($ (-4096)) = true). mauto. auto. mauto. 
    }
    asserts_rewrite (word_aligned (R r14) +ᵢ ($ 20) = true) in H0. iauto.
    simpl in H0.
    inverts H0.
    }
    }
    (* annul? no !*){
    inverts H5.
    false.
    apply (AnnulDeq R).
    apply H8. apply IVR.
    }
  }
  }



  assert (R'#pc = R_#pc +ᵢ ($4 )+ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) /\ normal_cursor (R',F')) as CSR'. {
    splits. {
      asserts_rewrite (get_R pc R' = get_R npc R). iauto.
      asserts_rewrite (get_R npc R = (get_R pc R) +ᵢ ($ 4)). apply CSR.
      asserts_rewrite (get_R pc R = (get_R pc R_) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)). apply CSR.
      auto.
    }
    {
      unfolds.
        asserts_rewrite (get_R npc R' = (get_R npc R) +ᵢ ($ 4)). iauto.
        asserts_rewrite (get_R pc R'  = get_R npc R). iauto.
        auto.
    }
  }

  {
  assert (handler_context R') as IVR'. {
    unfolds.
    splits; try unfolds; try unfolds;
    try asserts_rewrite ((get_R cwp R') = (get_R cwp R));
    try asserts_rewrite ((get_R annul R') = (get_R annul R)); 
    try asserts_rewrite ((get_R et R') = (get_R et R));
    try asserts_rewrite ((get_R trap R') = (get_R trap R));
    try asserts_rewrite ((get_R s R') = (get_R s R));
    iauto; apply IVR.
  }

  assert (
   word_aligned_R R'#sp /\ memort_context R'#sp Ms' /\
   (let (Rr,Fr) := right_win 2 (R',F') in word_aligned_R Rr#l1 /\ word_aligned_R Rr#l2) /\ word_aligned_R (get_R r14 R') +ᵢ ($ 20)) as ALIGN'. {
    unfold align_context in ALIGN.
    splits.
    {
      asserts_rewrite ((get_R r14 R') = (get_R r14 R)). iauto. iauto.
    }
    {
      asserts_rewrite (Ms' = Ms). iauto.
      asserts_rewrite ((get_R r14 R') = (get_R r14 R)). iauto. iauto.
    }
    {

      remember (right_win 2 (R', F')) as K.
      destruct K as (Rrr',Frr').
      remember (right_win 2 (R, F)) as K.
      destruct K as (Rrr,Frr).
      asserts_rewrite ((get_R r17 Rrr')  = (get_R r17 Rrr)). {
        apply (Right2_Right2_Same R R' Rrr Rrr' F F' Frr Frr'); iauto.
      }
      asserts_rewrite ((get_R r18 Rrr')  = (get_R r18 Rrr)). {
        apply (Right2_Right2_Same R R' Rrr Rrr' F F' Frr Frr'); iauto.
      }
      iauto.
    }
    asserts_rewrite (get_R r14 R' = get_R r14 R). iauto. iauto.
  }

  assert (single_mask (post_cwp 1 R') (get_R wim R')) as MASK'. {
    asserts_rewrite ((get_R wim R') = (get_R wim R)). iauto.
    unfold post_cwp.
    unfold post_cwp in MASK.
    asserts_rewrite ((get_R cwp R') = (get_R cwp R)). iauto.
    iauto.
  }


  assert (D' = []) as DELAY'. {
    iauto.
  }


  assert (f_context F_restore /\ f_context F_restore_restore /\ f_context F') as CONT'. {
    splits; iauto.
    asserts_rewrite(F' = F). iauto.
    iauto.
  }

  assert (Z__ (Cu, Cs) (Mu, Ms_, (R_, F_),[]) [None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None] 16 (Mu, Ms', (R', F'),D')) as GOAL'. {
    apply (No_Event (Cu,Cs) [None;None;None;None;None;None;None;None;None;None;None;None;None;None;None] 15 (Mu, Ms_, (R_, F_),[]) (Mu, Ms', (R', F'),D') (Mu, Ms, (R, F),D));
    try rewrite DELAY in *; auto.
  }
  clear H P__ IVR MASK CSR DELAY ALIGN GOAL CONT TMP.
  clear Ms R F D.
  rename Ms' into Ms.
  rename R' into R.
  rename F' into F.
  rename D' into D.
  rename IVR' into IVR.
  rename MASK' into MASK.
  rename CSR' into CSR.
  rename DELAY' into DELAY.
  rename GOAL' into GOAL.
  rename ALIGN' into ALIGN.
  rename CONT' into CONT.






(* step 17 *)

  assert (not_abort Cs Ms (R,F) D) as NA. {
    unfolds.
    exists (R,F) D  (ld (sp+ₐₙ($24)) l6).
    splits.
    - substs. auto.
    - asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)  +ᵢ ($ 4) +ᵢ ($ 4)  +ᵢ ($ 4)  +ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)); iauto. apply FUNC.
    - unfolds. simpl. auto.
      asserts_rewrite(($ (-4096)) <=ᵢ ($ 24) && ($ 24) <=ᵢ ($ 4095) = true). {
        unfolds.
        asserts_rewrite (($ (-4096)) <=ᵢ ($ 24) = true). unfolds.
        asserts_rewrite (($ 24) >ᵢ ($ (-4096)) = true). mauto. auto. mauto. 
      }
      assert (exists v, Ms (R r14) +ᵢ ($ 24) = Some v). {
      assert ( memort_context (get_R r14 R) Ms). iauto.
      unfold memort_context in H.
      destruct H as (v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & v15 & v16 & H).
      exists v7.
      apply H.
      }
      inverts H.
      rewrite H0. auto.
  }

  (* to P__ *)
  assert
  (exists Ms' Q' D', P__ (Cu,Cs) ((Mu,Ms),(R,F),D) ((Mu,Ms'),Q',D')) as H. {
    apply (Exists_P_Sup Cu Cs Mu Ms (R,F) D);
    auto; try apply IVR.
  }
  destruct H as (Ms' & Q' & D' & P__).
  destruct Q' as (R' & F').
  clear NA.

  (* deal with delay *)
  rewrite DELAY in *.

  (* align *)
  assert (word_aligned_R (get_R r14 R)+ᵢ ($24)) as TMP. {
     asserts_rewrite (($ 24) = ($ 20) +ᵢ ($ 4)). {
      clear CSR. int auto.
    }
    rewrite <- Int.add_assoc.
    apply align_plus4. iauto.
  }


  (* small changes in one step *)
  assert (R'#pc = R#npc /\ R'#npc = R#npc +ᵢ ($4) /\
          R'#cwp = R#cwp /\ R'#annul = R#annul /\ R'#et = R#et /\ R'#trap = R#trap /\ R'#s = R#s /\ R'#wim = R#wim /\
          R'#sp = R#sp /\ F' = F /\ D' = [] /\ Ms' = Ms). {
  inverts P__.
  (* usr_mode *) {
    false. apply (ModeDeq (R,F)); auto.
    apply IVR.
  }

  (* sup_mode *) {
    inverts H10.
    unfolds in H6.
    inverts H6.
    assert (Cs (cursor_Q (R, F)) = Some (ld (sp+ₐₙ($24)) l6)) as INS. {
    asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4)  +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)  +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) ). iauto.
    apply FUNC.
    }
    rewrite H11 in INS.
    clear H11. inverts INS.

    {
    inverts H12; try solve [false].
    inverts H5; try solve [false].
    inverts H6.
    splits;inverts H4;iauto.
    (* trap? no !*){
    inverts H4.
    asserts_rewrite(($ (-4096)) <=ᵢ ($ 24) && ($ 24) <=ᵢ ($ 4095) = true) in H0. {
       unfolds.
       asserts_rewrite (($ (-4096)) <=ᵢ ($ 24) = true). unfolds.
       asserts_rewrite (($ 24) >ᵢ ($ (-4096)) = true). mauto. auto. mauto. 
    }
    asserts_rewrite (word_aligned (R r14) +ᵢ ($ 24) = true) in H0. iauto.
    simpl in H0.
    inverts H0.
    }
    }
    (* annul? no !*){
    inverts H5.
    false.
    apply (AnnulDeq R).
    apply H8. apply IVR.
    }
  }
  }



  assert (R'#pc = R_#pc +ᵢ ($4 )+ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) /\ normal_cursor (R',F')) as CSR'. {
    splits. {
      asserts_rewrite (get_R pc R' = get_R npc R). iauto.
      asserts_rewrite (get_R npc R = (get_R pc R) +ᵢ ($ 4)). apply CSR.
      asserts_rewrite (get_R pc R = (get_R pc R_) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)). apply CSR.
      auto.
    }
    {
      unfolds.
        asserts_rewrite (get_R npc R' = (get_R npc R) +ᵢ ($ 4)). iauto.
        asserts_rewrite (get_R pc R'  = get_R npc R). iauto.
        auto.
    }
  }

  {
  assert (handler_context R') as IVR'. {
    unfolds.
    splits; try unfolds; try unfolds;
    try asserts_rewrite ((get_R cwp R') = (get_R cwp R));
    try asserts_rewrite ((get_R annul R') = (get_R annul R)); 
    try asserts_rewrite ((get_R et R') = (get_R et R));
    try asserts_rewrite ((get_R trap R') = (get_R trap R));
    try asserts_rewrite ((get_R s R') = (get_R s R));
    iauto; apply IVR.
  }

  assert (
   word_aligned_R R'#sp /\ memort_context R'#sp Ms' /\
   (let (Rr,Fr) := right_win 2 (R',F') in word_aligned_R Rr#l1 /\ word_aligned_R Rr#l2) /\ word_aligned_R (get_R r14 R') +ᵢ ($ 24)) as ALIGN'. {
    unfold align_context in ALIGN.
    splits.
    {
      asserts_rewrite ((get_R r14 R') = (get_R r14 R)). iauto. iauto.
    }
    {
      asserts_rewrite (Ms' = Ms). iauto.
      asserts_rewrite ((get_R r14 R') = (get_R r14 R)). iauto. iauto.
    }
    {

      remember (right_win 2 (R', F')) as K.
      destruct K as (Rrr',Frr').
      remember (right_win 2 (R, F)) as K.
      destruct K as (Rrr,Frr).
      asserts_rewrite ((get_R r17 Rrr')  = (get_R r17 Rrr)). {
        apply (Right2_Right2_Same R R' Rrr Rrr' F F' Frr Frr'); iauto.
      }
      asserts_rewrite ((get_R r18 Rrr')  = (get_R r18 Rrr)). {
        apply (Right2_Right2_Same R R' Rrr Rrr' F F' Frr Frr'); iauto.
      }
      iauto.
    }
    asserts_rewrite (get_R r14 R' = get_R r14 R). iauto. iauto.
  }

  assert (single_mask (post_cwp 1 R') (get_R wim R')) as MASK'. {
    asserts_rewrite ((get_R wim R') = (get_R wim R)). iauto.
    unfold post_cwp.
    unfold post_cwp in MASK.
    asserts_rewrite ((get_R cwp R') = (get_R cwp R)). iauto.
    iauto.
  }


  assert (D' = []) as DELAY'. {
    iauto.
  }


  assert (f_context F_restore /\ f_context F_restore_restore /\ f_context F') as CONT'. {
    splits; iauto.
    asserts_rewrite(F' = F). iauto.
    iauto.
  }

  assert (Z__ (Cu, Cs) (Mu, Ms_, (R_, F_),[]) [None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None] 17 (Mu, Ms', (R', F'),D')) as GOAL'. {
    apply (No_Event (Cu,Cs) [None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None] 16 (Mu, Ms_, (R_, F_),[]) (Mu, Ms', (R', F'),D') (Mu, Ms, (R, F),D));
    try rewrite DELAY in *; auto.
  }
  clear H P__ IVR MASK CSR DELAY ALIGN GOAL CONT TMP.
  clear Ms R F D.
  rename Ms' into Ms.
  rename R' into R.
  rename F' into F.
  rename D' into D.
  rename IVR' into IVR.
  rename MASK' into MASK.
  rename CSR' into CSR.
  rename DELAY' into DELAY.
  rename GOAL' into GOAL.
  rename ALIGN' into ALIGN.
  rename CONT' into CONT.





(* step 18 *)

  assert (not_abort Cs Ms (R,F) D) as NA. {
    unfolds.
    exists (R,F) D  (ld (sp+ₐₙ($28)) l7).
    splits.
    - substs. auto.
    - asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)  +ᵢ ($ 4) +ᵢ ($ 4)  +ᵢ ($ 4)  +ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)); iauto. apply FUNC.
    - unfolds. simpl. auto.
      asserts_rewrite(($ (-4096)) <=ᵢ ($ 28) && ($ 28) <=ᵢ ($ 4095) = true). {
        unfolds.
        asserts_rewrite (($ (-4096)) <=ᵢ ($ 28) = true). unfolds.
        asserts_rewrite (($ 28) >ᵢ ($ (-4096)) = true). mauto. auto. mauto. 
      }
      assert (exists v, Ms (R r14) +ᵢ ($ 28) = Some v). {
      assert ( memort_context (get_R r14 R) Ms). iauto.
      unfold memort_context in H.
      destruct H as (v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & v15 & v16 & H).
      exists v8.
      apply H.
      }
      inverts H.
      rewrite H0. auto.
  }

  (* to P__ *)
  assert
  (exists Ms' Q' D', P__ (Cu,Cs) ((Mu,Ms),(R,F),D) ((Mu,Ms'),Q',D')) as H. {
    apply (Exists_P_Sup Cu Cs Mu Ms (R,F) D);
    auto; try apply IVR.
  }
  destruct H as (Ms' & Q' & D' & P__).
  destruct Q' as (R' & F').
  clear NA.

  (* deal with delay *)
  rewrite DELAY in *.

  (* align *)
  assert (word_aligned_R (get_R r14 R)+ᵢ ($28)) as TMP. {
     asserts_rewrite (($ 28) = ($ 24) +ᵢ ($ 4)). {
      clear CSR. int auto.
    }
    rewrite <- Int.add_assoc.
    apply align_plus4. iauto.
  }


  (* small changes in one step *)
  assert (R'#pc = R#npc /\ R'#npc = R#npc +ᵢ ($4) /\
          R'#cwp = R#cwp /\ R'#annul = R#annul /\ R'#et = R#et /\ R'#trap = R#trap /\ R'#s = R#s /\ R'#wim = R#wim /\
          R'#sp = R#sp /\ F' = F /\ D' = [] /\ Ms' = Ms). {
  inverts P__.
  (* usr_mode *) {
    false. apply (ModeDeq (R,F)); auto.
    apply IVR.
  }

  (* sup_mode *) {
    inverts H10.
    unfolds in H6.
    inverts H6.
    assert (Cs (cursor_Q (R, F)) = Some (ld (sp+ₐₙ($28)) l7)) as INS. {
    asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)  +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)  +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) ). iauto.
    apply FUNC.
    }
    rewrite H11 in INS.
    clear H11. inverts INS.

    {
    inverts H12; try solve [false].
    inverts H5; try solve [false].
    inverts H6.
    splits;inverts H4;iauto.
    (* trap? no !*){
    inverts H4.
    asserts_rewrite(($ (-4096)) <=ᵢ ($ 28) && ($ 28) <=ᵢ ($ 4095) = true) in H0. {
       unfolds.
       asserts_rewrite (($ (-4096)) <=ᵢ ($ 28) = true). unfolds.
       asserts_rewrite (($ 28) >ᵢ ($ (-4096)) = true). mauto. auto. mauto. 
    }
    asserts_rewrite (word_aligned (R r14) +ᵢ ($ 28) = true) in H0. iauto.
    simpl in H0.
    inverts H0.
    }
    }
    (* annul? no !*){
    inverts H5.
    false.
    apply (AnnulDeq R).
    apply H8. apply IVR.
    }
  }
  }



  assert (R'#pc = R_#pc +ᵢ ($4 ) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) /\ normal_cursor (R',F')) as CSR'. {
    splits. {
      asserts_rewrite (get_R pc R' = get_R npc R). iauto.
      asserts_rewrite (get_R npc R = (get_R pc R) +ᵢ ($ 4)). apply CSR.
      asserts_rewrite (get_R pc R = (get_R pc R_)  +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)). apply CSR.
      auto.
    }
    {
      unfolds.
        asserts_rewrite (get_R npc R' = (get_R npc R) +ᵢ ($ 4)). iauto.
        asserts_rewrite (get_R pc R'  = get_R npc R). iauto.
        auto.
    }
  }

  {
  assert (handler_context R') as IVR'. {
    unfolds.
    splits; try unfolds; try unfolds;
    try asserts_rewrite ((get_R cwp R') = (get_R cwp R));
    try asserts_rewrite ((get_R annul R') = (get_R annul R)); 
    try asserts_rewrite ((get_R et R') = (get_R et R));
    try asserts_rewrite ((get_R trap R') = (get_R trap R));
    try asserts_rewrite ((get_R s R') = (get_R s R));
    iauto; apply IVR.
  }

  assert (
   word_aligned_R R'#sp /\ memort_context R'#sp Ms' /\
   (let (Rr,Fr) := right_win 2 (R',F') in word_aligned_R Rr#l1 /\ word_aligned_R Rr#l2) /\ word_aligned_R (get_R r14 R') +ᵢ ($ 28)) as ALIGN'. {
    unfold align_context in ALIGN.
    splits.
    {
      asserts_rewrite ((get_R r14 R') = (get_R r14 R)). iauto. iauto.
    }
    {
      asserts_rewrite (Ms' = Ms). iauto.
      asserts_rewrite ((get_R r14 R') = (get_R r14 R)). iauto. iauto.
    }
    {

      remember (right_win 2 (R', F')) as K.
      destruct K as (Rrr',Frr').
      remember (right_win 2 (R, F)) as K.
      destruct K as (Rrr,Frr).
      asserts_rewrite ((get_R r17 Rrr')  = (get_R r17 Rrr)). {
        apply (Right2_Right2_Same R R' Rrr Rrr' F F' Frr Frr'); iauto.
      }
      asserts_rewrite ((get_R r18 Rrr')  = (get_R r18 Rrr)). {
        apply (Right2_Right2_Same R R' Rrr Rrr' F F' Frr Frr'); iauto.
      }
      iauto.
    }
    asserts_rewrite (get_R r14 R' = get_R r14 R). iauto. iauto.
  }

  assert (single_mask (post_cwp 1 R') (get_R wim R')) as MASK'. {
    asserts_rewrite ((get_R wim R') = (get_R wim R)). iauto.
    unfold post_cwp.
    unfold post_cwp in MASK.
    asserts_rewrite ((get_R cwp R') = (get_R cwp R)). iauto.
    iauto.
  }


  assert (D' = []) as DELAY'. {
    iauto.
  }


  assert (f_context F_restore /\ f_context F_restore_restore /\ f_context F') as CONT'. {
    splits; iauto.
    asserts_rewrite(F' = F). iauto.
    iauto.
  }

  assert (Z__ (Cu, Cs) (Mu, Ms_, (R_, F_),[]) [None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None] 18 (Mu, Ms', (R', F'),D')) as GOAL'. {
    apply (No_Event (Cu,Cs) [None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None] 17 (Mu, Ms_, (R_, F_),[]) (Mu, Ms', (R', F'),D') (Mu, Ms, (R, F),D));
    try rewrite DELAY in *; auto.
  }
  clear H P__ IVR MASK CSR DELAY ALIGN GOAL CONT TMP.
  clear Ms R F D.
  rename Ms' into Ms.
  rename R' into R.
  rename F' into F.
  rename D' into D.
  rename IVR' into IVR.
  rename MASK' into MASK.
  rename CSR' into CSR.
  rename DELAY' into DELAY.
  rename GOAL' into GOAL.
  rename ALIGN' into ALIGN.
  rename CONT' into CONT.






(* step 19 *)

  assert (not_abort Cs Ms (R,F) D) as NA. {
    unfolds.
    exists (R,F) D  (ld (sp+ₐₙ($32)) i0).
    splits.
    - substs. auto.
    - asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)  +ᵢ ($ 4) +ᵢ ($ 4)  +ᵢ ($ 4)  +ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)); iauto. apply FUNC.
    - unfolds. simpl. auto.
      asserts_rewrite(($ (-4096)) <=ᵢ ($ 32) && ($ 32) <=ᵢ ($ 4095) = true). {
        unfolds.
        asserts_rewrite (($ (-4096)) <=ᵢ ($ 32) = true). unfolds.
        asserts_rewrite (($ 32) >ᵢ ($ (-4096)) = true). mauto. auto. mauto. 
      }
      assert (exists v, Ms (R r14) +ᵢ ($ 32) = Some v). {
      assert ( memort_context (get_R r14 R) Ms). iauto.
      unfold memort_context in H.
      destruct H as (v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & v15 & v16 & H).
      exists v9.
      apply H.
      }
      inverts H.
      rewrite H0. auto.
  }

  (* to P__ *)
  assert
  (exists Ms' Q' D', P__ (Cu,Cs) ((Mu,Ms),(R,F),D) ((Mu,Ms'),Q',D')) as H. {
    apply (Exists_P_Sup Cu Cs Mu Ms (R,F) D);
    auto; try apply IVR.
  }
  destruct H as (Ms' & Q' & D' & P__).
  destruct Q' as (R' & F').
  clear NA.

  (* deal with delay *)
  rewrite DELAY in *.

  (* align *)
  assert (word_aligned_R (get_R r14 R)+ᵢ ($32)) as TMP. {
     asserts_rewrite (($ 32) = ($ 28) +ᵢ ($ 4)). {
      clear CSR. int auto.
    }
    rewrite <- Int.add_assoc.
    apply align_plus4. iauto.
  }


  (* small changes in one step *)
  assert (R'#pc = R#npc /\ R'#npc = R#npc +ᵢ ($4) /\
          R'#cwp = R#cwp /\ R'#annul = R#annul /\ R'#et = R#et /\ R'#trap = R#trap /\ R'#s = R#s /\ R'#wim = R#wim /\
          R'#sp = R#sp /\ F' = F /\ D' = [] /\ Ms' = Ms). {
  inverts P__.
  (* usr_mode *) {
    false. apply (ModeDeq (R,F)); auto.
    apply IVR.
  }

  (* sup_mode *) {
    inverts H10.
    unfolds in H6.
    inverts H6.
    assert (Cs (cursor_Q (R, F)) = Some (ld (sp+ₐₙ($32)) i0)) as INS. {
    asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)  +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)  +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) ). iauto.
    apply FUNC.
    }
    rewrite H11 in INS.
    clear H11. inverts INS.

    {
    inverts H12; try solve [false].
    inverts H5; try solve [false].
    inverts H6.
    splits;inverts H4;iauto.
    (* trap? no !*){
    inverts H4.
    asserts_rewrite(($ (-4096)) <=ᵢ ($ 32) && ($ 32) <=ᵢ ($ 4095) = true) in H0. {
       unfolds.
       asserts_rewrite (($ (-4096)) <=ᵢ ($ 32) = true). unfolds.
       asserts_rewrite (($ 32) >ᵢ ($ (-4096)) = true). mauto. auto. mauto. 
    }
    asserts_rewrite (word_aligned (R r14) +ᵢ ($ 32) = true) in H0. iauto.
    simpl in H0.
    inverts H0.
    }
    }
    (* annul? no !*){
    inverts H5.
    false.
    apply (AnnulDeq R).
    apply H8. apply IVR.
    }
  }
  }



  assert (R'#pc = R_#pc +ᵢ ($4 ) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) /\ normal_cursor (R',F')) as CSR'. {
    splits. {
      asserts_rewrite (get_R pc R' = get_R npc R). iauto.
      asserts_rewrite (get_R npc R = (get_R pc R) +ᵢ ($ 4)). apply CSR.
      asserts_rewrite (get_R pc R = (get_R pc R_)  +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)). apply CSR.
      auto.
    }
    {
      unfolds.
        asserts_rewrite (get_R npc R' = (get_R npc R) +ᵢ ($ 4)). iauto.
        asserts_rewrite (get_R pc R'  = get_R npc R). iauto.
        auto.
    }
  }

  {
  assert (handler_context R') as IVR'. {
    unfolds.
    splits; try unfolds; try unfolds;
    try asserts_rewrite ((get_R cwp R') = (get_R cwp R));
    try asserts_rewrite ((get_R annul R') = (get_R annul R)); 
    try asserts_rewrite ((get_R et R') = (get_R et R));
    try asserts_rewrite ((get_R trap R') = (get_R trap R));
    try asserts_rewrite ((get_R s R') = (get_R s R));
    iauto; apply IVR.
  }

  assert (
   word_aligned_R R'#sp /\ memort_context R'#sp Ms' /\
   (let (Rr,Fr) := right_win 2 (R',F') in word_aligned_R Rr#l1 /\ word_aligned_R Rr#l2) /\ word_aligned_R (get_R r14 R') +ᵢ ($ 32)) as ALIGN'. {
    unfold align_context in ALIGN.
    splits.
    {
      asserts_rewrite ((get_R r14 R') = (get_R r14 R)). iauto. iauto.
    }
    {
      asserts_rewrite (Ms' = Ms). iauto.
      asserts_rewrite ((get_R r14 R') = (get_R r14 R)). iauto. iauto.
    }
    {

      remember (right_win 2 (R', F')) as K.
      destruct K as (Rrr',Frr').
      remember (right_win 2 (R, F)) as K.
      destruct K as (Rrr,Frr).
      asserts_rewrite ((get_R r17 Rrr')  = (get_R r17 Rrr)). {
        apply (Right2_Right2_Same R R' Rrr Rrr' F F' Frr Frr'); iauto.
      }
      asserts_rewrite ((get_R r18 Rrr')  = (get_R r18 Rrr)). {
        apply (Right2_Right2_Same R R' Rrr Rrr' F F' Frr Frr'); iauto.
      }
      iauto.
    }
    asserts_rewrite (get_R r14 R' = get_R r14 R). iauto. iauto.
  }

  assert (single_mask (post_cwp 1 R') (get_R wim R')) as MASK'. {
    asserts_rewrite ((get_R wim R') = (get_R wim R)). iauto.
    unfold post_cwp.
    unfold post_cwp in MASK.
    asserts_rewrite ((get_R cwp R') = (get_R cwp R)). iauto.
    iauto.
  }


  assert (D' = []) as DELAY'. {
    iauto.
  }


  assert (f_context F_restore /\ f_context F_restore_restore /\ f_context F') as CONT'. {
    splits; iauto.
    asserts_rewrite(F' = F). iauto.
    iauto.
  }

  assert (Z__ (Cu, Cs) (Mu, Ms_, (R_, F_),[]) [None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None] 19 (Mu, Ms', (R', F'),D')) as GOAL'. {
    apply (No_Event (Cu,Cs) [None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None] 18 (Mu, Ms_, (R_, F_),[]) (Mu, Ms', (R', F'),D') (Mu, Ms, (R, F),D));
    try rewrite DELAY in *; auto.
  }
  clear H P__ IVR MASK CSR DELAY ALIGN GOAL CONT TMP.
  clear Ms R F D.
  rename Ms' into Ms.
  rename R' into R.
  rename F' into F.
  rename D' into D.
  rename IVR' into IVR.
  rename MASK' into MASK.
  rename CSR' into CSR.
  rename DELAY' into DELAY.
  rename GOAL' into GOAL.
  rename ALIGN' into ALIGN.
  rename CONT' into CONT.







(* step 20 *)

  assert (not_abort Cs Ms (R,F) D) as NA. {
    unfolds.
    exists (R,F) D  (ld (sp+ₐₙ($36)) i1).
    splits.
    - substs. auto.
    - asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)  +ᵢ ($ 4) +ᵢ ($ 4)  +ᵢ ($ 4)  +ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)); iauto. apply FUNC.
    - unfolds. simpl. auto.
      asserts_rewrite(($ (-4096)) <=ᵢ ($ 36) && ($ 36) <=ᵢ ($ 4095) = true). {
        unfolds.
        asserts_rewrite (($ (-4096)) <=ᵢ ($ 36) = true). unfolds.
        asserts_rewrite (($ 36) >ᵢ ($ (-4096)) = true). mauto. auto. mauto. 
      }
      assert (exists v, Ms (R r14) +ᵢ ($ 36) = Some v). {
      assert ( memort_context (get_R r14 R) Ms). iauto.
      unfold memort_context in H.
      destruct H as (v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & v15 & v16 & H).
      exists v10.
      apply H.
      }
      inverts H.
      rewrite H0. auto.
  }

  (* to P__ *)
  assert
  (exists Ms' Q' D', P__ (Cu,Cs) ((Mu,Ms),(R,F),D) ((Mu,Ms'),Q',D')) as H. {
    apply (Exists_P_Sup Cu Cs Mu Ms (R,F) D);
    auto; try apply IVR.
  }
  destruct H as (Ms' & Q' & D' & P__).
  destruct Q' as (R' & F').
  clear NA.

  (* deal with delay *)
  rewrite DELAY in *.

  (* align *)
  assert (word_aligned_R (get_R r14 R)+ᵢ ($36)) as TMP. {
     asserts_rewrite (($ 36) = ($ 32) +ᵢ ($ 4)). {
      clear CSR. int auto.
    }
    rewrite <- Int.add_assoc.
    apply align_plus4. iauto.
  }


  (* small changes in one step *)
  assert (R'#pc = R#npc /\ R'#npc = R#npc +ᵢ ($4) /\
          R'#cwp = R#cwp /\ R'#annul = R#annul /\ R'#et = R#et /\ R'#trap = R#trap /\ R'#s = R#s /\ R'#wim = R#wim /\
          R'#sp = R#sp /\ F' = F /\ D' = [] /\ Ms' = Ms). {
  inverts P__.
  (* usr_mode *) {
    false. apply (ModeDeq (R,F)); auto.
    apply IVR.
  }

  (* sup_mode *) {
    inverts H10.
    unfolds in H6.
    inverts H6.
    assert (Cs (cursor_Q (R, F)) = Some (ld (sp+ₐₙ($36)) i1)) as INS. {
    asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)  +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)  +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) ). iauto.
    apply FUNC.
    }
    rewrite H11 in INS.
    clear H11. inverts INS.

    {
    inverts H12; try solve [false].
    inverts H5; try solve [false].
    inverts H6.
    splits;inverts H4;iauto.
    (* trap? no !*){
    inverts H4.
    asserts_rewrite(($ (-4096)) <=ᵢ ($ 36) && ($ 36) <=ᵢ ($ 4095) = true) in H0. {
       unfolds.
       asserts_rewrite (($ (-4096)) <=ᵢ ($ 36) = true). unfolds.
       asserts_rewrite (($ 36) >ᵢ ($ (-4096)) = true). mauto. auto. mauto. 
    }
    asserts_rewrite (word_aligned (R r14) +ᵢ ($ 36) = true) in H0. iauto.
    simpl in H0.
    inverts H0.
    }
    }
    (* annul? no !*){
    inverts H5.
    false.
    apply (AnnulDeq R).
    apply H8. apply IVR.
    }
  }
  }



  assert (R'#pc = R_#pc +ᵢ ($4 ) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)  +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) /\ normal_cursor (R',F')) as CSR'. {
    splits. {
      asserts_rewrite (get_R pc R' = get_R npc R). iauto.
      asserts_rewrite (get_R npc R = (get_R pc R) +ᵢ ($ 4)). apply CSR.
      asserts_rewrite (get_R pc R = (get_R pc R_)   +ᵢ ($4)  +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)). apply CSR.
      auto.
    }
    {
      unfolds.
        asserts_rewrite (get_R npc R' = (get_R npc R) +ᵢ ($ 4)). iauto.
        asserts_rewrite (get_R pc R'  = get_R npc R). iauto.
        auto.
    }
  }

  {
  assert (handler_context R') as IVR'. {
    unfolds.
    splits; try unfolds; try unfolds;
    try asserts_rewrite ((get_R cwp R') = (get_R cwp R));
    try asserts_rewrite ((get_R annul R') = (get_R annul R)); 
    try asserts_rewrite ((get_R et R') = (get_R et R));
    try asserts_rewrite ((get_R trap R') = (get_R trap R));
    try asserts_rewrite ((get_R s R') = (get_R s R));
    iauto; apply IVR.
  }

  assert (
   word_aligned_R R'#sp /\ memort_context R'#sp Ms' /\
   (let (Rr,Fr) := right_win 2 (R',F') in word_aligned_R Rr#l1 /\ word_aligned_R Rr#l2) /\ word_aligned_R (get_R r14 R') +ᵢ ($ 36)) as ALIGN'. {
    unfold align_context in ALIGN.
    splits.
    {
      asserts_rewrite ((get_R r14 R') = (get_R r14 R)). iauto. iauto.
    }
    {
      asserts_rewrite (Ms' = Ms). iauto.
      asserts_rewrite ((get_R r14 R') = (get_R r14 R)). iauto. iauto.
    }
    {

      remember (right_win 2 (R', F')) as K.
      destruct K as (Rrr',Frr').
      remember (right_win 2 (R, F)) as K.
      destruct K as (Rrr,Frr).
      asserts_rewrite ((get_R r17 Rrr')  = (get_R r17 Rrr)). {
        apply (Right2_Right2_Same R R' Rrr Rrr' F F' Frr Frr'); iauto.
      }
      asserts_rewrite ((get_R r18 Rrr')  = (get_R r18 Rrr)). {
        apply (Right2_Right2_Same R R' Rrr Rrr' F F' Frr Frr'); iauto.
      }
      iauto.
    }
    asserts_rewrite (get_R r14 R' = get_R r14 R). iauto. iauto.
  }

  assert (single_mask (post_cwp 1 R') (get_R wim R')) as MASK'. {
    asserts_rewrite ((get_R wim R') = (get_R wim R)). iauto.
    unfold post_cwp.
    unfold post_cwp in MASK.
    asserts_rewrite ((get_R cwp R') = (get_R cwp R)). iauto.
    iauto.
  }


  assert (D' = []) as DELAY'. {
    iauto.
  }


  assert (f_context F_restore /\ f_context F_restore_restore /\ f_context F') as CONT'. {
    splits; iauto.
    asserts_rewrite(F' = F). iauto.
    iauto.
  }

  assert (Z__ (Cu, Cs) (Mu, Ms_, (R_, F_),[]) [None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None] 20 (Mu, Ms', (R', F'),D')) as GOAL'. {
    apply (No_Event (Cu,Cs) [None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None] 19 (Mu, Ms_, (R_, F_),[]) (Mu, Ms', (R', F'),D') (Mu, Ms, (R, F),D));
    try rewrite DELAY in *; auto.
  }
  clear H P__ IVR MASK CSR DELAY ALIGN GOAL CONT TMP.
  clear Ms R F D.
  rename Ms' into Ms.
  rename R' into R.
  rename F' into F.
  rename D' into D.
  rename IVR' into IVR.
  rename MASK' into MASK.
  rename CSR' into CSR.
  rename DELAY' into DELAY.
  rename GOAL' into GOAL.
  rename ALIGN' into ALIGN.
  rename CONT' into CONT.














(* step 21 *)

  assert (not_abort Cs Ms (R,F) D) as NA. {
    unfolds.
    exists (R,F) D  (ld (sp+ₐₙ($40)) i2).
    splits.
    - substs. auto.
    - asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)  +ᵢ ($ 4) +ᵢ ($ 4)  +ᵢ ($ 4)  +ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)); iauto. apply FUNC.
    - unfolds. simpl. auto.
      asserts_rewrite(($ (-4096)) <=ᵢ ($ 40) && ($ 40) <=ᵢ ($ 4095) = true). {
        unfolds.
        asserts_rewrite (($ (-4096)) <=ᵢ ($ 40) = true). unfolds.
        asserts_rewrite (($ 40) >ᵢ ($ (-4096)) = true). mauto. auto. mauto. 
      }
      assert (exists v, Ms (R r14) +ᵢ ($ 40) = Some v). {
      assert ( memort_context (get_R r14 R) Ms). iauto.
      unfold memort_context in H.
      destruct H as (v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & v15 & v16 & H).
      exists v11.
      apply H.
      }
      inverts H.
      rewrite H0. auto.
  }

  (* to P__ *)
  assert
  (exists Ms' Q' D', P__ (Cu,Cs) ((Mu,Ms),(R,F),D) ((Mu,Ms'),Q',D')) as H. {
    apply (Exists_P_Sup Cu Cs Mu Ms (R,F) D);
    auto; try apply IVR.
  }
  destruct H as (Ms' & Q' & D' & P__).
  destruct Q' as (R' & F').
  clear NA.

  (* deal with delay *)
  rewrite DELAY in *.

  (* align *)
  assert (word_aligned_R (get_R r14 R)+ᵢ ($40)) as TMP. {
     asserts_rewrite (($ 40) = ($ 36) +ᵢ ($ 4)). {
      clear CSR. int auto.
    }
    rewrite <- Int.add_assoc.
    apply align_plus4. iauto.
  }


  (* small changes in one step *)
  assert (R'#pc = R#npc /\ R'#npc = R#npc +ᵢ ($4) /\
          R'#cwp = R#cwp /\ R'#annul = R#annul /\ R'#et = R#et /\ R'#trap = R#trap /\ R'#s = R#s /\ R'#wim = R#wim /\
          R'#sp = R#sp /\ F' = F /\ D' = [] /\ Ms' = Ms). {
  inverts P__.
  (* usr_mode *) {
    false. apply (ModeDeq (R,F)); auto.
    apply IVR.
  }

  (* sup_mode *) {
    inverts H10.
    unfolds in H6.
    inverts H6.
    assert (Cs (cursor_Q (R, F)) = Some (ld (sp+ₐₙ($40)) i2)) as INS. {
    asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)  +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)  +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) ). iauto.
    apply FUNC.
    }
    rewrite H11 in INS.
    clear H11. inverts INS.

    {
    inverts H12; try solve [false].
    inverts H5; try solve [false].
    inverts H6.
    splits;inverts H4;iauto.
    (* trap? no !*){
    inverts H4.
    asserts_rewrite(($ (-4096)) <=ᵢ ($ 40) && ($ 40) <=ᵢ ($ 4095) = true) in H0. {
       unfolds.
       asserts_rewrite (($ (-4096)) <=ᵢ ($ 40) = true). unfolds.
       asserts_rewrite (($ 40) >ᵢ ($ (-4096)) = true). mauto. auto. mauto. 
    }
    asserts_rewrite (word_aligned (R r14) +ᵢ ($ 40) = true) in H0. iauto.
    simpl in H0.
    inverts H0.
    }
    }
    (* annul? no !*){
    inverts H5.
    false.
    apply (AnnulDeq R).
    apply H8. apply IVR.
    }
  }
  }



  assert (R'#pc = R_#pc +ᵢ ($4 ) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)  +ᵢ ($4)  +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) /\ normal_cursor (R',F')) as CSR'. {
    splits. {
      asserts_rewrite (get_R pc R' = get_R npc R). iauto.
      asserts_rewrite (get_R npc R = (get_R pc R) +ᵢ ($ 4)). apply CSR.
      asserts_rewrite (get_R pc R = (get_R pc R_)  +ᵢ ($4) +ᵢ ($4)  +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)). apply CSR.
      auto.
    }
    {
      unfolds.
        asserts_rewrite (get_R npc R' = (get_R npc R) +ᵢ ($ 4)). iauto.
        asserts_rewrite (get_R pc R'  = get_R npc R). iauto.
        auto.
    }
  }

  {
  assert (handler_context R') as IVR'. {
    unfolds.
    splits; try unfolds; try unfolds;
    try asserts_rewrite ((get_R cwp R') = (get_R cwp R));
    try asserts_rewrite ((get_R annul R') = (get_R annul R)); 
    try asserts_rewrite ((get_R et R') = (get_R et R));
    try asserts_rewrite ((get_R trap R') = (get_R trap R));
    try asserts_rewrite ((get_R s R') = (get_R s R));
    iauto; apply IVR.
  }

  assert (
   word_aligned_R R'#sp /\ memort_context R'#sp Ms' /\
   (let (Rr,Fr) := right_win 2 (R',F') in word_aligned_R Rr#l1 /\ word_aligned_R Rr#l2) /\ word_aligned_R (get_R r14 R') +ᵢ ($ 40)) as ALIGN'. {
    unfold align_context in ALIGN.
    splits.
    {
      asserts_rewrite ((get_R r14 R') = (get_R r14 R)). iauto. iauto.
    }
    {
      asserts_rewrite (Ms' = Ms). iauto.
      asserts_rewrite ((get_R r14 R') = (get_R r14 R)). iauto. iauto.
    }
    {

      remember (right_win 2 (R', F')) as K.
      destruct K as (Rrr',Frr').
      remember (right_win 2 (R, F)) as K.
      destruct K as (Rrr,Frr).
      asserts_rewrite ((get_R r17 Rrr')  = (get_R r17 Rrr)). {
        apply (Right2_Right2_Same R R' Rrr Rrr' F F' Frr Frr'); iauto.
      }
      asserts_rewrite ((get_R r18 Rrr')  = (get_R r18 Rrr)). {
        apply (Right2_Right2_Same R R' Rrr Rrr' F F' Frr Frr'); iauto.
      }
      iauto.
    }
    asserts_rewrite (get_R r14 R' = get_R r14 R). iauto. iauto.
  }

  assert (single_mask (post_cwp 1 R') (get_R wim R')) as MASK'. {
    asserts_rewrite ((get_R wim R') = (get_R wim R)). iauto.
    unfold post_cwp.
    unfold post_cwp in MASK.
    asserts_rewrite ((get_R cwp R') = (get_R cwp R)). iauto.
    iauto.
  }


  assert (D' = []) as DELAY'. {
    iauto.
  }


  assert (f_context F_restore /\ f_context F_restore_restore /\ f_context F') as CONT'. {
    splits; iauto.
    asserts_rewrite(F' = F). iauto.
    iauto.
  }

  assert (Z__ (Cu, Cs) (Mu, Ms_, (R_, F_),[]) [None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None] 21 (Mu, Ms', (R', F'),D')) as GOAL'. {
    apply (No_Event (Cu,Cs) [None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None] 20 (Mu, Ms_, (R_, F_),[]) (Mu, Ms', (R', F'),D') (Mu, Ms, (R, F),D));
    try rewrite DELAY in *; auto.
  }
  clear H P__ IVR MASK CSR DELAY ALIGN GOAL CONT TMP.
  clear Ms R F D.
  rename Ms' into Ms.
  rename R' into R.
  rename F' into F.
  rename D' into D.
  rename IVR' into IVR.
  rename MASK' into MASK.
  rename CSR' into CSR.
  rename DELAY' into DELAY.
  rename GOAL' into GOAL.
  rename ALIGN' into ALIGN.
  rename CONT' into CONT.








(* step 22 *)

  assert (not_abort Cs Ms (R,F) D) as NA. {
    unfolds.
    exists (R,F) D  (ld (sp+ₐₙ($44)) i3).
    splits.
    - substs. auto.
    - asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)  +ᵢ ($ 4) +ᵢ ($ 4)  +ᵢ ($ 4)  +ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)); iauto. apply FUNC.
    - unfolds. simpl. auto.
      asserts_rewrite(($ (-4096)) <=ᵢ ($ 44) && ($ 44) <=ᵢ ($ 4095) = true). {
        unfolds.
        asserts_rewrite (($ (-4096)) <=ᵢ ($ 44) = true). unfolds.
        asserts_rewrite (($ 44) >ᵢ ($ (-4096)) = true). mauto. auto. mauto. 
      }
      assert (exists v, Ms (R r14) +ᵢ ($ 44) = Some v). {
      assert ( memort_context (get_R r14 R) Ms). iauto.
      unfold memort_context in H.
      destruct H as (v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & v15 & v16 & H).
      exists v12.
      apply H.
      }
      inverts H.
      rewrite H0. auto.
  }

  (* to P__ *)
  assert
  (exists Ms' Q' D', P__ (Cu,Cs) ((Mu,Ms),(R,F),D) ((Mu,Ms'),Q',D')) as H. {
    apply (Exists_P_Sup Cu Cs Mu Ms (R,F) D);
    auto; try apply IVR.
  }
  destruct H as (Ms' & Q' & D' & P__).
  destruct Q' as (R' & F').
  clear NA.

  (* deal with delay *)
  rewrite DELAY in *.

  (* align *)
  assert (word_aligned_R (get_R r14 R)+ᵢ ($44)) as TMP. {
     asserts_rewrite (($ 44) = ($ 40) +ᵢ ($ 4)). {
      clear CSR. int auto.
    }
    rewrite <- Int.add_assoc.
    apply align_plus4. iauto.
  }


  (* small changes in one step *)
  assert (R'#pc = R#npc /\ R'#npc = R#npc +ᵢ ($4) /\
          R'#cwp = R#cwp /\ R'#annul = R#annul /\ R'#et = R#et /\ R'#trap = R#trap /\ R'#s = R#s /\ R'#wim = R#wim /\
          R'#sp = R#sp /\ F' = F /\ D' = [] /\ Ms' = Ms). {
  inverts P__.
  (* usr_mode *) {
    false. apply (ModeDeq (R,F)); auto.
    apply IVR.
  }

  (* sup_mode *) {
    inverts H10.
    unfolds in H6.
    inverts H6.
    assert (Cs (cursor_Q (R, F)) = Some (ld (sp+ₐₙ($44)) i3)) as INS. {
    asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)  +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)  +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) ). iauto.
    apply FUNC.
    }
    rewrite H11 in INS.
    clear H11. inverts INS.

    {
    inverts H12; try solve [false].
    inverts H5; try solve [false].
    inverts H6.
    splits;inverts H4;iauto.
    (* trap? no !*){
    inverts H4.
    asserts_rewrite(($ (-4096)) <=ᵢ ($ 44) && ($ 44) <=ᵢ ($ 4095) = true) in H0. {
       unfolds.
       asserts_rewrite (($ (-4096)) <=ᵢ ($ 44) = true). unfolds.
       asserts_rewrite (($ 44) >ᵢ ($ (-4096)) = true). mauto. auto. mauto. 
    }
    asserts_rewrite (word_aligned (R r14) +ᵢ ($ 44) = true) in H0. iauto.
    simpl in H0.
    inverts H0.
    }
    }
    (* annul? no !*){
    inverts H5.
    false.
    apply (AnnulDeq R).
    apply H8. apply IVR.
    }
  }
  }



  assert (R'#pc = R_#pc +ᵢ ($4 ) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)  +ᵢ ($4)  +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) /\ normal_cursor (R',F')) as CSR'. {
    splits. {
      asserts_rewrite (get_R pc R' = get_R npc R). iauto.
      asserts_rewrite (get_R npc R = (get_R pc R) +ᵢ ($ 4)). apply CSR.
      asserts_rewrite (get_R pc R = (get_R pc R_) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)  +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)). apply CSR.
      auto.
    }
    {
      unfolds.
        asserts_rewrite (get_R npc R' = (get_R npc R) +ᵢ ($ 4)). iauto.
        asserts_rewrite (get_R pc R'  = get_R npc R). iauto.
        auto.
    }
  }

  {
  assert (handler_context R') as IVR'. {
    unfolds.
    splits; try unfolds; try unfolds;
    try asserts_rewrite ((get_R cwp R') = (get_R cwp R));
    try asserts_rewrite ((get_R annul R') = (get_R annul R)); 
    try asserts_rewrite ((get_R et R') = (get_R et R));
    try asserts_rewrite ((get_R trap R') = (get_R trap R));
    try asserts_rewrite ((get_R s R') = (get_R s R));
    iauto; apply IVR.
  }

  assert (
   word_aligned_R R'#sp /\ memort_context R'#sp Ms' /\
   (let (Rr,Fr) := right_win 2 (R',F') in word_aligned_R Rr#l1 /\ word_aligned_R Rr#l2) /\ word_aligned_R (get_R r14 R') +ᵢ ($ 44)) as ALIGN'. {
    unfold align_context in ALIGN.
    splits.
    {
      asserts_rewrite ((get_R r14 R') = (get_R r14 R)). iauto. iauto.
    }
    {
      asserts_rewrite (Ms' = Ms). iauto.
      asserts_rewrite ((get_R r14 R') = (get_R r14 R)). iauto. iauto.
    }
    {

      remember (right_win 2 (R', F')) as K.
      destruct K as (Rrr',Frr').
      remember (right_win 2 (R, F)) as K.
      destruct K as (Rrr,Frr).
      asserts_rewrite ((get_R r17 Rrr')  = (get_R r17 Rrr)). {
        apply (Right2_Right2_Same R R' Rrr Rrr' F F' Frr Frr'); iauto.
      }
      asserts_rewrite ((get_R r18 Rrr')  = (get_R r18 Rrr)). {
        apply (Right2_Right2_Same R R' Rrr Rrr' F F' Frr Frr'); iauto.
      }
      iauto.
    }
    asserts_rewrite (get_R r14 R' = get_R r14 R). iauto. iauto.
  }

  assert (single_mask (post_cwp 1 R') (get_R wim R')) as MASK'. {
    asserts_rewrite ((get_R wim R') = (get_R wim R)). iauto.
    unfold post_cwp.
    unfold post_cwp in MASK.
    asserts_rewrite ((get_R cwp R') = (get_R cwp R)). iauto.
    iauto.
  }


  assert (D' = []) as DELAY'. {
    iauto.
  }


  assert (f_context F_restore /\ f_context F_restore_restore /\ f_context F') as CONT'. {
    splits; iauto.
    asserts_rewrite(F' = F). iauto.
    iauto.
  }

  assert (Z__ (Cu, Cs) (Mu, Ms_, (R_, F_),[]) [None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None] 22 (Mu, Ms', (R', F'),D')) as GOAL'. {
    apply (No_Event (Cu,Cs) [None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None] 21 (Mu, Ms_, (R_, F_),[]) (Mu, Ms', (R', F'),D') (Mu, Ms, (R, F),D));
    try rewrite DELAY in *; auto.
  }
  clear H P__ IVR MASK CSR DELAY ALIGN GOAL CONT TMP.
  clear Ms R F D.
  rename Ms' into Ms.
  rename R' into R.
  rename F' into F.
  rename D' into D.
  rename IVR' into IVR.
  rename MASK' into MASK.
  rename CSR' into CSR.
  rename DELAY' into DELAY.
  rename GOAL' into GOAL.
  rename ALIGN' into ALIGN.
  rename CONT' into CONT.













(* step 23 *)

  assert (not_abort Cs Ms (R,F) D) as NA. {
    unfolds.
    exists (R,F) D  (ld (sp+ₐₙ($48)) i4).
    splits.
    - substs. auto.
    - asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)  +ᵢ ($ 4) +ᵢ ($ 4)  +ᵢ ($ 4)  +ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)); iauto. apply FUNC.
    - unfolds. simpl. auto.
      asserts_rewrite(($ (-4096)) <=ᵢ ($ 48) && ($ 48) <=ᵢ ($ 4095) = true). {
        unfolds.
        asserts_rewrite (($ (-4096)) <=ᵢ ($ 48) = true). unfolds.
        asserts_rewrite (($ 48) >ᵢ ($ (-4096)) = true). mauto. auto. mauto. 
      }
      assert (exists v, Ms (R r14) +ᵢ ($ 48) = Some v). {
      assert ( memort_context (get_R r14 R) Ms). iauto.
      unfold memort_context in H.
      destruct H as (v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & v15 & v16 & H).
      exists v13.
      apply H.
      }
      inverts H.
      rewrite H0. auto.
  }

  (* to P__ *)
  assert
  (exists Ms' Q' D', P__ (Cu,Cs) ((Mu,Ms),(R,F),D) ((Mu,Ms'),Q',D')) as H. {
    apply (Exists_P_Sup Cu Cs Mu Ms (R,F) D);
    auto; try apply IVR.
  }
  destruct H as (Ms' & Q' & D' & P__).
  destruct Q' as (R' & F').
  clear NA.

  (* deal with delay *)
  rewrite DELAY in *.

  (* align *)
  assert (word_aligned_R (get_R r14 R)+ᵢ ($48)) as TMP. {
     asserts_rewrite (($ 48) = ($ 44) +ᵢ ($ 4)). {
      clear CSR. int auto.
    }
    rewrite <- Int.add_assoc.
    apply align_plus4. iauto.
  }


  (* small changes in one step *)
  assert (R'#pc = R#npc /\ R'#npc = R#npc +ᵢ ($4) /\
          R'#cwp = R#cwp /\ R'#annul = R#annul /\ R'#et = R#et /\ R'#trap = R#trap /\ R'#s = R#s /\ R'#wim = R#wim /\
          R'#sp = R#sp /\ F' = F /\ D' = [] /\ Ms' = Ms). {
  inverts P__.
  (* usr_mode *) {
    false. apply (ModeDeq (R,F)); auto.
    apply IVR.
  }

  (* sup_mode *) {
    inverts H10.
    unfolds in H6.
    inverts H6.
    assert (Cs (cursor_Q (R, F)) = Some (ld (sp+ₐₙ($48)) i4)) as INS. {
    asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)  +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)  +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) ). iauto.
    apply FUNC.
    }
    rewrite H11 in INS.
    clear H11. inverts INS.

    {
    inverts H12; try solve [false].
    inverts H5; try solve [false].
    inverts H6.
    splits;inverts H4;iauto.
    (* trap? no !*){
    inverts H4.
    asserts_rewrite(($ (-4096)) <=ᵢ ($ 48) && ($ 48) <=ᵢ ($ 4095) = true) in H0. {
       unfolds.
       asserts_rewrite (($ (-4096)) <=ᵢ ($ 48) = true). unfolds.
       asserts_rewrite (($ 48) >ᵢ ($ (-4096)) = true). mauto. auto. mauto. 
    }
    asserts_rewrite (word_aligned (R r14) +ᵢ ($ 48) = true) in H0. iauto.
    simpl in H0.
    inverts H0.
    }
    }
    (* annul? no !*){
    inverts H5.
    false.
    apply (AnnulDeq R).
    apply H8. apply IVR.
    }
  }
  }



  assert (R'#pc = R_#pc +ᵢ ($4 ) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)  +ᵢ ($4) +ᵢ ($4)  +ᵢ ($4)  +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) /\ normal_cursor (R',F')) as CSR'. {
    splits. {
      asserts_rewrite (get_R pc R' = get_R npc R). iauto.
      asserts_rewrite (get_R npc R = (get_R pc R) +ᵢ ($ 4)). apply CSR.
      asserts_rewrite (get_R pc R = (get_R pc R_) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)  +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)). apply CSR.
      auto.
    }
    {
      unfolds.
        asserts_rewrite (get_R npc R' = (get_R npc R) +ᵢ ($ 4)). iauto.
        asserts_rewrite (get_R pc R'  = get_R npc R). iauto.
        auto.
    }
  }

  {
  assert (handler_context R') as IVR'. {
    unfolds.
    splits; try unfolds; try unfolds;
    try asserts_rewrite ((get_R cwp R') = (get_R cwp R));
    try asserts_rewrite ((get_R annul R') = (get_R annul R)); 
    try asserts_rewrite ((get_R et R') = (get_R et R));
    try asserts_rewrite ((get_R trap R') = (get_R trap R));
    try asserts_rewrite ((get_R s R') = (get_R s R));
    iauto; apply IVR.
  }

  assert (
   word_aligned_R R'#sp /\ memort_context R'#sp Ms' /\
   (let (Rr,Fr) := right_win 2 (R',F') in word_aligned_R Rr#l1 /\ word_aligned_R Rr#l2) /\ word_aligned_R (get_R r14 R') +ᵢ ($ 48)) as ALIGN'. {
    unfold align_context in ALIGN.
    splits.
    {
      asserts_rewrite ((get_R r14 R') = (get_R r14 R)). iauto. iauto.
    }
    {
      asserts_rewrite (Ms' = Ms). iauto.
      asserts_rewrite ((get_R r14 R') = (get_R r14 R)). iauto. iauto.
    }
    {

      remember (right_win 2 (R', F')) as K.
      destruct K as (Rrr',Frr').
      remember (right_win 2 (R, F)) as K.
      destruct K as (Rrr,Frr).
      asserts_rewrite ((get_R r17 Rrr')  = (get_R r17 Rrr)). {
        apply (Right2_Right2_Same R R' Rrr Rrr' F F' Frr Frr'); iauto.
      }
      asserts_rewrite ((get_R r18 Rrr')  = (get_R r18 Rrr)). {
        apply (Right2_Right2_Same R R' Rrr Rrr' F F' Frr Frr'); iauto.
      }
      iauto.
    }
    asserts_rewrite (get_R r14 R' = get_R r14 R). iauto. iauto.
  }

  assert (single_mask (post_cwp 1 R') (get_R wim R')) as MASK'. {
    asserts_rewrite ((get_R wim R') = (get_R wim R)). iauto.
    unfold post_cwp.
    unfold post_cwp in MASK.
    asserts_rewrite ((get_R cwp R') = (get_R cwp R)). iauto.
    iauto.
  }


  assert (D' = []) as DELAY'. {
    iauto.
  }


  assert (f_context F_restore /\ f_context F_restore_restore /\ f_context F') as CONT'. {
    splits; iauto.
    asserts_rewrite(F' = F). iauto.
    iauto.
  }

  assert (Z__ (Cu, Cs) (Mu, Ms_, (R_, F_),[]) [None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None] 23 (Mu, Ms', (R', F'),D')) as GOAL'. {
    apply (No_Event (Cu,Cs) [None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None] 22 (Mu, Ms_, (R_, F_),[]) (Mu, Ms', (R', F'),D') (Mu, Ms, (R, F),D));
    try rewrite DELAY in *; auto.
  }
  clear H P__ IVR MASK CSR DELAY ALIGN GOAL CONT TMP.
  clear Ms R F D.
  rename Ms' into Ms.
  rename R' into R.
  rename F' into F.
  rename D' into D.
  rename IVR' into IVR.
  rename MASK' into MASK.
  rename CSR' into CSR.
  rename DELAY' into DELAY.
  rename GOAL' into GOAL.
  rename ALIGN' into ALIGN.
  rename CONT' into CONT.












(* step 24 *)

  assert (not_abort Cs Ms (R,F) D) as NA. {
    unfolds.
    exists (R,F) D  (ld (sp+ₐₙ($52)) i5).
    splits.
    - substs. auto.
    - asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)  +ᵢ ($ 4) +ᵢ ($ 4)  +ᵢ ($ 4)  +ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)); iauto. apply FUNC.
    - unfolds. simpl. auto.
      asserts_rewrite(($ (-4096)) <=ᵢ ($ 52) && ($ 52) <=ᵢ ($ 4095) = true). {
        unfolds.
        asserts_rewrite (($ (-4096)) <=ᵢ ($ 52) = true). unfolds.
        asserts_rewrite (($ 52) >ᵢ ($ (-4096)) = true). mauto. auto. mauto. 
      }
      assert (exists v, Ms (R r14) +ᵢ ($ 52) = Some v). {
      assert ( memort_context (get_R r14 R) Ms). iauto.
      unfold memort_context in H.
      destruct H as (v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & v15 & v16 & H).
      exists v14.
      apply H.
      }
      inverts H.
      rewrite H0. auto.
  }

  (* to P__ *)
  assert
  (exists Ms' Q' D', P__ (Cu,Cs) ((Mu,Ms),(R,F),D) ((Mu,Ms'),Q',D')) as H. {
    apply (Exists_P_Sup Cu Cs Mu Ms (R,F) D);
    auto; try apply IVR.
  }
  destruct H as (Ms' & Q' & D' & P__).
  destruct Q' as (R' & F').
  clear NA.

  (* deal with delay *)
  rewrite DELAY in *.

  (* align *)
  assert (word_aligned_R (get_R r14 R)+ᵢ ($52)) as TMP. {
     asserts_rewrite (($ 52) = ($ 48) +ᵢ ($ 4)). {
      clear CSR. int auto.
    }
    rewrite <- Int.add_assoc.
    apply align_plus4. iauto.
  }


  (* small changes in one step *)
  assert (R'#pc = R#npc /\ R'#npc = R#npc +ᵢ ($4) /\
          R'#cwp = R#cwp /\ R'#annul = R#annul /\ R'#et = R#et /\ R'#trap = R#trap /\ R'#s = R#s /\ R'#wim = R#wim /\
          R'#sp = R#sp /\ F' = F /\ D' = [] /\ Ms' = Ms). {
  inverts P__.
  (* usr_mode *) {
    false. apply (ModeDeq (R,F)); auto.
    apply IVR.
  }

  (* sup_mode *) {
    inverts H10.
    unfolds in H6.
    inverts H6.
    assert (Cs (cursor_Q (R, F)) = Some (ld (sp+ₐₙ($52)) i5)) as INS. {
    asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)  +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)  +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) ). iauto.
    apply FUNC.
    }
    rewrite H11 in INS.
    clear H11. inverts INS.

    {
    inverts H12; try solve [false].
    inverts H5; try solve [false].
    inverts H6.
    splits;inverts H4;iauto.
    (* trap? no !*){
    inverts H4.
    asserts_rewrite(($ (-4096)) <=ᵢ ($ 52) && ($ 52) <=ᵢ ($ 4095) = true) in H0. {
       unfolds.
       asserts_rewrite (($ (-4096)) <=ᵢ ($ 52) = true). unfolds.
       asserts_rewrite (($ 52) >ᵢ ($ (-4096)) = true). mauto. auto. mauto. 
    }
    asserts_rewrite (word_aligned (R r14) +ᵢ ($ 52) = true) in H0. iauto.
    simpl in H0.
    inverts H0.
    }
    }
    (* annul? no !*){
    inverts H5.
    false.
    apply (AnnulDeq R).
    apply H8. apply IVR.
    }
  }
  }



  assert (R'#pc = R_#pc +ᵢ ($4 ) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)  +ᵢ ($4) +ᵢ ($4)  +ᵢ ($4)  +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) /\ normal_cursor (R',F')) as CSR'. {
    splits. {
      asserts_rewrite (get_R pc R' = get_R npc R). iauto.
      asserts_rewrite (get_R npc R = (get_R pc R) +ᵢ ($ 4)). apply CSR.
      asserts_rewrite (get_R pc R = (get_R pc R_) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)  +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)). apply CSR.
      auto.
    }
    {
      unfolds.
        asserts_rewrite (get_R npc R' = (get_R npc R) +ᵢ ($ 4)). iauto.
        asserts_rewrite (get_R pc R'  = get_R npc R). iauto.
        auto.
    }
  }

  {
  assert (handler_context R') as IVR'. {
    unfolds.
    splits; try unfolds; try unfolds;
    try asserts_rewrite ((get_R cwp R') = (get_R cwp R));
    try asserts_rewrite ((get_R annul R') = (get_R annul R)); 
    try asserts_rewrite ((get_R et R') = (get_R et R));
    try asserts_rewrite ((get_R trap R') = (get_R trap R));
    try asserts_rewrite ((get_R s R') = (get_R s R));
    iauto; apply IVR.
  }

  assert (
   word_aligned_R R'#sp /\ memort_context R'#sp Ms' /\
   (let (Rr,Fr) := right_win 2 (R',F') in word_aligned_R Rr#l1 /\ word_aligned_R Rr#l2) /\ word_aligned_R (get_R r14 R') +ᵢ ($ 52)) as ALIGN'. {
    unfold align_context in ALIGN.
    splits.
    {
      asserts_rewrite ((get_R r14 R') = (get_R r14 R)). iauto. iauto.
    }
    {
      asserts_rewrite (Ms' = Ms). iauto.
      asserts_rewrite ((get_R r14 R') = (get_R r14 R)). iauto. iauto.
    }
    {

      remember (right_win 2 (R', F')) as K.
      destruct K as (Rrr',Frr').
      remember (right_win 2 (R, F)) as K.
      destruct K as (Rrr,Frr).
      asserts_rewrite ((get_R r17 Rrr')  = (get_R r17 Rrr)). {
        apply (Right2_Right2_Same R R' Rrr Rrr' F F' Frr Frr'); iauto.
      }
      asserts_rewrite ((get_R r18 Rrr')  = (get_R r18 Rrr)). {
        apply (Right2_Right2_Same R R' Rrr Rrr' F F' Frr Frr'); iauto.
      }
      iauto.
    }
    asserts_rewrite (get_R r14 R' = get_R r14 R). iauto. iauto.
  }

  assert (single_mask (post_cwp 1 R') (get_R wim R')) as MASK'. {
    asserts_rewrite ((get_R wim R') = (get_R wim R)). iauto.
    unfold post_cwp.
    unfold post_cwp in MASK.
    asserts_rewrite ((get_R cwp R') = (get_R cwp R)). iauto.
    iauto.
  }


  assert (D' = []) as DELAY'. {
    iauto.
  }


  assert (f_context F_restore /\ f_context F_restore_restore /\ f_context F') as CONT'. {
    splits; iauto.
    asserts_rewrite(F' = F). iauto.
    iauto.
  }

  assert (Z__ (Cu, Cs) (Mu, Ms_, (R_, F_),[]) [None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None] 24 (Mu, Ms', (R', F'),D')) as GOAL'. {
    apply (No_Event (Cu,Cs) [None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None] 23 (Mu, Ms_, (R_, F_),[]) (Mu, Ms', (R', F'),D') (Mu, Ms, (R, F),D));
    try rewrite DELAY in *; auto.
  }
  clear H P__ IVR MASK CSR DELAY ALIGN GOAL CONT TMP.
  clear Ms R F D.
  rename Ms' into Ms.
  rename R' into R.
  rename F' into F.
  rename D' into D.
  rename IVR' into IVR.
  rename MASK' into MASK.
  rename CSR' into CSR.
  rename DELAY' into DELAY.
  rename GOAL' into GOAL.
  rename ALIGN' into ALIGN.
  rename CONT' into CONT.






(* step 25 *)

  assert (not_abort Cs Ms (R,F) D) as NA. {
    unfolds.
    exists (R,F) D  (ld (sp+ₐₙ($56)) i6).
    splits.
    - substs. auto.
    - asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)  +ᵢ ($ 4) +ᵢ ($ 4)  +ᵢ ($ 4)  +ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)); iauto. apply FUNC.
    - unfolds. simpl. auto.
      asserts_rewrite(($ (-4096)) <=ᵢ ($ 56) && ($ 56) <=ᵢ ($ 4095) = true). {
        unfolds.
        asserts_rewrite (($ (-4096)) <=ᵢ ($ 56) = true). unfolds.
        asserts_rewrite (($ 56) >ᵢ ($ (-4096)) = true). mauto. auto. mauto. 
      }
      assert (exists v, Ms (R r14) +ᵢ ($ 56) = Some v). {
      assert ( memort_context (get_R r14 R) Ms). iauto.
      unfold memort_context in H.
      destruct H as (v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & v15 & v16 & H).
      exists v15.
      apply H.
      }
      inverts H.
      rewrite H0. auto.
  }

  (* to P__ *)
  assert
  (exists Ms' Q' D', P__ (Cu,Cs) ((Mu,Ms),(R,F),D) ((Mu,Ms'),Q',D')) as H. {
    apply (Exists_P_Sup Cu Cs Mu Ms (R,F) D);
    auto; try apply IVR.
  }
  destruct H as (Ms' & Q' & D' & P__).
  destruct Q' as (R' & F').
  clear NA.

  (* deal with delay *)
  rewrite DELAY in *.

  (* align *)
  assert (word_aligned_R (get_R r14 R)+ᵢ ($56)) as TMP. {
     asserts_rewrite (($ 56) = ($ 52) +ᵢ ($ 4)). {
      clear CSR. int auto.
    }
    rewrite <- Int.add_assoc.
    apply align_plus4. iauto.
  }


  (* small changes in one step *)
  assert (R'#pc = R#npc /\ R'#npc = R#npc +ᵢ ($4) /\
          R'#cwp = R#cwp /\ R'#annul = R#annul /\ R'#et = R#et /\ R'#trap = R#trap /\ R'#s = R#s /\ R'#wim = R#wim /\
          R'#sp = R#sp /\ F' = F /\ D' = [] /\ Ms' = Ms). {
  inverts P__.
  (* usr_mode *) {
    false. apply (ModeDeq (R,F)); auto.
    apply IVR.
  }

  (* sup_mode *) {
    inverts H10.
    unfolds in H6.
    inverts H6.
    assert (Cs (cursor_Q (R, F)) = Some (ld (sp+ₐₙ($56)) i6)) as INS. {
    asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)  +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)  +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) ). iauto.
    apply FUNC.
    }
    rewrite H11 in INS.
    clear H11. inverts INS.

    {
    inverts H12; try solve [false].
    inverts H5; try solve [false].
    inverts H6.
    splits;inverts H4;iauto.
    (* trap? no !*){
    inverts H4.
    asserts_rewrite(($ (-4096)) <=ᵢ ($ 56) && ($ 56) <=ᵢ ($ 4095) = true) in H0. {
       unfolds.
       asserts_rewrite (($ (-4096)) <=ᵢ ($ 56) = true). unfolds.
       asserts_rewrite (($ 56) >ᵢ ($ (-4096)) = true). mauto. auto. mauto. 
    }
    asserts_rewrite (word_aligned (R r14) +ᵢ ($ 56) = true) in H0. iauto.
    simpl in H0.
    inverts H0.
    }
    }
    (* annul? no !*){
    inverts H5.
    false.
    apply (AnnulDeq R).
    apply H8. apply IVR.
    }
  }
  }



  assert (R'#pc = R_#pc +ᵢ ($4 ) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)  +ᵢ ($4) +ᵢ ($4)  +ᵢ ($4)  +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) /\ normal_cursor (R',F')) as CSR'. {
    splits. {
      asserts_rewrite (get_R pc R' = get_R npc R). iauto.
      asserts_rewrite (get_R npc R = (get_R pc R) +ᵢ ($ 4)). apply CSR.
      asserts_rewrite (get_R pc R = (get_R pc R_) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)  +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)). apply CSR.
      auto.
    }
    {
      unfolds.
        asserts_rewrite (get_R npc R' = (get_R npc R) +ᵢ ($ 4)). iauto.
        asserts_rewrite (get_R pc R'  = get_R npc R). iauto.
        auto.
    }
  }

  {
  assert (handler_context R') as IVR'. {
    unfolds.
    splits; try unfolds; try unfolds;
    try asserts_rewrite ((get_R cwp R') = (get_R cwp R));
    try asserts_rewrite ((get_R annul R') = (get_R annul R)); 
    try asserts_rewrite ((get_R et R') = (get_R et R));
    try asserts_rewrite ((get_R trap R') = (get_R trap R));
    try asserts_rewrite ((get_R s R') = (get_R s R));
    iauto; apply IVR.
  }

  assert (
   word_aligned_R R'#sp /\ memort_context R'#sp Ms' /\
   (let (Rr,Fr) := right_win 2 (R',F') in word_aligned_R Rr#l1 /\ word_aligned_R Rr#l2) /\ word_aligned_R (get_R r14 R') +ᵢ ($ 56)) as ALIGN'. {
    unfold align_context in ALIGN.
    splits.
    {
      asserts_rewrite ((get_R r14 R') = (get_R r14 R)). iauto. iauto.
    }
    {
      asserts_rewrite (Ms' = Ms). iauto.
      asserts_rewrite ((get_R r14 R') = (get_R r14 R)). iauto. iauto.
    }
    {

      remember (right_win 2 (R', F')) as K.
      destruct K as (Rrr',Frr').
      remember (right_win 2 (R, F)) as K.
      destruct K as (Rrr,Frr).
      asserts_rewrite ((get_R r17 Rrr')  = (get_R r17 Rrr)). {
        apply (Right2_Right2_Same R R' Rrr Rrr' F F' Frr Frr'); iauto.
      }
      asserts_rewrite ((get_R r18 Rrr')  = (get_R r18 Rrr)). {
        apply (Right2_Right2_Same R R' Rrr Rrr' F F' Frr Frr'); iauto.
      }
      iauto.
    }
    asserts_rewrite (get_R r14 R' = get_R r14 R). iauto. iauto.
  }

  assert (single_mask (post_cwp 1 R') (get_R wim R')) as MASK'. {
    asserts_rewrite ((get_R wim R') = (get_R wim R)). iauto.
    unfold post_cwp.
    unfold post_cwp in MASK.
    asserts_rewrite ((get_R cwp R') = (get_R cwp R)). iauto.
    iauto.
  }


  assert (D' = []) as DELAY'. {
    iauto.
  }


  assert (f_context F_restore /\ f_context F_restore_restore /\ f_context F') as CONT'. {
    splits; iauto.
    asserts_rewrite(F' = F). iauto.
    iauto.
  }

  assert (Z__ (Cu, Cs) (Mu, Ms_, (R_, F_),[]) [None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None] 25 (Mu, Ms', (R', F'),D')) as GOAL'. {
    apply (No_Event (Cu,Cs) [None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None] 24 (Mu, Ms_, (R_, F_),[]) (Mu, Ms', (R', F'),D') (Mu, Ms, (R, F),D));
    try rewrite DELAY in *; auto.
  }
  clear H P__ IVR MASK CSR DELAY ALIGN GOAL CONT TMP.
  clear Ms R F D.
  rename Ms' into Ms.
  rename R' into R.
  rename F' into F.
  rename D' into D.
  rename IVR' into IVR.
  rename MASK' into MASK.
  rename CSR' into CSR.
  rename DELAY' into DELAY.
  rename GOAL' into GOAL.
  rename ALIGN' into ALIGN.
  rename CONT' into CONT.








(* step 26 *)

  assert (not_abort Cs Ms (R,F) D) as NA. {
    unfolds.
    exists (R,F) D  (ld (sp+ₐₙ($60)) i7).
    splits.
    - substs. auto.
    - asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)  +ᵢ ($ 4) +ᵢ ($ 4)  +ᵢ ($ 4)  +ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)); iauto. apply FUNC.
    - unfolds. simpl. auto.
      asserts_rewrite(($ (-4096)) <=ᵢ ($ 60) && ($ 60) <=ᵢ ($ 4095) = true). {
        unfolds.
        asserts_rewrite (($ (-4096)) <=ᵢ ($ 60) = true). unfolds.
        asserts_rewrite (($ 60) >ᵢ ($ (-4096)) = true). mauto. auto. mauto. 
      }
      assert (exists v, Ms (R r14) +ᵢ ($ 60) = Some v). {
      assert ( memort_context (get_R r14 R) Ms). iauto.
      unfold memort_context in H.
      destruct H as (v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & v15 & v16 & H).
      exists v16.
      apply H.
      }
      inverts H.
      rewrite H0. auto.
  }

  (* to P__ *)
  assert
  (exists Ms' Q' D', P__ (Cu,Cs) ((Mu,Ms),(R,F),D) ((Mu,Ms'),Q',D')) as H. {
    apply (Exists_P_Sup Cu Cs Mu Ms (R,F) D);
    auto; try apply IVR.
  }
  destruct H as (Ms' & Q' & D' & P__).
  destruct Q' as (R' & F').
  clear NA.

  (* deal with delay *)
  rewrite DELAY in *.

  (* align *)
  assert (word_aligned_R (get_R r14 R)+ᵢ ($60)) as TMP. {
     asserts_rewrite (($ 60) = ($ 56) +ᵢ ($ 4)). {
      clear CSR. int auto.
    }
    rewrite <- Int.add_assoc.
    apply align_plus4. iauto.
  }


  (* small changes in one step *)
  assert (R'#pc = R#npc /\ R'#npc = R#npc +ᵢ ($4) /\
          R'#cwp = R#cwp /\ R'#annul = R#annul /\ R'#et = R#et /\ R'#trap = R#trap /\ R'#s = R#s /\ R'#wim = R#wim /\
          R'#sp = R#sp /\ F' = F /\ D' = [] /\ Ms' = Ms). {
  inverts P__.
  (* usr_mode *) {
    false. apply (ModeDeq (R,F)); auto.
    apply IVR.
  }

  (* sup_mode *) {
    inverts H10.
    unfolds in H6.
    inverts H6.
    assert (Cs (cursor_Q (R, F)) = Some (ld (sp+ₐₙ($60)) i7)) as INS. {
    asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)  +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)  +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) ). iauto.
    apply FUNC.
    }
    rewrite H11 in INS.
    clear H11. inverts INS.

    {
    inverts H12; try solve [false].
    inverts H5; try solve [false].
    inverts H6.
    splits;inverts H4;iauto.
    (* trap? no !*){
    inverts H4.
    asserts_rewrite(($ (-4096)) <=ᵢ ($ 60) && ($ 60) <=ᵢ ($ 4095) = true) in H0. {
       unfolds.
       asserts_rewrite (($ (-4096)) <=ᵢ ($ 60) = true). unfolds.
       asserts_rewrite (($ 60) >ᵢ ($ (-4096)) = true). mauto. auto. mauto. 
    }
    asserts_rewrite (word_aligned (R r14) +ᵢ ($ 60) = true) in H0. iauto.
    simpl in H0.
    inverts H0.
    }
    }
    (* annul? no !*){
    inverts H5.
    false.
    apply (AnnulDeq R).
    apply H8. apply IVR.
    }
  }
  }



  assert (R'#pc = R_#pc +ᵢ ($4 ) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)  +ᵢ ($4) +ᵢ ($4)  +ᵢ ($4)  +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) /\ normal_cursor (R',F')) as CSR'. {
    splits. {
      asserts_rewrite (get_R pc R' = get_R npc R). iauto.
      asserts_rewrite (get_R npc R = (get_R pc R) +ᵢ ($ 4)). apply CSR.
      asserts_rewrite (get_R pc R = (get_R pc R_) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)  +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)  +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)). apply CSR.
      auto.
    }
    {
      unfolds.
        asserts_rewrite (get_R npc R' = (get_R npc R) +ᵢ ($ 4)). iauto.
        asserts_rewrite (get_R pc R'  = get_R npc R). iauto.
        auto.
    }
  }

  {
  assert (handler_context R') as IVR'. {
    unfolds.
    splits; try unfolds; try unfolds;
    try asserts_rewrite ((get_R cwp R') = (get_R cwp R));
    try asserts_rewrite ((get_R annul R') = (get_R annul R)); 
    try asserts_rewrite ((get_R et R') = (get_R et R));
    try asserts_rewrite ((get_R trap R') = (get_R trap R));
    try asserts_rewrite ((get_R s R') = (get_R s R));
    iauto; apply IVR.
  }

  assert (
   word_aligned_R R'#sp /\ memort_context R'#sp Ms' /\
   (let (Rr,Fr) := right_win 2 (R',F') in word_aligned_R Rr#l1 /\ word_aligned_R Rr#l2) /\ word_aligned_R (get_R r14 R') +ᵢ ($ 60)) as ALIGN'. {
    unfold align_context in ALIGN.
    splits.
    {
      asserts_rewrite ((get_R r14 R') = (get_R r14 R)). iauto. iauto.
    }
    {
      asserts_rewrite (Ms' = Ms). iauto.
      asserts_rewrite ((get_R r14 R') = (get_R r14 R)). iauto. iauto.
    }
    {

      remember (right_win 2 (R', F')) as K.
      destruct K as (Rrr',Frr').
      remember (right_win 2 (R, F)) as K.
      destruct K as (Rrr,Frr).
      asserts_rewrite ((get_R r17 Rrr')  = (get_R r17 Rrr)). {
        apply (Right2_Right2_Same R R' Rrr Rrr' F F' Frr Frr'); iauto.
      }
      asserts_rewrite ((get_R r18 Rrr')  = (get_R r18 Rrr)). {
        apply (Right2_Right2_Same R R' Rrr Rrr' F F' Frr Frr'); iauto.
      }
      iauto.
    }
    asserts_rewrite (get_R r14 R' = get_R r14 R). iauto. iauto.
  }

  assert (single_mask (post_cwp 1 R') (get_R wim R')) as MASK'. {
    asserts_rewrite ((get_R wim R') = (get_R wim R)). iauto.
    unfold post_cwp.
    unfold post_cwp in MASK.
    asserts_rewrite ((get_R cwp R') = (get_R cwp R)). iauto.
    iauto.
  }


  assert (D' = []) as DELAY'. {
    iauto.
  }


  assert (f_context F_restore /\ f_context F_restore_restore /\ f_context F') as CONT'. {
    splits; iauto.
    asserts_rewrite(F' = F). iauto.
    iauto.
  }

  assert (Z__ (Cu, Cs) (Mu, Ms_, (R_, F_),[]) [None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None] 26 (Mu, Ms', (R', F'),D')) as GOAL'. {
    apply (No_Event (Cu,Cs) [None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None] 25 (Mu, Ms_, (R_, F_),[]) (Mu, Ms', (R', F'),D') (Mu, Ms, (R, F),D));
    try rewrite DELAY in *; auto.
  }
  clear H P__ IVR MASK CSR DELAY ALIGN GOAL CONT TMP.
  clear Ms R F D.
  rename Ms' into Ms.
  rename R' into R.
  rename F' into F.
  rename D' into D.
  rename IVR' into IVR.
  rename MASK' into MASK.
  rename CSR' into CSR.
  rename DELAY' into DELAY.
  rename GOAL' into GOAL.
  rename ALIGN' into ALIGN.
  rename CONT' into CONT.




(* step 27 *)

   assert (not_abort Cs Ms (R,F) D) as NA. {
    unfolds.
    exists (R,F) D  (save g0 g0 ᵣ g0).
    splits.
    - substs. auto.
    - asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)); iauto. apply FUNC.
    - unfolds. auto.
  }

  (* to P__ *)
  assert
  (exists Ms' Q' D', P__ (Cu,Cs) ((Mu,Ms),(R,F),D) ((Mu,Ms'),Q',D')) as H. {
    apply (Exists_P_Sup Cu Cs Mu Ms (R,F) D);
    auto; try apply IVR.
  }
  destruct H as (Ms' & Q' & D' & P__).
  destruct Q' as (R' & F').
  clear NA.

  (* deal with delay *)
  rewrite DELAY in *.

(* small changes in one step *)
  assert (R'#pc = R#npc /\ R'#npc = R#npc +ᵢ ($4) /\
         R'#annul = R#annul /\ R'#et = R#et /\ R'#trap = R#trap /\ R'#s = R#s /\ R'#wim = R#wim /\
           R'#cwp = (pre_cwp 1 R) /\ D' = D /\ (let (R_Save,F_Save) := right_win 1 (R,F) in R'#l1 = R_Save#l1 /\ R'#l2 = R_Save#l2 /\ R'#r14 = R_Save#r14 /\ F' = F_Save) /\ Ms' = Ms). {
  inverts P__.
  (* usr_mode *) {
    false. apply (ModeDeq (R,F)); auto.
    apply IVR.
  }
  (* sup_mode *) {
    inverts H10.
    unfolds in H6.
    inverts H6.
    assert (Cs (cursor_Q (R, F)) = Some (save g0 g0 ᵣ g0)) as INS. {
    asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)); iauto. apply FUNC.
    }
    rewrite H11 in INS.
    clear H11. inverts INS.

    {
    inverts H12; try solve [false].
    inverts H5; try solve [false].
    inverts H6.
    unfold dec_win in *.
    destruct (win_masked (pre_cwp 1 R) R).
    simpl in H13. try false.
    unfold negb in H13.
    remember (right_win 1 (R, F)).
    destruct r.
    inverts H13.
    rename Heqr into RWIN.
    assert (some_reg_eq R R'0). {
      apply (Hold_Sth_RightWin R R'0 F F' 1); iauto.
    }
    unfolds in H. simpl in H.
    splits.
    simpl. asserts_rewrite (R npc = R'0 npc). iauto. auto.
    simpl. asserts_rewrite (R npc = R'0 npc). iauto. auto.
    simpl. asserts_rewrite (R annul = R'0 annul). iauto. auto.
    simpl. asserts_rewrite (R et = R'0 et). iauto. auto.
    simpl. asserts_rewrite (R trap = R'0 trap). iauto. auto.
    simpl. asserts_rewrite (R s = R'0 s). iauto. auto.
    simpl. asserts_rewrite (R Rwim = R'0 Rwim). iauto. auto.
    splits.
    simpl. asserts_rewrite (pre_cwp 1 R = R'0 cwp). {
      symmetry. apply (right_cwp R R'0 F F'); iauto.
    } 
    iauto.
    iauto.
    asserts_rewrite (get_R r17 (next R'0 # r0 <- ((get_R r0 R) +ᵢ a)) = get_R r17 R'0). iauto. auto. auto.
    (* trap? no !*){
    inverts H4.
    asserts_rewrite (win_masked (pre_cwp 1 R) R = false) in H0. {
      apply (mask_cwp_pre1 R); iauto. apply IVR.
    }
    simpl in H0.
    inverts H0.
    }
    }
    (* annul? no !*){
    inverts H5.
    false.
    apply (AnnulDeq R).
    apply H8. apply IVR.
    }
  }
  }

  assert (R'#pc = R_#pc +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($4) +ᵢ ($4) +ᵢ ($4)+ᵢ ($4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)  +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) /\ normal_cursor (R',F')) as CSR'. {
    splits. {
      asserts_rewrite (get_R pc R' = get_R npc R). iauto.
      asserts_rewrite (get_R npc R = (get_R pc R) +ᵢ ($ 4)). apply CSR.
      asserts_rewrite (get_R pc R = (get_R pc R_) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)+ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)). apply CSR.
      auto.
    }
    {
      unfolds.
        asserts_rewrite (get_R npc R' = (get_R npc R) +ᵢ ($ 4)). iauto.
        asserts_rewrite (get_R pc R'  = get_R npc R). iauto.
        auto.
    }
  }

  {
  assert (handler_context R') as IVR'. {
    unfolds.
    splits; try unfolds; try unfolds;
    try asserts_rewrite ((get_R annul R') = (get_R annul R)); 
    try asserts_rewrite ((get_R et R') = (get_R et R));
    try asserts_rewrite ((get_R trap R') = (get_R trap R));
    try asserts_rewrite ((get_R s R') = (get_R s R));
    iauto; try apply IVR.
    unfolds in IVR.
    asserts_rewrite(Int.unsigned Asm.N - 1 = 7). {
      unfold Asm.N. mauto.
    }
    asserts_rewrite((get_R cwp R') = pre_cwp 1 R). iauto.
    apply (cwp_cycle_pre R). apply IVR.
  }

  assert ((let (Rr,Fr) := right_win 1 (R',F') in word_aligned_R Rr#l1 /\ word_aligned_R Rr#l2) ) as ALIGN'. {
    {
      remember (right_win 1 (R', F')) as K.
      destruct K as (Rr',Fr').
      remember (right_win 1 (R, F)) as K.
      destruct K as (Rr,Fr).
      remember (right_win 2 (R, F)) as K.
      destruct K as (Rrr,Frr).
      asserts_rewrite ((get_R r17 Rr')  = (get_R r17 Rrr)). {
      apply (Right_Right_is_Right2 R R' Rr Rr' Rrr F F' Fr Fr' Frr); iauto.
      }
      asserts_rewrite ((get_R r18 Rr')  = (get_R r18 Rrr)). {
      apply (Right_Right_is_Right2 R R' Rr Rr' Rrr F F' Fr Fr' Frr); iauto.
      }
      splits;
      iauto.
    }  
  }


  assert (single_mask2 R'#cwp (get_R wim R')) as MASK'. {
    asserts_rewrite ((get_R wim R') = (get_R wim R)). iauto.
    apply (Post1_add_1_is_2 R R'); iauto.
  }

  assert (D' = []) as DELAY'. {
    asserts_rewrite (D' = D). iauto. iauto.
  }

  assert (f_context F') as CONT'. {
    remember (right_win 1 (R, F)) as K.
      destruct K as (Rr,Fr).
    asserts_rewrite(F' = Fr). iauto.
    apply (hold_context_right R Rr F Fr); iauto. 
  }

  assert (Z__ (Cu, Cs) (Mu, Ms_, (R_, F_),[]) [None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None] 27 (Mu, Ms', (R', F'),D')) as GOAL'. {
    apply (No_Event (Cu,Cs) [None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None] 26 (Mu, Ms_, (R_, F_),[]) (Mu, Ms', (R', F'),D') (Mu, Ms, (R, F),D));
    try rewrite DELAY in *; auto.
  }
  clear H P__ IVR MASK CSR DELAY ALIGN GOAL CONT.
  clear Ms R F D.
  rename Ms' into Ms.
  rename R' into R.
  rename F' into F.
  rename D' into D.
  rename IVR' into IVR.
  rename MASK' into MASK.
  rename CSR' into CSR.
  rename DELAY' into DELAY.
  rename GOAL' into GOAL.
  rename ALIGN' into ALIGN.
  rename CONT' into CONT.















(* step 28 *)

   assert (not_abort Cs Ms (R,F) D) as NA. {
    unfolds.
    exists (R,F) D  (save g0 g0 ᵣ g0).
    splits.
    - substs. auto.
    - asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)); iauto. apply FUNC.
    - unfolds. auto.
  }

  (* to P__ *)
  assert
  (exists Ms' Q' D', P__ (Cu,Cs) ((Mu,Ms),(R,F),D) ((Mu,Ms'),Q',D')) as H. {
    apply (Exists_P_Sup Cu Cs Mu Ms (R,F) D);
    auto; try apply IVR.
  }
  destruct H as (Ms' & Q' & D' & P__).
  destruct Q' as (R' & F').
  clear NA.

  (* deal with delay *)
  rewrite DELAY in *.

(* small changes in one step *)
  assert (R'#pc = R#npc /\ R'#npc = R#npc +ᵢ ($4) /\
         R'#annul = R#annul /\ R'#et = R#et /\ R'#trap = R#trap /\ R'#s = R#s /\ R'#wim = R#wim /\
           R'#cwp = (pre_cwp 1 R) /\ D' = D /\ (let (R_Save,F_Save) := right_win 1 (R,F) in R'#l1 = R_Save#l1 /\ R'#l2 = R_Save#l2 /\ R'#r14 = R_Save#r14 /\ F' = F_Save) /\ Ms' = Ms). {
  inverts P__.
  (* usr_mode *) {
    false. apply (ModeDeq (R,F)); auto.
    apply IVR.
  }
  (* sup_mode *) {
    inverts H10.
    unfolds in H6.
    inverts H6.
    assert (Cs (cursor_Q (R, F)) = Some (save g0 g0 ᵣ g0)) as INS. {
    asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)); iauto. apply FUNC.
    }
    rewrite H11 in INS.
    clear H11. inverts INS.

    {
    inverts H12; try solve [false].
    inverts H5; try solve [false].
    inverts H6.
    unfold dec_win in *.
    destruct (win_masked (pre_cwp 1 R) R).
    simpl in H13. try false.
    unfold negb in H13.
    remember (right_win 1 (R, F)).
    destruct r.
    inverts H13.
    rename Heqr into RWIN.
    assert (some_reg_eq R R'0). {
      apply (Hold_Sth_RightWin R R'0 F F' 1); iauto.
    }
    unfolds in H. simpl in H.
    splits.
    simpl. asserts_rewrite (R npc = R'0 npc). iauto. auto.
    simpl. asserts_rewrite (R npc = R'0 npc). iauto. auto.
    simpl. asserts_rewrite (R annul = R'0 annul). iauto. auto.
    simpl. asserts_rewrite (R et = R'0 et). iauto. auto.
    simpl. asserts_rewrite (R trap = R'0 trap). iauto. auto.
    simpl. asserts_rewrite (R s = R'0 s). iauto. auto.
    simpl. asserts_rewrite (R Rwim = R'0 Rwim). iauto. auto.
    splits.
    simpl. asserts_rewrite (pre_cwp 1 R = R'0 cwp). {
      symmetry. apply (right_cwp R R'0 F F'); iauto.
    } 
    iauto.
    iauto.
    asserts_rewrite (get_R r17 (next R'0 # r0 <- ((get_R r0 R) +ᵢ a)) = get_R r17 R'0). iauto. auto. auto.
    (* trap? no !*){
    inverts H4.
    asserts_rewrite (win_masked (pre_cwp 1 R) R = false) in H0. {
      apply (mask_cwp_pre2 R); iauto. apply IVR.
    }
    simpl in H0.
    inverts H0.
    }
    }
    (* annul? no !*){
    inverts H5.
    false.
    apply (AnnulDeq R).
    apply H8. apply IVR.
    }
  }
  }

  assert (R'#pc = R_#pc +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)+ᵢ ($4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)  +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) /\ normal_cursor (R',F')) as CSR'. {
    splits. {
      asserts_rewrite (get_R pc R' = get_R npc R). iauto.
      asserts_rewrite (get_R npc R = (get_R pc R) +ᵢ ($ 4)). apply CSR.
      asserts_rewrite (get_R pc R = (get_R pc R_) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)+ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)). apply CSR.
      auto.
    }
    {
      unfolds.
        asserts_rewrite (get_R npc R' = (get_R npc R) +ᵢ ($ 4)). iauto.
        asserts_rewrite (get_R pc R'  = get_R npc R). iauto.
        auto.
    }
  }

  {
  assert (handler_context R') as IVR'. {
    unfolds.
    splits; try unfolds; try unfolds;
    try asserts_rewrite ((get_R annul R') = (get_R annul R)); 
    try asserts_rewrite ((get_R et R') = (get_R et R));
    try asserts_rewrite ((get_R trap R') = (get_R trap R));
    try asserts_rewrite ((get_R s R') = (get_R s R));
    iauto; try apply IVR.
    unfolds in IVR.
    asserts_rewrite(Int.unsigned Asm.N - 1 = 7). {
      unfold Asm.N. mauto.
    }
    asserts_rewrite((get_R cwp R') = pre_cwp 1 R). iauto.
    apply (cwp_cycle_pre R). apply IVR.
  }

  assert (word_aligned_R R'#l1 /\ word_aligned_R R'#l2) as ALIGN'. {
    {
      remember (right_win 1 (R, F)) as K.
      destruct K as (Rr,Fr).
      asserts_rewrite ((get_R r17 R')  = (get_R r17 Rr)). iauto.
      asserts_rewrite ((get_R r18 R')  = (get_R r18 Rr)). iauto.
      iauto.
    }  
  }

  assert (single_mask2 (post_cwp 1 R') (get_R wim R')) as MASK'. {
    asserts_rewrite ((get_R wim R') = (get_R wim R)). iauto.
    apply (Post2_add_1_is_3 R R'); iauto.
  }

  assert (D' = []) as DELAY'. {
    asserts_rewrite (D' = D). iauto. iauto.
  }

  assert (f_context F') as CONT'. {
    remember (right_win 1 (R, F)) as K.
      destruct K as (Rr,Fr).
    asserts_rewrite(F' = Fr). iauto.
    apply (hold_context_right R Rr F Fr); iauto. 
  }

  assert (Z__ (Cu, Cs) (Mu, Ms_, (R_, F_),[]) [None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None] 28 (Mu, Ms', (R', F'),D')) as GOAL'. {
    apply (No_Event (Cu,Cs) [None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None] 27 (Mu, Ms_, (R_, F_),[]) (Mu, Ms', (R', F'),D') (Mu, Ms, (R, F),D));
    try rewrite DELAY in *; auto.
  }
  clear H P__ IVR MASK CSR DELAY ALIGN GOAL CONT.
  clear Ms R F D.
  rename Ms' into Ms.
  rename R' into R.
  rename F' into F.
  rename D' into D.
  rename IVR' into IVR.
  rename MASK' into MASK.
  rename CSR' into CSR.
  rename DELAY' into DELAY.
  rename GOAL' into GOAL.
  rename ALIGN' into ALIGN.
  rename CONT' into CONT.



(* step 29 *)

   assert (not_abort Cs Ms (R,F) D) as NA. {
    unfolds.
    exists (R,F) D  (jmpl l1 ₐᵣ g0).
    splits.
    - substs. auto.
    - asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)); iauto. apply FUNC.
    - unfolds. auto.
  }

  (* to P__ *)
  assert
  (exists Ms' Q' D', P__ (Cu,Cs) ((Mu,Ms),(R,F),D) ((Mu,Ms'),Q',D')) as H. {
    apply (Exists_P_Sup Cu Cs Mu Ms (R,F) D);
    auto; try apply IVR.
  }
  destruct H as (Ms' & Q' & D' & P__).
  destruct Q' as (R' & F').
  clear NA.

  (* deal with delay *)
  rewrite DELAY in *.

  (* small changes in one step *)
  assert (R'#pc = R#npc /\
          R'#annul = R#annul /\ R'#et = R#et /\ R'#trap = R#trap /\ R'#s = R#s /\ R'#wim = R#wim /\
          R'#cwp = R#cwp /\ R'#l2 = R#l2 /\ D' = [] /\ F' = F). {
  inverts P__.
  (* usr_mode *) {
    false. apply (ModeDeq (R,F)); auto.
    apply IVR.
  }
   (* sup_mode *) {
    inverts H10.
    unfolds in H6.
    inverts H6.
    assert (Cs (cursor_Q (R, F)) = Some (jmpl l1 ₐᵣ g0)) as INS. {
    asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)); iauto. apply FUNC.
    }
    rewrite H11 in INS.
    clear H11. inverts INS.

    {
    inverts H12; try solve [false].
    inverts H5; try solve [false].
    inverts H4; repeat (split; auto); auto.
    unfold unexpected_trap in *.
    unfold trap_type in *.
    unfold eval_AddrExp in *.
    unfold eval_OpExp in *.
    asserts_rewrite(word_aligned (get_R r17 R) = true) in H4. iauto.
    simpl in H4.
    inverts H4.
    }

    (* annul? no !*){
    inverts H5.
    false.
    apply (AnnulDeq R).
    apply H8. apply IVR.
    }
  }
  }

  assert (R'#pc = R_#pc +ᵢ ($4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($4) +ᵢ ($4) +ᵢ ($4)+ᵢ ($4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)  +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)) as CSR'. {
      asserts_rewrite (get_R pc R' = get_R npc R). iauto.
      asserts_rewrite (get_R npc R = (get_R pc R) +ᵢ ($ 4)). apply CSR.
      asserts_rewrite (get_R pc R = (get_R pc R_) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)+ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)). apply CSR.
      auto.
  }

  {
  assert (handler_context R') as IVR'. {
    unfolds.
    splits; try unfolds; try unfolds;
    try asserts_rewrite ((get_R cwp R') = (get_R cwp R)); 
    try asserts_rewrite ((get_R annul R') = (get_R annul R)); 
    try asserts_rewrite ((get_R et R') = (get_R et R));
    try asserts_rewrite ((get_R trap R') = (get_R trap R));
    try asserts_rewrite ((get_R s R') = (get_R s R));
    iauto; try apply IVR.
  }

  assert (word_aligned_R R'#r18) as ALIGN'. {
    asserts_rewrite (get_R r18 R' = get_R r18 R). iauto. iauto.
  }

  assert (single_mask2 (post_cwp 1 R') (get_R wim R')) as MASK'. {
    unfold post_cwp.
    asserts_rewrite (get_R cwp R' = get_R cwp R). iauto.
    asserts_rewrite (get_R wim R' = get_R wim R). iauto.
    apply MASK.
  }

  assert (D' = []) as DELAY'. {
    iauto.
  }

  assert (f_context F') as CONT'. {
    asserts_rewrite(F' = F). iauto. iauto.
  }

  assert (Z__ (Cu, Cs) (Mu, Ms_, (R_, F_),[]) [None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None] 29 (Mu, Ms', (R', F'),D')) as GOAL'. {
    apply (No_Event (Cu,Cs) [None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None] 28 (Mu, Ms_, (R_, F_),[]) (Mu, Ms', (R', F'),D') (Mu, Ms, (R, F),D));
    try rewrite DELAY in *; auto.
  }
  clear H P__ IVR MASK CSR DELAY ALIGN GOAL CONT.
  clear Ms R F D.
  rename Ms' into Ms.
  rename R' into R.
  rename F' into F.
  rename D' into D.
  rename IVR' into IVR.
  rename MASK' into MASK.
  rename CSR' into CSR.
  rename DELAY' into DELAY.
  rename GOAL' into GOAL.
  rename ALIGN' into ALIGN.
  rename CONT' into CONT.





(* step 30 *)

   assert (not_abort Cs Ms (R,F) D) as NA. {
    unfolds.
    exists (R,F) D  (rett l2 ₐᵣ).
    splits.
    - substs. auto.
    - asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)); iauto. apply FUNC.
    - unfolds. auto.
      unfold unexpected_trap in *.
      unfold trap_type in *.
      unfold eval_AddrExp in *.
      unfold eval_OpExp in *.
      asserts_rewrite(word_aligned (get_R r18 R) = true). iauto.
      asserts_rewrite(usr_mode R = false). apply IVR.
      unfolds inc_win.
      asserts_rewrite (win_masked (post_cwp 1 R) R = false). {
      apply (mask_cwp_post3 R); iauto. apply IVR.
    }
    simpl. auto.
  }

  (* to P__ *)
  assert
  (exists Ms' Q' D', P__ (Cu,Cs) ((Mu,Ms),(R,F),D) ((Mu,Ms'),Q',D')) as H. {
    apply (Exists_P_Sup Cu Cs Mu Ms (R,F) D);
    auto; try apply IVR.
  }
  destruct H as (Ms' & Q' & D' & P__).
  destruct Q' as (R' & F').
  clear NA.

  (* deal with delay *)
  rewrite DELAY in *.

  (* small changes in one step *)
  assert (R'#trap = R#trap /\ R'#wim = R#wim /\
          R'#cwp = post_cwp 1 R /\ D' = []). {
  inverts P__.
  (* usr_mode *) {
    false. apply (ModeDeq (R,F)); auto.
    apply IVR.
  }
   (* sup_mode *) {
    inverts H10.
    unfolds in H6.
    inverts H6.
    assert (Cs (cursor_Q (R, F)) = Some (rett l2 ₐᵣ)) as INS. {
    asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)); iauto. apply FUNC.
    }
    rewrite H11 in INS.
    clear H11. inverts INS.

    {
    inverts H12; try solve [false].
    inverts H5; try solve [false].
    inverts H10.

    unfold rett_f in H17.
    unfolds inc_win.
    asserts_rewrite (win_masked (post_cwp 1 R) R = false) in H17. {
      apply (mask_cwp_post3 R); iauto. apply IVR.
    }
    unfold negb in H17.
    remember (left_win 1 (R, F)).
    destruct r.
    inverts H17.
    assert (some_reg_eq R r). {
      apply (Hold_Sth_LeftWin R r F F' 1); iauto.
    }
    unfolds in H. simpl in H.
    splits.
    simpl. asserts_rewrite (R trap = r trap). iauto. auto.
    simpl. asserts_rewrite (R Rwim = r Rwim). iauto. auto.
    asserts_rewrite(get_R cwp (djmp w (restore_mode (enable_trap r))) = get_R cwp r). iauto.
    apply (left_cwp R r F F'); iauto.
    auto.

    unfold unexpected_trap in *.
    unfold trap_type in *.
    unfold eval_AddrExp in *.
    unfold eval_OpExp in *.
    asserts_rewrite(trap_enabled R = false) in H4. apply IVR.
    inverts H4.
    }

    (* annul? no !*){
    inverts H5.
    false.
    apply (AnnulDeq R).
    apply H8. apply IVR.
    }
  }
  }

  assert (single_mask2 R'#cwp R'#wim) as MASK'. {
    asserts_rewrite (get_R cwp R' = post_cwp 1 R). iauto.
    asserts_rewrite (get_R wim R' = get_R wim R). iauto.
    apply MASK.
  }

  assert (D' = []) as DELAY'. {
    iauto.
  }

  assert (Z__ (Cu, Cs) (Mu, Ms_, (R_, F_),[]) [None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None] 30 (Mu, Ms', (R', F'),D')) as GOAL'. {
    apply (No_Event (Cu,Cs) [None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None;None] 29 (Mu, Ms_, (R_, F_),[]) (Mu, Ms', (R', F'),D') (Mu, Ms, (R, F),D));
    try rewrite DELAY in *; auto.
  }
  clear H P__ IVR MASK CSR DELAY ALIGN GOAL CONT.
  clear Ms R F D.
  rename Ms' into Ms.
  rename R' into R.
  rename F' into F.
  rename D' into D.
  rename MASK' into MASK.
  rename DELAY' into DELAY.
  rename GOAL' into GOAL.


(* Done! *)


  remember ([None; None; None; None; None; None; None; None; None; None; None;
         None; None; None; None; None; None; None; None; None; None; None;
         None; None; None; None; None; None; None; None]) as E.
  exists (Mu, Ms, (R, F), D) E.
  splits. auto.
  unfolds. auto.
  rewrite HeqE.
  simpl. auto.
Qed.



