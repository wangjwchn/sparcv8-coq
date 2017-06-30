Require Import Asm.
Require Import Coqlib.
Require Import Props.
Require Import LibTactics.
Import ListNotations.
Local Open Scope sparc_scope.
Require Import int_auto.
Require Import math_sol.
Require Import Integers.
Require Import Coq.Logic.FunctionalExtensionality.

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
  or g0 g1 ᵣ l7;
  srl l3 ($1)ₙ g1;
  sll l3 (Asm.N-ᵢ($1))ₙ l4;
  or l4 g1 ᵣ g1;
  save g0 g0 ᵣ g0;
  wr g0 g1 ᵣ wim;
  nop;
  nop;
  nop;
  st l0 sp ₐᵣ;
  st l1 sp+ₐₙ($4);
  st l2 sp+ₐₙ($8);
  st l3 sp+ₐₙ($12);
  st l4 sp+ₐₙ($16);
  st l5 sp+ₐₙ($20);
  st l6 sp+ₐₙ($24);
  st l7 sp+ₐₙ($28);
  st i0 sp+ₐₙ($32);
  st i1 sp+ₐₙ($36);
  st i2 sp+ₐₙ($40);
  st i3 sp+ₐₙ($44);
  st i4 sp+ₐₙ($48);
  st i5 sp+ₐₙ($52);
  st i6 sp+ₐₙ($56);
  st i7 sp+ₐₙ($60);
  restore g0 g0 ᵣ g0;
  or g0 l7 ᵣ g1;
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


Definition handler_context (R: RegFile) :=
 0 <= Int.unsigned (R#cwp) <= Int.unsigned(Asm.N)-1 /\ not_annuled_R R /\ trap_disabled_R R /\
  no_trap_R R /\  sup_mode_R R.

Definition single_mask : Word -> Word -> Prop :=
  fun cwp wim =>
    ($1) <<ᵢ cwp = wim.

Definition align_context(O: RState) :=
  let (R,F) := O in word_aligned_R R#l1 /\ word_aligned_R R#l2 /\ 
      let (R',F') := right_win 1 (R,F) in word_aligned_R R'#sp.

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
    let (R,F) := Q in
    set_function (cursor_Q Q) overflow_handler Cs /\ normal_cursor Q /\
    handler_context R /\ align_context Q /\ single_mask R#cwp R#wim /\ D = nil /\ f_context F.

Definition overflow_post_cond : Cond :=
  fun W =>
    let (CP,S) := W in
    let (Cu,Cs) := CP in
    let '(MP,Q,_) := S in
    let (R,F) := Q in
    single_mask (pre_cwp 2 R) R#wim.

Lemma get_range7:
  forall w,
    get_range 0 7 w = w &ᵢ ($255).
Proof.
  intros.
  unfolds.
  mauto.
Qed.

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

(* align 4 *)
Lemma align_div:
  forall n,
  0<= (Int.unsigned n) <= Int.max_unsigned - 4 ->
  Int.divu (n+ᵢ ($4)) ($4) = (Int.divu (n) ($4)) +ᵢ ($1).
Proof.
  intros.
  int auto; remember (Int.unsigned n).
  apply (Z_div_plus_full z 1 4).
  omega.
  split;
  clear Heqz n.
  SearchAbout Z.le Z.div.
  apply (Z_div_pos z 4).
  omega.
  auto.
  SearchAbout Z.le Z.div.
  apply (Z_div_le z (4294967295*4) 4).
  omega.
  omega.
Qed.


(*
Int.modu_divu:
  forall x y : int32,
  y <> Int.zero -> x modu y = x -ᵢ (Int.mul (Int.divu x y) y)
*)

Lemma align_modu:
  forall n,
  0<= (Int.unsigned n) <= Int.max_unsigned - 4 ->
  Int.modu n ($4) = ($0) ->
  Int.modu (n+ᵢ ($4)) ($4) = ($0).
Proof.
  intros.
  SearchAbout Int.modu.
  assert (n modu ($4) = n -ᵢ (Int.mul (Int.divu n ($4)) ($4))).
  apply Int.modu_divu. {
    clear n H H0. mauto.
  }
  assert ((n+ᵢ$4) modu ($4) = (n+ᵢ$4) -ᵢ (Int.mul (Int.divu (n+ᵢ$4) ($4)) ($4))).
  apply Int.modu_divu. {
    clear n H H0 H1. mauto.
  }
  rewrite H0 in H1.
  clear H0.
  assert ((n +ᵢ ($ 4)) -ᵢ (Int.mul (Int.divu n +ᵢ ($ 4) $ 4) $ 4) = ($0)). {
  clear H2.
  asserts_rewrite (Int.divu (n+ᵢ ($4)) ($4) = (Int.divu (n) ($4)) +ᵢ ($1)).
  apply align_div; eauto.
  SearchAbout Int.mul.
  asserts_rewrite ((Int.mul (Int.divu n $ 4) +ᵢ ($ 1) $ 4) = 
    (Int.mul (Int.divu n ($4)) $4) +ᵢ (Int.mul ($1) ($4))). {
    apply (Int.mul_add_distr_l (Int.divu n $ 4) ($1) ($4)).
  }
  SearchAbout Int.add Int.sub.
  asserts_rewrite ((Int.mul $ 1 $ 4) = ($4)). {
    SearchAbout Int.mul.
    apply Int.mul_commut.
  }
  SearchAbout Int.add Int.sub.
  asserts_rewrite ((n +ᵢ ($ 4)) -ᵢ ((Int.mul (Int.divu n $ 4) $ 4) +ᵢ ($ 4)) = n -ᵢ (Int.mul (Int.divu n $ 4) $ 4)).
  apply (Int.sub_shifted n (Int.mul (Int.divu n $ 4) $ 4) ($4)).
  eauto.
}
  rewrite H2.
  apply H0.
Qed.

(* Int.modu_and: *)
Lemma align_and:
  forall n,
  0<= (Int.unsigned n) <= Int.max_unsigned - 4 ->
  n &ᵢ ($3) = ($0) ->
  (n+ᵢ ($4)) &ᵢ ($3) = ($0).
Proof.
  intros.
  assert ($3 = $4 -ᵢ Int.one). auto.
  rewrite H1 in H0. rewrite H1. clear H1.
  asserts_rewrite (n &ᵢ (($ 4) -ᵢ Int.one) = (n modu ($4))) in H0.
  symmetry.
      SearchAbout Int.modu.
    apply (Int.modu_and n ($4) ($2)).
    auto.
 asserts_rewrite ((n +ᵢ ($ 4)) &ᵢ (($ 4) -ᵢ Int.one) = ((n +ᵢ ($ 4)) modu ($4))).
  symmetry.
      apply (Int.modu_and (n +ᵢ ($ 4)) ($4) ($2)).
    auto.
    apply align_modu; eauto.
Qed.

Lemma align_plus4_part:
  forall w,
  0 <= (Int.unsigned w) <= Int.max_unsigned - 4 ->
  word_aligned_R w ->
  word_aligned_R w +ᵢ ($4).
Proof.
  intros.
  unfold word_aligned_R in *.
  unfold word_aligned in *.
  unfold get_range in *.
  asserts_rewrite ((((($ 1) <<ᵢ ($ (1 - 0 + 1))) -ᵢ ($ 1)) <<ᵢ ($ 0)) = ($3)) in *. auto.

  remember ((w &ᵢ ($ 3)) =ᵢ ($ 0)).
  destruct b; inverts H0.

  assert (if (w &ᵢ ($ 3)) =ᵢ ($ 0) then (w &ᵢ ($ 3)) = ($0) else (w &ᵢ ($ 3)) <> ($ 0)).
  {
    apply Int.eq_spec.
  }
  rewrite <- Heqb in H0. clear Heqb.
  asserts_rewrite (((w +ᵢ ($ 4)) &ᵢ ($ 3)) = ($0)).
  {
    apply align_and; eauto.
  }
  asserts_rewrite (($ 0) =ᵢ ($ 0) = true). apply Int.eq_true.
  auto.
Qed.

Lemma align_out_range3:
  forall w,
  (Int.unsigned w) = Int.max_unsigned - 3 ->
  word_aligned_R w ->
  word_aligned_R w +ᵢ ($4).
Proof.
  intros.
  unfold word_aligned_R in *.
  unfold word_aligned in *.
  unfold get_range in *.
  asserts_rewrite ((((($ 1) <<ᵢ ($ (1 - 0 + 1))) -ᵢ ($ 1)) <<ᵢ ($ 0)) = ($3)) in *. auto.

  assert (w = $(Int.max_unsigned - 3)).
  symmetry.
  apply (Int.eqm_repr_eq (Int.max_unsigned - 3) w).
  rewrite H. apply Int.eqm_refl.

  asserts_rewrite (((w +ᵢ ($ 4)) &ᵢ ($ 3)) = ($ 0)).
  {
   clear H0. rewrite H1.
   clear H1. auto.
  }
  asserts_rewrite (($ 0) =ᵢ ($ 0) = true). apply Int.eq_true.
  auto.
Qed.


Lemma align_out_range2:
  forall w,
  (Int.unsigned w) = Int.max_unsigned - 2 ->
  word_aligned_R w ->
  word_aligned_R w +ᵢ ($4).
Proof.
  intros.
  unfold word_aligned_R in *.
  unfold word_aligned in *.
  unfold get_range in *.
  asserts_rewrite ((((($ 1) <<ᵢ ($ (1 - 0 + 1))) -ᵢ ($ 1)) <<ᵢ ($ 0)) = ($3)) in *. auto.

  assert (w = $(Int.max_unsigned - 2)).
  symmetry.
  apply (Int.eqm_repr_eq (Int.max_unsigned - 2) w).
  rewrite H. apply Int.eqm_refl.

  assert ((w &ᵢ ($ 3)) = ($ 1)).
  {
  clear H. rewrite H1. auto.
  }
  rewrite H2 in H0.
  asserts_rewrite (($ 1) =ᵢ ($ 0) = false) in H0.
  auto. inverts H0.
Qed.

Lemma align_out_range1:
  forall w,
  (Int.unsigned w) = Int.max_unsigned - 1 ->
  word_aligned_R w ->
  word_aligned_R w +ᵢ ($4).
Proof.
  intros.
  unfold word_aligned_R in *.
  unfold word_aligned in *.
  unfold get_range in *.
  asserts_rewrite ((((($ 1) <<ᵢ ($ (1 - 0 + 1))) -ᵢ ($ 1)) <<ᵢ ($ 0)) = ($3)) in *. auto.

  assert (w = $(Int.max_unsigned - 1)).
  symmetry.
  apply (Int.eqm_repr_eq (Int.max_unsigned - 1) w).
  rewrite H. apply Int.eqm_refl.

  assert ((w &ᵢ ($ 3)) = ($ 2)).
  {
  clear H. rewrite H1. auto.
  }
  rewrite H2 in H0.
  asserts_rewrite (($ 2) =ᵢ ($ 0) = false) in H0.
  auto. inverts H0.
Qed.

Lemma align_out_range0:
  forall w,
  (Int.unsigned w) = Int.max_unsigned ->
  word_aligned_R w ->
  word_aligned_R w +ᵢ ($4).
Proof.
  intros.
  unfold word_aligned_R in *.
  unfold word_aligned in *.
  unfold get_range in *.
  asserts_rewrite ((((($ 1) <<ᵢ ($ (1 - 0 + 1))) -ᵢ ($ 1)) <<ᵢ ($ 0)) = ($3)) in *. auto.

  assert (w = $(Int.max_unsigned)).
  symmetry.
  apply (Int.eqm_repr_eq (Int.max_unsigned) w).
  rewrite H. apply Int.eqm_refl.

  assert ((w &ᵢ ($ 3)) = ($ 3)).
  {
  clear H. rewrite H1. auto.
  }
  rewrite H2 in H0.
  asserts_rewrite (($ 3) =ᵢ ($ 0) = false) in H0.
  auto. inverts H0.
Qed.

Lemma align_my_word:
  forall n,
  0<= (Int.unsigned n) <= Int.max_unsigned - 4 \/
  Int.unsigned n = Int.max_unsigned - 3 \/
  Int.unsigned n = Int.max_unsigned - 2 \/
  Int.unsigned n = Int.max_unsigned - 1 \/
  Int.unsigned n = Int.max_unsigned.
Proof.
  intros.
  assert(0<= (Int.unsigned n) <= Int.max_unsigned).
  apply Int.unsigned_range_2.
  int auto.
Qed.


Lemma align_plus4:
  forall w,
  word_aligned_R w ->
  word_aligned_R w +ᵢ ($4).
Proof.
  intros.
  assert (0<= (Int.unsigned w) <= Int.max_unsigned - 4 \/
  Int.unsigned w = Int.max_unsigned - 3 \/
  Int.unsigned w = Int.max_unsigned - 2 \/
  Int.unsigned w = Int.max_unsigned - 1 \/
  Int.unsigned w = Int.max_unsigned).
  apply align_my_word.
  destruct H0.
  apply align_plus4_part; eauto.
  destruct H0.
  apply align_out_range3; eauto.
  destruct H0.
  apply align_out_range2; eauto.
    destruct H0.
  apply align_out_range1; eauto.
  apply align_out_range0; eauto.
Qed.



Lemma cwp_cycle_pre:
  forall R,
      0 <= Int.unsigned (R#cwp) <= 7 ->
      0 <= Int.unsigned (pre_cwp 1 R) <= 7.
Proof.
  intros.
  unfold pre_cwp.
  unfold Asm.N.
  remember (get_R cwp R) as cwp.
  clear Heqcwp.

  remember (Int.unsigned cwp) as n.

  assert (n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5
   \/ n = 6 \/ n = 7). mauto. clear H.
  rename H0 into H.

  destruct H.
  int auto; rewrite <- Heqn;
  try rewrite H; int auto; simpl;
  asserts_rewrite (7 mod 8 = 7); try solve [compute; auto];
  omega.
  destruct H.
  int auto; rewrite <- Heqn;
  try rewrite H; int auto; simpl;
  asserts_rewrite (8 mod 8 = 0); try solve [compute; auto];
  omega.
  destruct H.
  int auto; rewrite <- Heqn;
  try rewrite H; int auto; simpl;
  asserts_rewrite (9 mod 8 = 1); try solve [compute; auto];
  omega.
  destruct H.
  int auto; rewrite <- Heqn;
  try rewrite H; int auto; simpl;
  asserts_rewrite (10 mod 8 = 2); try solve [compute; auto];
  omega.
  destruct H.
  int auto; rewrite <- Heqn;
  try rewrite H; int auto; simpl;
  asserts_rewrite (11 mod 8 = 3); try solve [compute; auto];
  omega.
  destruct H.
  int auto; rewrite <- Heqn;
  try rewrite H; int auto; simpl;
  asserts_rewrite (12 mod 8 = 4); try solve [compute; auto];
  omega.
  destruct H.
  int auto; rewrite <- Heqn;
  try rewrite H; int auto; simpl;
  asserts_rewrite (13 mod 8 = 5); try solve [compute; auto];
  omega.
  int auto; rewrite <- Heqn;
  try rewrite H; int auto; simpl;
  asserts_rewrite (14 mod 8 = 6); try solve [compute; auto];
  omega.
Qed.


Lemma post_is_pre:
    forall R R',
    0 <= Int.unsigned (R#cwp) <= 7 ->
    get_R cwp R' = post_cwp 1 R  ->
    get_R cwp R = pre_cwp 1 R'.
Proof.
  intros.
  unfold post_cwp in H0.
  unfold pre_cwp.
  rewrite H0. clear H0.
  unfold Asm.N.
  remember (get_R cwp R) as cwp.
  clear Heqcwp.

  remember (Int.unsigned cwp) as n.

  assert (n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5
   \/ n = 6 \/ n = 7). mauto. clear H.
  rename H0 into H.

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


Lemma pre_is_post:
    forall R R',
    0 <= Int.unsigned (R'#cwp) <= 7 ->
    get_R cwp R  = pre_cwp 1 R' ->
    get_R cwp R' = post_cwp 1 R.
Proof.
  intros.
  unfold pre_cwp in H0.
  unfold post_cwp.
  rewrite H0. clear H0.
  unfold Asm.N.
  remember (get_R cwp R') as cwp.
  clear Heqcwp.

  remember (Int.unsigned cwp) as n.

  assert (n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5
   \/ n = 6 \/ n = 7). mauto. clear H.
  rename H0 into H.

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

Lemma cwp_cycle_post:
  forall R,
      0 <= Int.unsigned (R#cwp) <= 7 ->
      0 <= Int.unsigned (post_cwp 1 R) <= 7.
Proof.
  intros.
  unfold post_cwp.
  unfold Asm.N.
  remember (get_R cwp R) as cwp.
  clear Heqcwp.

  remember (Int.unsigned cwp) as n.

  assert (n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5
   \/ n = 6 \/ n = 7). mauto. clear H.
  rename H0 into H.

  destruct H.
  int auto; rewrite <- Heqn;
  try rewrite H; int auto; simpl;
  asserts_rewrite (1 mod 8 = 1); try solve [compute; auto];
  omega.
  destruct H.
  int auto; rewrite <- Heqn;
  try rewrite H; int auto; simpl;
  asserts_rewrite (2 mod 8 = 2); try solve [compute; auto];
  omega.
  destruct H.
  int auto; rewrite <- Heqn;
  try rewrite H; int auto; simpl;
  asserts_rewrite (3 mod 8 = 3); try solve [compute; auto];
  omega.
  destruct H.
  int auto; rewrite <- Heqn;
  try rewrite H; int auto; simpl;
  asserts_rewrite (4 mod 8 = 4); try solve [compute; auto];
  omega.
  destruct H.
  int auto; rewrite <- Heqn;
  try rewrite H; int auto; simpl;
  asserts_rewrite (5 mod 8 = 5); try solve [compute; auto];
  omega.
  destruct H.
  int auto; rewrite <- Heqn;
  try rewrite H; int auto; simpl;
  asserts_rewrite (6 mod 8 = 6); try solve [compute; auto];
  omega.
  destruct H.
  int auto; rewrite <- Heqn;
  try rewrite H; int auto; simpl;
  asserts_rewrite (7 mod 8 = 7); try solve [compute; auto];
  omega.
  int auto; rewrite <- Heqn;
  try rewrite H; int auto; simpl;
  asserts_rewrite (8 mod 8 = 0); try solve [compute; auto];
  omega.
Qed.

Lemma mask_cwp:
    forall R,
    0 <= Int.unsigned (R#cwp) <= 7 ->
    single_mask R#cwp (R#wim) ->
    win_masked (pre_cwp 1 R) R = false.
Proof.
  intros.
  unfolds in H0.
  unfolds.
  rewrite <- H0.
  clear H0.
  unfold pre_cwp.
  unfold Asm.N.
  remember (get_R cwp R) as cwp.
  clear Heqcwp.

  remember (Int.unsigned cwp) as n.

 assert (n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5
   \/ n = 6 \/ n = 7). mauto. clear H.

  asserts_rewrite (((($ 1) <<ᵢ (((cwp +ᵢ ($ 8)) -ᵢ ($ 1)) modu ($ 8))) &ᵢ (($ 1) <<ᵢ cwp)) = ($0)).


  rename H0 into H.
  destruct H.
  int auto; rewrite <- Heqn;
  try rewrite H; int auto; mauto;
  simpl; int auto; mauto.
  destruct H.
  int auto; rewrite <- Heqn;
  try rewrite H; int auto; mauto;
  simpl; int auto; mauto.
  destruct H.
  int auto; rewrite <- Heqn;
  try rewrite H; int auto; mauto;
  simpl; int auto; mauto.
  destruct H.
  int auto; rewrite <- Heqn;
  try rewrite H; int auto; mauto;
  simpl; int auto; mauto.
  destruct H.
  int auto; rewrite <- Heqn;
  try rewrite H; int auto; mauto;
  simpl; int auto; mauto.
  destruct H.
  int auto; rewrite <- Heqn;
  try rewrite H; int auto; mauto;
  simpl; int auto; mauto.
  destruct H.
  int auto; rewrite <- Heqn;
  try rewrite H; int auto; mauto;
  simpl; int auto; mauto.
  int auto; rewrite <- Heqn;
  try rewrite H; int auto; mauto;
  simpl; int auto; mauto.

  auto.
Qed.


Lemma mask_cwp_post:
    forall R,
    0 <= Int.unsigned (R#cwp) <= 7 ->
    single_mask R#cwp (R#wim) ->
    win_masked (post_cwp 1 R) R = false.
Proof.
  intros.
  unfolds in H0.
  unfolds.
  rewrite <- H0.
  clear H0.
  unfold post_cwp.
  unfold Asm.N.
  remember (get_R cwp R) as cwp.
  clear Heqcwp.

  remember (Int.unsigned cwp) as n.

 assert (n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5
   \/ n = 6 \/ n = 7). mauto. clear H.

  asserts_rewrite (((($ 1) <<ᵢ ((cwp +ᵢ ($ 1)) modu ($ 8))) &ᵢ (($ 1) <<ᵢ cwp)) = ($0)).


  rename H0 into H.
  destruct H.
  int auto; rewrite <- Heqn;
  try rewrite H; int auto; mauto;
  simpl; int auto; mauto.
  destruct H.
  int auto; rewrite <- Heqn;
  try rewrite H; int auto; mauto;
  simpl; int auto; mauto.
  destruct H.
  int auto; rewrite <- Heqn;
  try rewrite H; int auto; mauto;
  simpl; int auto; mauto.
  destruct H.
  int auto; rewrite <- Heqn;
  try rewrite H; int auto; mauto;
  simpl; int auto; mauto.
  destruct H.
  int auto; rewrite <- Heqn;
  try rewrite H; int auto; mauto;
  simpl; int auto; mauto.
  destruct H.
  int auto; rewrite <- Heqn;
  try rewrite H; int auto; mauto;
  simpl; int auto; mauto.
  destruct H.
  int auto; rewrite <- Heqn;
  try rewrite H; int auto; mauto;
  simpl; int auto; mauto.
  int auto; rewrite <- Heqn;
  try rewrite H; int auto; mauto;
  simpl; int auto; mauto.

  auto.
Qed.

Lemma pre_pre_is_pre2:
  forall R R',
  0 <= Int.unsigned (R#cwp) <= 7 ->
  get_R cwp R' = post_cwp 1 R ->
  (pre_cwp 1 R) = (pre_cwp 2 R').
Proof.
  intros.
  unfold post_cwp in H0.
  unfold pre_cwp.

  rewrite H0.
  clear H0.

  unfold Asm.N.
  remember (get_R cwp R) as cwp.
  clear Heqcwp.


  remember (Int.unsigned cwp) as n.

 assert (n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5
   \/ n = 6 \/ n = 7). mauto. clear H.

  rename H0 into H.

  destruct H.
  {
    substs.
    int auto;
    rewrite H;
    simpl;
    int auto;
    int auto;
    mauto.
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
  }
  {
    substs.
    int auto;
    rewrite H;
    simpl;
    int auto;
    int auto;
    mauto.
  }
Qed.


Lemma mask_cwp_post2:
    forall R,
    0 <= Int.unsigned (R#cwp) <= 7 ->
    single_mask (pre_cwp 1 R) (R#wim) ->
    win_masked (post_cwp 1 R) R = false.
Proof.
  intros.
  unfolds in H0.
  unfolds.
  unfold pre_cwp in H0.
  rewrite <- H0.
  clear H0.
  unfold post_cwp.
  unfold Asm.N.
  remember (get_R cwp R) as cwp.
  clear Heqcwp.

  remember (Int.unsigned cwp) as n.

 assert (n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5
   \/ n = 6 \/ n = 7). mauto. clear H.

  asserts_rewrite (((($ 1) <<ᵢ ((cwp +ᵢ ($ 1)) modu ($ 8))) &ᵢ
   (($ 1) <<ᵢ (((cwp +ᵢ ($ 8)) -ᵢ ($ 1)) modu ($ 8)))) = ($0)).


  rename H0 into H.
  destruct H.
  int auto; rewrite <- Heqn;
  try rewrite H; int auto; mauto;
  simpl; int auto; mauto.
  destruct H.
  int auto; rewrite <- Heqn;
  try rewrite H; int auto; mauto;
  simpl; int auto; mauto.
  destruct H.
  int auto; rewrite <- Heqn;
  try rewrite H; int auto; mauto;
  simpl; int auto; mauto.
  destruct H.
  int auto; rewrite <- Heqn;
  try rewrite H; int auto; mauto;
  simpl; int auto; mauto.
  destruct H.
  int auto; rewrite <- Heqn;
  try rewrite H; int auto; mauto;
  simpl; int auto; mauto.
  destruct H.
  int auto; rewrite <- Heqn;
  try rewrite H; int auto; mauto;
  simpl; int auto; mauto.
  destruct H.
  int auto; rewrite <- Heqn;
  try rewrite H; int auto; mauto;
  simpl; int auto; mauto.
  int auto; rewrite <- Heqn;
  try rewrite H; int auto; mauto;
  simpl; int auto; mauto.

  auto.
Qed.

Lemma Win_Xor:
forall cwp x y,
    0 <= Int.unsigned cwp <= 7 ->
    single_mask (cwp+ᵢ ($7)) y ->
     (1 <= Int.unsigned cwp <= 7 /\ single_mask(cwp -ᵢ ($1)) x) \/
     (Int.unsigned cwp = 0 /\ x = ($0)) ->
    single_mask ((cwp +ᵢ Asm.N -ᵢ ($1)) modu Asm.N) (y |ᵢ  x)&ᵢ($255).
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


Theorem HandleOverflow:
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
          R'#l3 = R#wim /\ R'#l1 = R#l1 /\ R'#l2 = R#l2 /\ R'#sp = R#sp /\ F' = F /\ D' = D). {
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

  assert (align_context (R',F')) as ALIGN'. {
    unfolds.
    splits; try unfolds; try unfolds;
    try asserts_rewrite (get_R r17 R' = get_R r17 R);
    try asserts_rewrite (get_R r18 R' = get_R r18 R); 
    try asserts_rewrite (get_R r30 R' = get_R r30 R);
    iauto; try apply ALIGN.
    {
      unfolds in ALIGN.
      unfold get_R.
      remember (right_win 1 (R, F)).
      destruct r as (R1 & F1).
      remember (right_win 1 (R', F')).
      destruct r as (R2 & F2).
      asserts_rewrite(F' = F) in Heqr0. iauto.
      unfold get_R in ALIGN.
      asserts_rewrite (R1 r14 = R2 r14) in ALIGN. {
        apply (right_right_same r14 R R' F R1 R2 F1 F2); iauto.
      } iauto.
    }
  }

  assert (single_mask R'#cwp R'#wim /\ single_mask (get_R cwp R') (get_R l3 R') ) as MASK'. {
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
    exists (R,F) D  (or g0 g1 ᵣ l7).
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
          R'#l3 = R#l3 /\ R'#l1 = R#l1 /\ R'#l2 = R#l2 /\ R'#fp = R#fp /\ F' = F /\ D' = D). {
  inverts P__.
  (* usr_mode *) {
    false. apply (ModeDeq (R,F)); auto.
    apply IVR.
  }
  (* sup_mode *) {
    inverts H10.
    unfolds in H6.
    inverts H6.
    assert (Cs (cursor_Q (R, F)) = Some (or g0 g1 ᵣ l7)) as INS. {
    asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4)). iauto.
    apply FUNC.
    }
    rewrite H11 in INS.
    clear H11. inverts INS.

    {
    inverts H12; try solve [false].
    inverts H5; try solve [false].
    inverts H4; repeat (split; auto); auto.
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

  assert (align_context (R',F')) as ALIGN'. {
    unfolds.
    splits; try unfolds; try unfolds;
    try asserts_rewrite (get_R r17 R' = get_R r17 R);
    try asserts_rewrite (get_R r18 R' = get_R r18 R); 
    try asserts_rewrite (get_R r30 R' = get_R r30 R);
    iauto; try apply ALIGN.
    {
      unfolds in ALIGN.
      unfold get_R.
      remember (right_win 1 (R, F)).
      destruct r as (R1 & F1).
      remember (right_win 1 (R', F')).
      destruct r as (R2 & F2).
      asserts_rewrite(F' = F) in Heqr0. iauto.
      unfold get_R in ALIGN.
      asserts_rewrite (R1 r14 = R2 r14) in ALIGN. {
        apply (right_right_same r14 R R' F R1 R2 F1 F2); iauto.
      } iauto.
    }
  }

  assert (single_mask R'#cwp R'#wim /\ single_mask (get_R cwp R') (get_R l3 R') ) as MASK'. {
    asserts_rewrite ((get_R cwp R') = (get_R cwp R)). iauto.
    asserts_rewrite ((get_R l3 R') = (get_R l3 R)). iauto.
    asserts_rewrite (get_R wim R' = get_R wim R). iauto.
    splits;
    apply MASK.
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
    exists (R,F) D  (srl l3 ($1)ₙ g1).
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
          R'#l3 = R#l3 /\ R'#g1 = R#l3 >>ᵢ ($1) /\ R'#l1 = R#l1 /\ R'#l2 = R#l2 /\ R'#fp = R#fp /\ F' = F /\ D' = D). {
  inverts P__.
  (* usr_mode *) {
    false. apply (ModeDeq (R,F)); auto.
    apply IVR.
  }
  (* sup_mode *) {
    inverts H10.
    unfolds in H6.
    inverts H6.
    assert (Cs (cursor_Q (R, F)) = Some (srl l3 ($1)ₙ g1)) as INS. {
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

  assert (align_context (R',F')) as ALIGN'. {
    unfolds.
    splits; try unfolds; try unfolds;
    try asserts_rewrite (get_R r17 R' = get_R r17 R);
    try asserts_rewrite (get_R r18 R' = get_R r18 R); 
    try asserts_rewrite (get_R r30 R' = get_R r30 R);
    iauto; try apply ALIGN.
    {
      unfolds in ALIGN.
      unfold get_R.
      remember (right_win 1 (R, F)).
      destruct r as (R1 & F1).
      remember (right_win 1 (R', F')).
      destruct r as (R2 & F2).
      asserts_rewrite(F' = F) in Heqr0. iauto.
      unfold get_R in ALIGN.
      asserts_rewrite (R1 r14 = R2 r14) in ALIGN. {
        apply (right_right_same r14 R R' F R1 R2 F1 F2); iauto.
      } iauto.
    }
  }

  assert (single_mask R'#cwp R'#wim /\ single_mask (R'#cwp) (R'#l3) /\
              ((1 <= Int.unsigned (R'#cwp) <= 7 /\ single_mask (R'#cwp) -ᵢ ($ 1) (R'#g1)) \/
              (Int.unsigned (R'#cwp) = 0 /\ (R'#g1) = ($0)))) as MASK'. {
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
      asserts_rewrite (get_R g1 R' = (get_R l3 R) >>ᵢ ($ 1)). iauto.
      asserts_rewrite (get_R cwp R' = get_R cwp R). iauto.
      apply Mask_When_Shiftr; iauto.
      apply IVR.
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
    exists (R,F) D  (sll l3 (Asm.N-ᵢ($1))ₙ l4).
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
          R'#l4 = R#l3 <<ᵢ($7) /\ R'#g1 = R#g1 /\ R'#l1 = R#l1 /\ R'#l2 = R#l2 /\ R'#fp = R#fp /\ F' = F /\ D' = D). {
  inverts P__.
  (* usr_mode *) {
    false. apply (ModeDeq (R,F)); auto.
    apply IVR.
  }
  (* sup_mode *) {
    inverts H10.
    unfolds in H6.
    inverts H6.
    assert (Cs (cursor_Q (R, F)) = Some (sll l3 (Asm.N-ᵢ($1))ₙ l4)) as INS. {
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

  assert (R'#pc = R_#pc +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) /\ normal_cursor (R',F')) as CSR'. {
    splits. {
      asserts_rewrite (get_R pc R' = get_R npc R). iauto.
      asserts_rewrite (get_R npc R = (get_R pc R) +ᵢ ($ 4)). apply CSR.
      asserts_rewrite (get_R pc R = (get_R pc R_) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)). apply CSR.
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

  assert (align_context (R',F')) as ALIGN'. {
    unfolds.
    splits; try unfolds; try unfolds;
    try asserts_rewrite (get_R r17 R' = get_R r17 R);
    try asserts_rewrite (get_R r18 R' = get_R r18 R); 
    try asserts_rewrite (get_R r30 R' = get_R r30 R);
    iauto; try apply ALIGN.
    {
      unfolds in ALIGN.
      unfold get_R.
      remember (right_win 1 (R, F)).
      destruct r as (R1 & F1).
      remember (right_win 1 (R', F')).
      destruct r as (R2 & F2).
      asserts_rewrite(F' = F) in Heqr0. iauto.
      unfold get_R in ALIGN.
      asserts_rewrite (R1 r14 = R2 r14) in ALIGN. {
        apply (right_right_same r14 R R' F R1 R2 F1 F2); iauto.
      } iauto.
    }
  }

  assert (single_mask R'#cwp (R'#wim) /\ single_mask (R'#cwp+ᵢ($7)) R'#l4 /\
              ((1 <= Int.unsigned (R'#cwp) <= 7 /\ single_mask (R'#cwp) -ᵢ ($ 1) (R'#g1)) \/
              (Int.unsigned (R'#cwp) = 0 /\ (R'#g1) = ($0)))) as MASK'. {
    splits.
    {
    asserts_rewrite (get_R wim R' = get_R wim R). iauto.
    asserts_rewrite (get_R cwp R' = get_R cwp R). iauto.
    apply MASK.
    }
    {
    asserts_rewrite (get_R l4 R' = (get_R l3 R) <<ᵢ ($ 7)). iauto.
    asserts_rewrite (get_R cwp R' = get_R cwp R). iauto.
    apply (Mask_When_Shiftl (get_R cwp R) (get_R r19 R)); iauto.
    apply IVR.
    }
    {
      asserts_rewrite (get_R g1 R' = get_R g1 R ). iauto.
      asserts_rewrite (get_R cwp R' = get_R cwp R). iauto.
      apply MASK.
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
    exists (R,F) D  (or l4 g1 ᵣ g1).
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
          R'#g1 = R#l4 |ᵢ (R#g1) /\ R'#l1 = R#l1 /\ R'#l2 = R#l2 /\ R'#fp = R#fp /\ F' = F /\ D' = D). {
  inverts P__.
  (* usr_mode *) {
    false. apply (ModeDeq (R,F)); auto.
    apply IVR.
  }
  (* sup_mode *) {
    inverts H10.
    unfolds in H6.
    inverts H6.
    assert (Cs (cursor_Q (R, F)) = Some (or l4 g1 ᵣ g1)) as INS. {
    asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)). iauto.
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

  assert (R'#pc = R_#pc +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) /\ normal_cursor (R',F')) as CSR'. {
    splits. {
      asserts_rewrite (get_R pc R' = get_R npc R). iauto.
      asserts_rewrite (get_R npc R = (get_R pc R) +ᵢ ($ 4)). apply CSR.
      asserts_rewrite (get_R pc R = (get_R pc R_) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($4)). apply CSR.
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

  assert (align_context (R',F')) as ALIGN'. {
    unfolds.
    splits; try unfolds; try unfolds;
    try asserts_rewrite (get_R r17 R' = get_R r17 R);
    try asserts_rewrite (get_R r18 R' = get_R r18 R); 
    try asserts_rewrite (get_R r30 R' = get_R r30 R);
    iauto; try apply ALIGN.
    {
      unfolds in ALIGN.
      unfold get_R.
      remember (right_win 1 (R, F)).
      destruct r as (R1 & F1).
      remember (right_win 1 (R', F')).
      destruct r as (R2 & F2).
      asserts_rewrite(F' = F) in Heqr0. iauto.
      unfold get_R in ALIGN.
      asserts_rewrite (R1 r14 = R2 r14) in ALIGN. {
        apply (right_right_same r14 R R' F R1 R2 F1 F2); iauto.
      } iauto.
    }
  }

  assert (single_mask R'#cwp (R'#wim) /\ single_mask (pre_cwp 1 R')(R'#g1&ᵢ($255))) as MASK'. {
    split.
    {
      asserts_rewrite (get_R cwp R' = get_R cwp R). iauto.
      asserts_rewrite (get_R wim R' = get_R wim R). iauto.
      apply MASK.
    }
    asserts_rewrite (get_R g1 R' = (get_R l4 R) |ᵢ (get_R g1 R)). iauto.
    unfold pre_cwp.
    asserts_rewrite (get_R cwp R' = get_R cwp R). iauto.
     apply Win_Xor; iauto.
     apply IVR.
  }

  assert (D' = []) as DELAY'. {
    asserts_rewrite (D' = D). iauto. iauto.
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
    exists (R,F) D  (save g0 g0 ᵣ g0).
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
  assert (R'#pc = R#npc /\ R'#npc = R#npc +ᵢ ($4) /\ R'#g1 = R#g1 /\
          R'#cwp = (pre_cwp 1 R) /\ R'#annul = R#annul /\ R'#et = R#et /\ R'#trap = R#trap /\ R'#s = R#s /\ R'#wim = R#wim /\
          D' = D /\ (exists Rx,(Rx,F') = right_win 1 (R,F)) /\ word_aligned_R (get_R sp R')). {
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
    asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)). iauto.
    apply FUNC.
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
    simpl. asserts_rewrite (R r1 = R'0 r1). iauto. auto.
    simpl. asserts_rewrite (pre_cwp 1 R = R'0 cwp). {
      symmetry. apply (right_cwp R R'0 F F'); iauto.
    } iauto.
    simpl. asserts_rewrite (R annul = R'0 annul). iauto. auto.
    simpl. asserts_rewrite (R et = R'0 et). iauto. auto.
    simpl. asserts_rewrite (R trap = R'0 trap). iauto. auto.
    simpl. asserts_rewrite (R s = R'0 s). iauto. auto.
    splits; iauto.
    {
    unfolds in ALIGN.
    remember (right_win 1 (R, F)).
    destruct r as (R1 & F1).
    inverts RWIN.
    simpl. apply ALIGN.
    }

    (* trap? no !*){
    inverts H4.
    asserts_rewrite (win_masked (pre_cwp 1 R) R = false) in H0. {
      apply (mask_cwp R); iauto. apply IVR.
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

  assert (R'#pc = R_#pc +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)/\ normal_cursor (R',F')) as CSR'. {
    splits. {
      asserts_rewrite (get_R pc R' = get_R npc R). iauto.
      asserts_rewrite (get_R npc R = (get_R pc R) +ᵢ ($ 4)). apply CSR.
      asserts_rewrite (get_R pc R = (get_R pc R_) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($4)). apply CSR.
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


  assert ((exists Rx : RegFile, (Rx, F') = right_win 1 (R, F)) /\ word_aligned_R (get_R l1 R)
    /\ word_aligned_R (get_R l2 R) /\ word_aligned_R (get_R sp R')) as ALIGN'. {
    unfold align_context in ALIGN.
    splits; iauto.
  }

  assert (single_mask R'#cwp (R'#g1&ᵢ($255))) as MASK'. {
    asserts_rewrite ((get_R cwp R') = pre_cwp 1 R). iauto.
    asserts_rewrite (get_R r1 R' = get_R r1 R). iauto.
    apply MASK.
  }

  assert (D' = []) as DELAY'. {
    asserts_rewrite (D' = D). iauto. iauto.
  }


  assert (f_context F /\ f_context F') as CONT'. {
    splits; iauto.
    assert (exists Rx : RegFile, (Rx, F') = right_win 1 (R, F)). iauto.
    destruct H0 as (Rx & H0).
    apply (hold_context R Rx F F'); iauto. 
  }


  assert (Z__ (Cu, Cs) (Mu, Ms_, (R_, F_),[]) [None;None;None;None;None;None] 6 (Mu, Ms', (R', F'),D')) as GOAL'. {
    apply (No_Event (Cu,Cs) [None;None;None;None;None] 5 (Mu, Ms_, (R_, F_),[]) (Mu, Ms', (R', F'),D') (Mu, Ms, (R, F),D));
    try rewrite DELAY in *; auto.
  }
  clear H P__ IVR MASK CSR DELAY ALIGN GOAL CONT.
  clear Ms D.
  rename R into R_save.
  rename F into F_save.
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
    exists (R,F) D  (wr g0 g1 ᵣ wim).
    splits.
    - substs. auto.
    - asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)); iauto. apply FUNC.
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
          R'#g1 = R#g1 /\ R'#sp = R#sp /\ F' = F /\ D' = [(2%nat, wim, R r1)]). {
  inverts P__.
  (* usr_mode *) {
    false. apply (ModeDeq (R,F)); auto.
    apply IVR.
  }
  (* sup_mode *) {
    inverts H10.
    unfolds in H6.
    inverts H6.
    assert (Cs (cursor_Q (R, F)) = Some (wr g0 g1 ᵣ wim)) as INS. {
    asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)). iauto.
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
    asserts_rewrite (($ 0) xor (R r1) = R r1).
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

  assert (R'#pc = R_#pc +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) /\ normal_cursor (R',F')) as CSR'. {
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

  assert ((exists Rx : RegFile, (Rx, F') = right_win 1 (R_save, F_save)) /\
        word_aligned_R (get_R r17 R_save) /\
        word_aligned_R (get_R r18 R_save) /\ word_aligned_R (get_R r14 R')) as ALIGN'. {
    splits; iauto.
    asserts_rewrite (F' = F). iauto. iauto.
    asserts_rewrite (get_R r14 R' = get_R r14 R). iauto. iauto.
  }

  assert (single_mask R'#cwp (R'#g1&ᵢ($255))) as MASK'. {
    asserts_rewrite (get_R cwp R' = get_R cwp R). iauto.
    asserts_rewrite (get_R r1 R' = get_R r1 R). iauto.
    apply MASK.
  }

  assert (D' = [(2%nat, wim, R' r1)]) as DELAY'. {
    asserts_rewrite (R' r1 = get_R r1 R). iauto.
    iauto.
  }

  assert (f_context F_save /\ f_context F') as CONT'. {
    splits; iauto.
    asserts_rewrite(F' = F). iauto. iauto.
  }

  assert (Z__ (Cu, Cs) (Mu, Ms_, (R_, F_),[]) [None;None;None;None;None;None;None] 7 (Mu, Ms', (R', F'),D')) as GOAL'. {
    apply (No_Event (Cu,Cs) [None;None;None;None;None;None] 6 (Mu, Ms_, (R_, F_),[]) (Mu, Ms', (R', F'),D') (Mu, Ms, (R, F),D));
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


(* step 8 *)

  assert (not_abort Cs Ms (R,F) D) as NA. {
    unfolds.
    exists (R,F) [(1%nat, wim, R r1)] (nop).
    splits.
    - substs. auto.
    - asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)); iauto. apply FUNC.
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
          R'#g1 = R#g1 /\ R'#sp = R#sp /\ F' = F /\ D' = [(1%nat, wim, R r1)]). {
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
    asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4)). iauto.
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

  assert (R'#pc = R_#pc +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) /\ normal_cursor (R',F')) as CSR'. {
    splits. {
      asserts_rewrite (get_R pc R' = get_R npc R). iauto.
      asserts_rewrite (get_R npc R = (get_R pc R) +ᵢ ($ 4)). apply CSR.
      asserts_rewrite (get_R pc R = (get_R pc R_) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)). apply CSR.
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

  assert ((exists Rx : RegFile, (Rx, F') = right_win 1 (R_save, F_save)) /\
        word_aligned_R (get_R r17 R_save) /\
        word_aligned_R (get_R r18 R_save) /\ word_aligned_R (get_R r14 R')) as ALIGN'. {
    splits; iauto.
    asserts_rewrite (F' = F). iauto. iauto.
    asserts_rewrite (get_R r14 R' = get_R r14 R). iauto. iauto.
  }

  assert (single_mask R'#cwp (R'#g1&ᵢ($255))) as MASK'. {
    asserts_rewrite (get_R cwp R' = get_R cwp R). iauto.
    asserts_rewrite (get_R r1 R' = get_R r1 R). iauto.
    apply MASK.
  }

  assert (D' = [(1%nat, wim, R' r1)]) as DELAY'. {
    asserts_rewrite (R' r1 = get_R r1 R). iauto.
    iauto.
  }

  assert (f_context F_save /\ f_context F') as CONT'. {
    splits; iauto.
    asserts_rewrite(F' = F). iauto. iauto.
  }

  assert (Z__ (Cu, Cs) (Mu, Ms_, (R_, F_),[]) [None;None;None;None;None;None;None;None] 8 (Mu, Ms', (R', F'),D')) as GOAL'. {
    apply (No_Event (Cu,Cs) [None;None;None;None;None;None;None] 7 (Mu, Ms_, (R_, F_),[]) (Mu, Ms', (R', F'),D') (Mu, Ms, (R, F),D));
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




(* step 9 *)

  assert (not_abort Cs Ms (R,F) D) as NA. {
    unfolds.
    exists (R,F) [(0%nat, wim, R r1)] (nop).
    splits.
    - substs. auto.
    - asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)); iauto. apply FUNC.
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
          R'#g1 = R#g1 /\ R'#sp = R#sp /\ F' = F /\ D' = [(0%nat, wim, R r1)]). {
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
    asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4)). iauto.
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

  assert (R'#pc = R_#pc +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) /\ normal_cursor (R',F')) as CSR'. {
    splits. {
      asserts_rewrite (get_R pc R' = get_R npc R). iauto.
      asserts_rewrite (get_R npc R = (get_R pc R) +ᵢ ($ 4)). apply CSR.
      asserts_rewrite (get_R pc R = (get_R pc R_) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)). apply CSR.
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

  assert ((exists Rx : RegFile, (Rx, F') = right_win 1 (R_save, F_save)) /\
        word_aligned_R (get_R r17 R_save) /\
        word_aligned_R (get_R r18 R_save) /\ word_aligned_R (get_R r14 R')) as ALIGN'. {
    splits; iauto.
    asserts_rewrite (F' = F). iauto. iauto.
    asserts_rewrite (get_R r14 R' = get_R r14 R). iauto. iauto.
  }

  assert (single_mask R'#cwp (R'#g1&ᵢ($255))) as MASK'. {
    asserts_rewrite (get_R cwp R' = get_R cwp R). iauto.
    asserts_rewrite (get_R r1 R' = get_R r1 R). iauto.
    apply MASK.
  }

  assert (D' = [(0%nat, wim, R' r1)]) as DELAY'. {
    asserts_rewrite (R' r1 = get_R r1 R). iauto.
    iauto.
  }

  assert (f_context F_save /\ f_context F') as CONT'. {
    splits; iauto.
    asserts_rewrite(F' = F). iauto. iauto.
  }

  assert (Z__ (Cu, Cs) (Mu, Ms_, (R_, F_),[]) [None;None;None;None;None;None;None;None;None] 9 (Mu, Ms', (R', F'),D')) as GOAL'. {
    apply (No_Event (Cu,Cs) [None;None;None;None;None;None;None;None] 8 (Mu, Ms_, (R_, F_),[]) (Mu, Ms', (R', F'),D') (Mu, Ms, (R, F),D));
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



(* step 10 *)

  assert (not_abort Cs Ms (R,F) D) as NA. {
    unfolds.
    remember (exe_delay (R, F) D).
    destruct p.
    exists r d (nop).
    splits.
    - substs. auto.
    - rewrite DELAY in Heqp. unfold exe_delay in Heqp.
      remember (R # wim <- (R r1)).
      inverts Heqp.
      rewrite Heqr0.
      asserts_rewrite (cursor_Q (R # wim <- (R r1), F) = cursor_Q (R, F)). iauto.
      asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)); iauto. apply FUNC.
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
          R'#cwp = R#cwp /\ R'#annul = R#annul /\ R'#et = R#et /\ R'#trap = R#trap /\ R'#s = R#s /\ R'#wim = (R#g1)&ᵢ ($ 255) /\
          R'#g1 = R#g1 /\ R'#sp = R#sp /\ F' = F /\ D' = []). {
  inverts P__.
  (* usr_mode *) {
    false. apply (ModeDeq (R,F)); auto.
    apply IVR.
  }
  (* sup_mode *) {
    inverts H10.
    unfolds in H6.
    remember (R # wim <- (R r1)).
    inverts H6.
    assert (Cs (cursor_Q (R, F)) = Some (nop)) as INS. {
    asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4) ). iauto.
    apply FUNC.
    }
    rewrite Heqr in H11.
    asserts_rewrite (cursor_Q (R # wim <- (R r1), F) = cursor_Q (R, F)) in H11. iauto.
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

  assert (R'#pc = R_#pc +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) /\ normal_cursor (R',F')) as CSR'. {
    splits. {
      asserts_rewrite (get_R pc R' = get_R npc R). iauto.
      asserts_rewrite (get_R npc R = (get_R pc R) +ᵢ ($ 4)). apply CSR.
      asserts_rewrite (get_R pc R = (get_R pc R_) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)). apply CSR.
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

  assert ((exists Rx : RegFile, (Rx, F') = right_win 1 (R_save, F_save)) /\
        word_aligned_R (get_R r17 R_save) /\
        word_aligned_R (get_R r18 R_save) /\ word_aligned_R (get_R r14 R')) as ALIGN'. {
    splits; iauto.
    asserts_rewrite (F' = F). iauto. iauto.
    asserts_rewrite (get_R r14 R' = get_R r14 R). iauto. iauto.
  }

  assert (single_mask R'#cwp R'#wim) as MASK'. {
    asserts_rewrite (get_R cwp R' = get_R cwp R). iauto.
    asserts_rewrite (get_R wim R' = (get_R r1 R) &ᵢ ($ 255)). iauto.
    apply MASK.
  }

  assert (D' = []) as DELAY'. {
    iauto.
  }

  assert (f_context F_save /\ f_context F') as CONT'. {
    splits; iauto.
    asserts_rewrite(F' = F). iauto. iauto.
  }

  assert (Z__ (Cu, Cs) (Mu, Ms_, (R_, F_),[]) [None;None;None;None;None;None;None;None;None;None] 10 (Mu, Ms', (R', F'),D')) as GOAL'. {
    apply (No_Event (Cu,Cs) [None;None;None;None;None;None;None;None;None] 9 (Mu, Ms_, (R_, F_),[]) (Mu, Ms', (R', F'),D') (Mu, Ms, (R, F),D));
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





(* step 11 *)

   assert (not_abort Cs Ms (R,F) D) as NA. {
    unfolds.
    exists (R,F) D  (st l0 sp ₐᵣ).
    splits.
    - substs. auto.
    - asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)); iauto. apply FUNC.
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
          R'#sp = R#sp /\ F' = F /\ D' = []). {
  inverts P__.
  (* usr_mode *) {
    false. apply (ModeDeq (R,F)); auto.
    apply IVR.
  }
  (* sup_mode *) {
    inverts H10.
    unfolds in H6.
    inverts H6.
    assert (Cs (cursor_Q (R, F)) = Some (st l0 sp ₐᵣ)) as INS. {
    asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4)). iauto.
    apply FUNC.
    }
    rewrite H11 in INS.
    clear H11. inverts INS.

    {
    inverts H12; try solve [false].
    inverts H5; try solve [false].
    repeat (split; auto); auto.
    unfold unexpected_trap in *.
    unfold trap_type in *.
    unfold eval_AddrExp in *.
    unfold eval_OpExp in *.
    asserts_rewrite (word_aligned (get_R r14 R) = true) in H4. iauto.
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

  assert ((exists Rx : RegFile, (Rx, F') = right_win 1 (R_save, F_save)) /\
        word_aligned_R (get_R r17 R_save) /\
        word_aligned_R (get_R r18 R_save) /\ word_aligned_R (get_R r14 R')) as ALIGN'. {
    splits; iauto.
    asserts_rewrite (F' = F). iauto. iauto.
    asserts_rewrite (get_R r14 R' = get_R r14 R). iauto. iauto.
  }

  assert (single_mask R'#cwp R'#wim) as MASK'. {
    asserts_rewrite (get_R cwp R' = get_R cwp R). iauto.
    asserts_rewrite (get_R wim R' = get_R wim R). iauto.
    apply MASK.
  }

  assert (D' = []) as DELAY'. {
    iauto.
  }

  assert (f_context F_save /\ f_context F') as CONT'. {
    splits; iauto.
    asserts_rewrite(F' = F). iauto. iauto.
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
    exists (R,F) D  (st l1 sp+ₐₙ($4)).
    splits.
    - substs. auto.
    - asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4)  +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)); iauto. apply FUNC.
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

  (* align *)
  assert (word_aligned_R (get_R r14 R)+ᵢ ($4)) as TMP. {
        apply align_plus4. iauto.
  }


  (* small changes in one step *)
  assert (R'#pc = R#npc /\ R'#npc = R#npc +ᵢ ($4) /\
          R'#cwp = R#cwp /\ R'#annul = R#annul /\ R'#et = R#et /\ R'#trap = R#trap /\ R'#s = R#s /\ R'#wim = R#wim /\
          R'#sp = R#sp /\ F' = F /\ D' = []). {
  inverts P__.
  (* usr_mode *) {
    false. apply (ModeDeq (R,F)); auto.
    apply IVR.
  }
  (* sup_mode *) {
    inverts H10.
    unfolds in H6.
    inverts H6.
    assert (Cs (cursor_Q (R, F)) = Some (st l1 sp+ₐₙ($4))) as INS. {
    asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4)). iauto.
    apply FUNC.
    }
    rewrite H11 in INS.
    clear H11. inverts INS.

    {
    inverts H12; try solve [false].
    inverts H5; try solve [false].
    repeat (split; auto); auto.
    unfold unexpected_trap in *.
    unfold trap_type in *.
    unfold eval_AddrExp in *.
    unfold eval_OpExp in *.
    asserts_rewrite(($ (-4096)) <=ᵢ ($ 4) && ($ 4) <=ᵢ ($ 4095) = true) in H4. {
       clear CSR H4.
       unfolds.
       asserts_rewrite (($ (-4096)) <=ᵢ ($ 4) = true). unfolds.
       asserts_rewrite (($ 4) >ᵢ ($ (-4096)) = true). mauto. auto. mauto. 
    }
    asserts_rewrite (word_aligned (get_R r14 R) +ᵢ ($ 4) = true) in H4. iauto.
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

  assert (R'#pc = R_#pc +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) /\ normal_cursor (R',F')) as CSR'. {
    splits. {
      asserts_rewrite (get_R pc R' = get_R npc R). iauto.
      asserts_rewrite (get_R npc R = (get_R pc R) +ᵢ ($ 4)). apply CSR.
      asserts_rewrite (get_R pc R = (get_R pc R_) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)). apply CSR.
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

  assert ((exists Rx : RegFile, (Rx, F') = right_win 1 (R_save, F_save)) /\
        word_aligned_R (get_R r17 R_save) /\
        word_aligned_R (get_R r18 R_save) /\ word_aligned_R (get_R r14 R') +ᵢ ($ 4)) as ALIGN'. {
    splits; iauto.
    asserts_rewrite (F' = F). iauto. iauto.
    asserts_rewrite (get_R r14 R' = get_R r14 R). iauto. iauto.
  }

  assert (single_mask R'#cwp R'#wim) as MASK'. {
    asserts_rewrite (get_R cwp R' = get_R cwp R). iauto.
    asserts_rewrite (get_R wim R' = get_R wim R). iauto.
    apply MASK.
  }

  assert (D' = []) as DELAY'. {
    iauto.
  }

  assert (f_context F_save /\ f_context F') as CONT'. {
    splits; iauto.
    asserts_rewrite(F' = F). iauto. iauto.
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
    exists (R,F) D  (st l2 sp+ₐₙ($8)).
    splits.
    - substs. auto.
    - asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4)  +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)); iauto. apply FUNC.
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
          R'#sp = R#sp /\ F' = F /\ D' = []). {
  inverts P__.
  (* usr_mode *) {
    false. apply (ModeDeq (R,F)); auto.
    apply IVR.
  }
  (* sup_mode *) {
    inverts H10.
    unfolds in H6.
    inverts H6.
    assert (Cs (cursor_Q (R, F)) = Some (st l2 sp+ₐₙ($8))) as INS. {
    asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4)). iauto.
    apply FUNC.
    }
    rewrite H11 in INS.
    clear H11. inverts INS.

    {
    inverts H12; try solve [false].
    inverts H5; try solve [false].
    repeat (split; auto); auto.
    unfold unexpected_trap in *.
    unfold trap_type in *.
    unfold eval_AddrExp in *.
    unfold eval_OpExp in *.
    asserts_rewrite(($ (-4096)) <=ᵢ ($ 8) && ($ 8) <=ᵢ ($ 4095) = true) in H4. {
       clear CSR H4.
       unfolds.
       asserts_rewrite (($ (-4096)) <=ᵢ ($ 8) = true). unfolds.
       asserts_rewrite (($ 8) >ᵢ ($ (-4096)) = true). mauto. auto. mauto. 
    }
    asserts_rewrite (word_aligned (get_R r14 R) +ᵢ ($ 8) = true) in H4. iauto.
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

  assert (R'#pc = R_#pc +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) /\ normal_cursor (R',F')) as CSR'. {
    splits. {
      asserts_rewrite (get_R pc R' = get_R npc R). iauto.
      asserts_rewrite (get_R npc R = (get_R pc R) +ᵢ ($ 4)). apply CSR.
      asserts_rewrite (get_R pc R = (get_R pc R_) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($4)+ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)). apply CSR.
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

  assert ((exists Rx : RegFile, (Rx, F') = right_win 1 (R_save, F_save)) /\
        word_aligned_R (get_R r17 R_save) /\
        word_aligned_R (get_R r18 R_save) /\ word_aligned_R (get_R r14 R') +ᵢ ($ 8)) as ALIGN'. {
    splits; iauto.
    asserts_rewrite (F' = F). iauto. iauto.
    asserts_rewrite (get_R r14 R' = get_R r14 R). iauto. iauto.
  }

  assert (single_mask R'#cwp R'#wim) as MASK'. {
    asserts_rewrite (get_R cwp R' = get_R cwp R). iauto.
    asserts_rewrite (get_R wim R' = get_R wim R). iauto.
    apply MASK.
  }

  assert (D' = []) as DELAY'. {
    iauto.
  }

  assert (f_context F_save /\ f_context F') as CONT'. {
    splits; iauto.
    asserts_rewrite(F' = F). iauto. iauto.
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
    exists (R,F) D  (st l3 sp+ₐₙ($12)).
    splits.
    - substs. auto.
    - asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)); iauto. apply FUNC.
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
          R'#sp = R#sp /\ F' = F /\ D' = []). {
  inverts P__.
  (* usr_mode *) {
    false. apply (ModeDeq (R,F)); auto.
    apply IVR.
  }
  (* sup_mode *) {
    inverts H10.
    unfolds in H6.
    inverts H6.
    assert (Cs (cursor_Q (R, F)) = Some (st l3 sp+ₐₙ($12))) as INS. {
    asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4)). iauto.
    apply FUNC.
    }
    rewrite H11 in INS.
    clear H11. inverts INS.

    {
    inverts H12; try solve [false].
    inverts H5; try solve [false].
    repeat (split; auto); auto.
    unfold unexpected_trap in *.
    unfold trap_type in *.
    unfold eval_AddrExp in *.
    unfold eval_OpExp in *.
    asserts_rewrite(($ (-4096)) <=ᵢ ($ 12) && ($ 12) <=ᵢ ($ 4095) = true) in H4. {
       clear CSR H4.
       unfolds.
       asserts_rewrite (($ (-4096)) <=ᵢ ($ 12) = true). unfolds.
       asserts_rewrite (($ 12) >ᵢ ($ (-4096)) = true). mauto. auto. mauto. 
    }
    asserts_rewrite (word_aligned (get_R r14 R) +ᵢ ($ 12) = true) in H4. iauto.
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

  assert (R'#pc = R_#pc +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) /\ normal_cursor (R',F')) as CSR'. {
    splits. {
      asserts_rewrite (get_R pc R' = get_R npc R). iauto.
      asserts_rewrite (get_R npc R = (get_R pc R) +ᵢ ($ 4)). apply CSR.
      asserts_rewrite (get_R pc R = (get_R pc R_) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($4)+ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)). apply CSR.
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

  assert ((exists Rx : RegFile, (Rx, F') = right_win 1 (R_save, F_save)) /\
        word_aligned_R (get_R r17 R_save) /\
        word_aligned_R (get_R r18 R_save) /\ word_aligned_R (get_R r14 R') +ᵢ ($ 12)) as ALIGN'. {
    splits; iauto.
    asserts_rewrite (F' = F). iauto. iauto.
    asserts_rewrite (get_R r14 R' = get_R r14 R). iauto. iauto.
  }

  assert (single_mask R'#cwp R'#wim) as MASK'. {
    asserts_rewrite (get_R cwp R' = get_R cwp R). iauto.
    asserts_rewrite (get_R wim R' = get_R wim R). iauto.
    apply MASK.
  }

  assert (D' = []) as DELAY'. {
    iauto.
  }

  assert (f_context F_save /\ f_context F') as CONT'. {
    splits; iauto.
    asserts_rewrite(F' = F). iauto. iauto.
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
    exists (R,F) D  (st l4 sp+ₐₙ($16)).
    splits.
    - substs. auto.
    - asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)); iauto. apply FUNC.
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
          R'#sp = R#sp /\ F' = F /\ D' = []). {
  inverts P__.
  (* usr_mode *) {
    false. apply (ModeDeq (R,F)); auto.
    apply IVR.
  }
  (* sup_mode *) {
    inverts H10.
    unfolds in H6.
    inverts H6.
    assert (Cs (cursor_Q (R, F)) = Some (st l4 sp+ₐₙ($16))) as INS. {
    asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4)). iauto.
    apply FUNC.
    }
    rewrite H11 in INS.
    clear H11. inverts INS.

    {
    inverts H12; try solve [false].
    inverts H5; try solve [false].
    repeat (split; auto); auto.
    unfold unexpected_trap in *.
    unfold trap_type in *.
    unfold eval_AddrExp in *.
    unfold eval_OpExp in *.
    asserts_rewrite(($ (-4096)) <=ᵢ ($ 16) && ($ 16) <=ᵢ ($ 4095) = true) in H4. {
       clear CSR H4.
       unfolds.
       asserts_rewrite (($ (-4096)) <=ᵢ ($ 16) = true). unfolds.
       asserts_rewrite (($ 16) >ᵢ ($ (-4096)) = true). mauto. auto. mauto. 
    }
    asserts_rewrite (word_aligned (get_R r14 R) +ᵢ ($ 16) = true) in H4. iauto.
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

  assert (R'#pc = R_#pc +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)+ᵢ ($4)  +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) /\ normal_cursor (R',F')) as CSR'. {
    splits. {
      asserts_rewrite (get_R pc R' = get_R npc R). iauto.
      asserts_rewrite (get_R npc R = (get_R pc R) +ᵢ ($ 4)). apply CSR.
      asserts_rewrite (get_R pc R = (get_R pc R_) +ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($4)+ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)). apply CSR.
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

  assert ((exists Rx : RegFile, (Rx, F') = right_win 1 (R_save, F_save)) /\
        word_aligned_R (get_R r17 R_save) /\
        word_aligned_R (get_R r18 R_save) /\ word_aligned_R (get_R r14 R') +ᵢ ($ 16)) as ALIGN'. {
    splits; iauto.
    asserts_rewrite (F' = F). iauto. iauto.
    asserts_rewrite (get_R r14 R' = get_R r14 R). iauto. iauto.
  }

  assert (single_mask R'#cwp R'#wim) as MASK'. {
    asserts_rewrite (get_R cwp R' = get_R cwp R). iauto.
    asserts_rewrite (get_R wim R' = get_R wim R). iauto.
    apply MASK.
  }

  assert (D' = []) as DELAY'. {
    iauto.
  }

  assert (f_context F_save /\ f_context F') as CONT'. {
    splits; iauto.
    asserts_rewrite(F' = F). iauto. iauto.
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
    exists (R,F) D  (st l5 sp+ₐₙ($20)).
    splits.
    - substs. auto.
    - asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)); iauto. apply FUNC.
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
          R'#sp = R#sp /\ F' = F /\ D' = []). {
  inverts P__.
  (* usr_mode *) {
    false. apply (ModeDeq (R,F)); auto.
    apply IVR.
  }
  (* sup_mode *) {
    inverts H10.
    unfolds in H6.
    inverts H6.
    assert (Cs (cursor_Q (R, F)) = Some (st l5 sp+ₐₙ($20))) as INS. {
    asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4)). iauto.
    apply FUNC.
    }
    rewrite H11 in INS.
    clear H11. inverts INS.

    {
    inverts H12; try solve [false].
    inverts H5; try solve [false].
    repeat (split; auto); auto.
    unfold unexpected_trap in *.
    unfold trap_type in *.
    unfold eval_AddrExp in *.
    unfold eval_OpExp in *.
    asserts_rewrite(($ (-4096)) <=ᵢ ($ 20) && ($ 20) <=ᵢ ($ 4095) = true) in H4. {
       clear CSR H4.
       unfolds.
       asserts_rewrite (($ (-4096)) <=ᵢ ($ 20) = true). unfolds.
       asserts_rewrite (($ 20) >ᵢ ($ (-4096)) = true). mauto. auto. mauto. 
    }
    asserts_rewrite (word_aligned (get_R r14 R) +ᵢ ($ 20) = true) in H4. iauto.
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

  assert (R'#pc = R_#pc +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)+ᵢ ($4)  +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) /\ normal_cursor (R',F')) as CSR'. {
    splits. {
      asserts_rewrite (get_R pc R' = get_R npc R). iauto.
      asserts_rewrite (get_R npc R = (get_R pc R) +ᵢ ($ 4)). apply CSR.
      asserts_rewrite (get_R pc R = (get_R pc R_) +ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($4)+ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)). apply CSR.
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

  assert ((exists Rx : RegFile, (Rx, F') = right_win 1 (R_save, F_save)) /\
        word_aligned_R (get_R r17 R_save) /\
        word_aligned_R (get_R r18 R_save) /\ word_aligned_R (get_R r14 R') +ᵢ ($ 20)) as ALIGN'. {
    splits; iauto.
    asserts_rewrite (F' = F). iauto. iauto.
    asserts_rewrite (get_R r14 R' = get_R r14 R). iauto. iauto.
  }

  assert (single_mask R'#cwp R'#wim) as MASK'. {
    asserts_rewrite (get_R cwp R' = get_R cwp R). iauto.
    asserts_rewrite (get_R wim R' = get_R wim R). iauto.
    apply MASK.
  }

  assert (D' = []) as DELAY'. {
    iauto.
  }

  assert (f_context F_save /\ f_context F') as CONT'. {
    splits; iauto.
    asserts_rewrite(F' = F). iauto. iauto.
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
    exists (R,F) D  (st l6 sp+ₐₙ($24)).
    splits.
    - substs. auto.
    - asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)); iauto. apply FUNC.
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
          R'#sp = R#sp /\ F' = F /\ D' = []). {
  inverts P__.
  (* usr_mode *) {
    false. apply (ModeDeq (R,F)); auto.
    apply IVR.
  }
  (* sup_mode *) {
    inverts H10.
    unfolds in H6.
    inverts H6.
    assert (Cs (cursor_Q (R, F)) = Some (st l6 sp+ₐₙ($24))) as INS. {
    asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ  ($ 4)+ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4)). iauto.
    apply FUNC.
    }
    rewrite H11 in INS.
    clear H11. inverts INS.

    {
    inverts H12; try solve [false].
    inverts H5; try solve [false].
    repeat (split; auto); auto.
    unfold unexpected_trap in *.
    unfold trap_type in *.
    unfold eval_AddrExp in *.
    unfold eval_OpExp in *.
    asserts_rewrite(($ (-4096)) <=ᵢ ($ 24) && ($ 24) <=ᵢ ($ 4095) = true) in H4. {
       clear CSR H4.
       unfolds.
       asserts_rewrite (($ (-4096)) <=ᵢ ($ 24) = true). unfolds.
       asserts_rewrite (($ 24) >ᵢ ($ (-4096)) = true). mauto. auto. mauto. 
    }
    asserts_rewrite (word_aligned (get_R r14 R) +ᵢ ($ 24) = true) in H4. iauto.
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

  assert (R'#pc = R_#pc +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)+ᵢ ($4)  +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) /\ normal_cursor (R',F')) as CSR'. {
    splits. {
      asserts_rewrite (get_R pc R' = get_R npc R). iauto.
      asserts_rewrite (get_R npc R = (get_R pc R) +ᵢ ($ 4)). apply CSR.
      asserts_rewrite (get_R pc R = (get_R pc R_) +ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)+ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)). apply CSR.
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

  assert ((exists Rx : RegFile, (Rx, F') = right_win 1 (R_save, F_save)) /\
        word_aligned_R (get_R r17 R_save) /\
        word_aligned_R (get_R r18 R_save) /\ word_aligned_R (get_R r14 R') +ᵢ ($ 24)) as ALIGN'. {
    splits; iauto.
    asserts_rewrite (F' = F). iauto. iauto.
    asserts_rewrite (get_R r14 R' = get_R r14 R). iauto. iauto.
  }

  assert (single_mask R'#cwp R'#wim) as MASK'. {
    asserts_rewrite (get_R cwp R' = get_R cwp R). iauto.
    asserts_rewrite (get_R wim R' = get_R wim R). iauto.
    apply MASK.
  }

  assert (D' = []) as DELAY'. {
    iauto.
  }

  assert (f_context F_save /\ f_context F') as CONT'. {
    splits; iauto.
    asserts_rewrite(F' = F). iauto. iauto.
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
    exists (R,F) D  (st l7 sp+ₐₙ($28)).
    splits.
    - substs. auto.
    - asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)); iauto. apply FUNC.
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
          R'#sp = R#sp /\ F' = F /\ D' = []). {
  inverts P__.
  (* usr_mode *) {
    false. apply (ModeDeq (R,F)); auto.
    apply IVR.
  }
  (* sup_mode *) {
    inverts H10.
    unfolds in H6.
    inverts H6.
    assert (Cs (cursor_Q (R, F)) = Some (st l7 sp+ₐₙ($28))) as INS. {
    asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ  ($ 4)+ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4)). iauto.
    apply FUNC.
    }
    rewrite H11 in INS.
    clear H11. inverts INS.

    {
    inverts H12; try solve [false].
    inverts H5; try solve [false].
    repeat (split; auto); auto.
    unfold unexpected_trap in *.
    unfold trap_type in *.
    unfold eval_AddrExp in *.
    unfold eval_OpExp in *.
    asserts_rewrite(($ (-4096)) <=ᵢ ($ 28) && ($ 28) <=ᵢ ($ 4095) = true) in H4. {
       clear CSR H4.
       unfolds.
       asserts_rewrite (($ (-4096)) <=ᵢ ($ 28) = true). unfolds.
       asserts_rewrite (($ 28) >ᵢ ($ (-4096)) = true). mauto. auto. mauto. 
    }
    asserts_rewrite (word_aligned (get_R r14 R) +ᵢ ($ 28) = true) in H4. iauto.
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

  assert (R'#pc = R_#pc +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)+ᵢ ($4)  +ᵢ ($ 4)+ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) /\ normal_cursor (R',F')) as CSR'. {
    splits. {
      asserts_rewrite (get_R pc R' = get_R npc R). iauto.
      asserts_rewrite (get_R npc R = (get_R pc R) +ᵢ ($ 4)). apply CSR.
      asserts_rewrite (get_R pc R = (get_R pc R_) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)+ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)). apply CSR.
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

  assert ((exists Rx : RegFile, (Rx, F') = right_win 1 (R_save, F_save)) /\
        word_aligned_R (get_R r17 R_save) /\
        word_aligned_R (get_R r18 R_save) /\ word_aligned_R (get_R r14 R') +ᵢ ($ 28)) as ALIGN'. {
    splits; iauto.
    asserts_rewrite (F' = F). iauto. iauto.
    asserts_rewrite (get_R r14 R' = get_R r14 R). iauto. iauto.
  }

  assert (single_mask R'#cwp R'#wim) as MASK'. {
    asserts_rewrite (get_R cwp R' = get_R cwp R). iauto.
    asserts_rewrite (get_R wim R' = get_R wim R). iauto.
    apply MASK.
  }

  assert (D' = []) as DELAY'. {
    iauto.
  }

  assert (f_context F_save /\ f_context F') as CONT'. {
    splits; iauto.
    asserts_rewrite(F' = F). iauto. iauto.
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
    exists (R,F) D  (st i0 sp+ₐₙ($32)).
    splits.
    - substs. auto.
    - asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)); iauto. apply FUNC.
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
          R'#sp = R#sp /\ F' = F /\ D' = []). {
  inverts P__.
  (* usr_mode *) {
    false. apply (ModeDeq (R,F)); auto.
    apply IVR.
  }
  (* sup_mode *) {
    inverts H10.
    unfolds in H6.
    inverts H6.
    assert (Cs (cursor_Q (R, F)) = Some (st i0 sp+ₐₙ($32))) as INS. {
    asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ  ($ 4)+ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4)). iauto.
    apply FUNC.
    }
    rewrite H11 in INS.
    clear H11. inverts INS.

    {
    inverts H12; try solve [false].
    inverts H5; try solve [false].
    repeat (split; auto); auto.
    unfold unexpected_trap in *.
    unfold trap_type in *.
    unfold eval_AddrExp in *.
    unfold eval_OpExp in *.
    asserts_rewrite(($ (-4096)) <=ᵢ ($ 32) && ($ 32) <=ᵢ ($ 4095) = true) in H4. {
       clear CSR H4.
       unfolds.
       asserts_rewrite (($ (-4096)) <=ᵢ ($ 32) = true). unfolds.
       asserts_rewrite (($ 32) >ᵢ ($ (-4096)) = true). mauto. auto. mauto. 
    }
    asserts_rewrite (word_aligned (get_R r14 R) +ᵢ ($ 32) = true) in H4. iauto.
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

  assert (R'#pc = R_#pc +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)+ᵢ ($4)  +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) /\ normal_cursor (R',F')) as CSR'. {
    splits. {
      asserts_rewrite (get_R pc R' = get_R npc R). iauto.
      asserts_rewrite (get_R npc R = (get_R pc R) +ᵢ ($ 4)). apply CSR.
      asserts_rewrite (get_R pc R = (get_R pc R_) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)+ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)). apply CSR.
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

  assert ((exists Rx : RegFile, (Rx, F') = right_win 1 (R_save, F_save)) /\
        word_aligned_R (get_R r17 R_save) /\
        word_aligned_R (get_R r18 R_save) /\ word_aligned_R (get_R r14 R') +ᵢ ($ 32)) as ALIGN'. {
    splits; iauto.
    asserts_rewrite (F' = F). iauto. iauto.
    asserts_rewrite (get_R r14 R' = get_R r14 R). iauto. iauto.
  }

  assert (single_mask R'#cwp R'#wim) as MASK'. {
    asserts_rewrite (get_R cwp R' = get_R cwp R). iauto.
    asserts_rewrite (get_R wim R' = get_R wim R). iauto.
    apply MASK.
  }

  assert (D' = []) as DELAY'. {
    iauto.
  }

  assert (f_context F_save /\ f_context F') as CONT'. {
    splits; iauto.
    asserts_rewrite(F' = F). iauto. iauto.
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
    exists (R,F) D  (st i1 sp+ₐₙ($36)).
    splits.
    - substs. auto.
    - asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)); iauto. apply FUNC.
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
          R'#sp = R#sp /\ F' = F /\ D' = []). {
  inverts P__.
  (* usr_mode *) {
    false. apply (ModeDeq (R,F)); auto.
    apply IVR.
  }
  (* sup_mode *) {
    inverts H10.
    unfolds in H6.
    inverts H6.
    assert (Cs (cursor_Q (R, F)) = Some (st i1 sp+ₐₙ($36))) as INS. {
    asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ  ($ 4)+ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4)). iauto.
    apply FUNC.
    }
    rewrite H11 in INS.
    clear H11. inverts INS.

    {
    inverts H12; try solve [false].
    inverts H5; try solve [false].
    repeat (split; auto); auto.
    unfold unexpected_trap in *.
    unfold trap_type in *.
    unfold eval_AddrExp in *.
    unfold eval_OpExp in *.
    asserts_rewrite(($ (-4096)) <=ᵢ ($ 36) && ($ 36) <=ᵢ ($ 4095) = true) in H4. {
       clear CSR H4.
       unfolds.
       asserts_rewrite (($ (-4096)) <=ᵢ ($ 36) = true). unfolds.
       asserts_rewrite (($ 36) >ᵢ ($ (-4096)) = true). mauto. auto. mauto. 
    }
    asserts_rewrite (word_aligned (get_R r14 R) +ᵢ ($ 36) = true) in H4. iauto.
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

  assert (R'#pc = R_#pc +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)+ᵢ ($4)  +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) /\ normal_cursor (R',F')) as CSR'. {
    splits. {
      asserts_rewrite (get_R pc R' = get_R npc R). iauto.
      asserts_rewrite (get_R npc R = (get_R pc R) +ᵢ ($ 4)). apply CSR.
      asserts_rewrite (get_R pc R = (get_R pc R_) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)+ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)). apply CSR.
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

  assert ((exists Rx : RegFile, (Rx, F') = right_win 1 (R_save, F_save)) /\
        word_aligned_R (get_R r17 R_save) /\
        word_aligned_R (get_R r18 R_save) /\ word_aligned_R (get_R r14 R') +ᵢ ($ 36)) as ALIGN'. {
    splits; iauto.
    asserts_rewrite (F' = F). iauto. iauto.
    asserts_rewrite (get_R r14 R' = get_R r14 R). iauto. iauto.
  }

  assert (single_mask R'#cwp R'#wim) as MASK'. {
    asserts_rewrite (get_R cwp R' = get_R cwp R). iauto.
    asserts_rewrite (get_R wim R' = get_R wim R). iauto.
    apply MASK.
  }

  assert (D' = []) as DELAY'. {
    iauto.
  }

  assert (f_context F_save /\ f_context F') as CONT'. {
    splits; iauto.
    asserts_rewrite(F' = F). iauto. iauto.
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
    exists (R,F) D  (st i2 sp+ₐₙ($40)).
    splits.
    - substs. auto.
    - asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)); iauto. apply FUNC.
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
          R'#sp = R#sp /\ F' = F /\ D' = []). {
  inverts P__.
  (* usr_mode *) {
    false. apply (ModeDeq (R,F)); auto.
    apply IVR.
  }
  (* sup_mode *) {
    inverts H10.
    unfolds in H6.
    inverts H6.
    assert (Cs (cursor_Q (R, F)) = Some (st i2 sp+ₐₙ($40))) as INS. {
    asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ  ($ 4)+ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4)). iauto.
    apply FUNC.
    }
    rewrite H11 in INS.
    clear H11. inverts INS.

    {
    inverts H12; try solve [false].
    inverts H5; try solve [false].
    repeat (split; auto); auto.
    unfold unexpected_trap in *.
    unfold trap_type in *.
    unfold eval_AddrExp in *.
    unfold eval_OpExp in *.
    asserts_rewrite(($ (-4096)) <=ᵢ ($ 40) && ($ 40) <=ᵢ ($ 4095) = true) in H4. {
       clear CSR H4.
       unfolds.
       asserts_rewrite (($ (-4096)) <=ᵢ ($ 40) = true). unfolds.
       asserts_rewrite (($ 40) >ᵢ ($ (-4096)) = true). mauto. auto. mauto. 
    }
    asserts_rewrite (word_aligned (get_R r14 R) +ᵢ ($ 40) = true) in H4. iauto.
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

  assert (R'#pc = R_#pc +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)+ᵢ ($4)+ᵢ ($ 4)  +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) /\ normal_cursor (R',F')) as CSR'. {
    splits. {
      asserts_rewrite (get_R pc R' = get_R npc R). iauto.
      asserts_rewrite (get_R npc R = (get_R pc R) +ᵢ ($ 4)). apply CSR.
      asserts_rewrite (get_R pc R = (get_R pc R_) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)+ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)). apply CSR.
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

  assert ((exists Rx : RegFile, (Rx, F') = right_win 1 (R_save, F_save)) /\
        word_aligned_R (get_R r17 R_save) /\
        word_aligned_R (get_R r18 R_save) /\ word_aligned_R (get_R r14 R') +ᵢ ($ 40)) as ALIGN'. {
    splits; iauto.
    asserts_rewrite (F' = F). iauto. iauto.
    asserts_rewrite (get_R r14 R' = get_R r14 R). iauto. iauto.
  }

  assert (single_mask R'#cwp R'#wim) as MASK'. {
    asserts_rewrite (get_R cwp R' = get_R cwp R). iauto.
    asserts_rewrite (get_R wim R' = get_R wim R). iauto.
    apply MASK.
  }

  assert (D' = []) as DELAY'. {
    iauto.
  }

  assert (f_context F_save /\ f_context F') as CONT'. {
    splits; iauto.
    asserts_rewrite(F' = F). iauto. iauto.
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
    exists (R,F) D  (st i3 sp+ₐₙ($44)).
    splits.
    - substs. auto.
    - asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)); iauto. apply FUNC.
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
          R'#sp = R#sp /\ F' = F /\ D' = []). {
  inverts P__.
  (* usr_mode *) {
    false. apply (ModeDeq (R,F)); auto.
    apply IVR.
  }
  (* sup_mode *) {
    inverts H10.
    unfolds in H6.
    inverts H6.
    assert (Cs (cursor_Q (R, F)) = Some (st i3 sp+ₐₙ($44))) as INS. {
    asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ  ($ 4)+ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4)). iauto.
    apply FUNC.
    }
    rewrite H11 in INS.
    clear H11. inverts INS.

    {
    inverts H12; try solve [false].
    inverts H5; try solve [false].
    repeat (split; auto); auto.
    unfold unexpected_trap in *.
    unfold trap_type in *.
    unfold eval_AddrExp in *.
    unfold eval_OpExp in *.
    asserts_rewrite(($ (-4096)) <=ᵢ ($ 44) && ($ 44) <=ᵢ ($ 4095) = true) in H4. {
       clear CSR H4.
       unfolds.
       asserts_rewrite (($ (-4096)) <=ᵢ ($ 44) = true). unfolds.
       asserts_rewrite (($ 44) >ᵢ ($ (-4096)) = true). mauto. auto. mauto. 
    }
    asserts_rewrite (word_aligned (get_R r14 R) +ᵢ ($ 44) = true) in H4. iauto.
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

  assert (R'#pc = R_#pc +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)+ᵢ ($4) +ᵢ ($ 4)+ᵢ ($ 4)  +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) /\ normal_cursor (R',F')) as CSR'. {
    splits. {
      asserts_rewrite (get_R pc R' = get_R npc R). iauto.
      asserts_rewrite (get_R npc R = (get_R pc R) +ᵢ ($ 4)). apply CSR.
      asserts_rewrite (get_R pc R = (get_R pc R_) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)+ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)). apply CSR.
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

  assert ((exists Rx : RegFile, (Rx, F') = right_win 1 (R_save, F_save)) /\
        word_aligned_R (get_R r17 R_save) /\
        word_aligned_R (get_R r18 R_save) /\ word_aligned_R (get_R r14 R') +ᵢ ($ 44)) as ALIGN'. {
    splits; iauto.
    asserts_rewrite (F' = F). iauto. iauto.
    asserts_rewrite (get_R r14 R' = get_R r14 R). iauto. iauto.
  }

  assert (single_mask R'#cwp R'#wim) as MASK'. {
    asserts_rewrite (get_R cwp R' = get_R cwp R). iauto.
    asserts_rewrite (get_R wim R' = get_R wim R). iauto.
    apply MASK.
  }

  assert (D' = []) as DELAY'. {
    iauto.
  }

  assert (f_context F_save /\ f_context F') as CONT'. {
    splits; iauto.
    asserts_rewrite(F' = F). iauto. iauto.
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
    exists (R,F) D  (st i4 sp+ₐₙ($48)).
    splits.
    - substs. auto.
    - asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)); iauto. apply FUNC.
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
          R'#sp = R#sp /\ F' = F /\ D' = []). {
  inverts P__.
  (* usr_mode *) {
    false. apply (ModeDeq (R,F)); auto.
    apply IVR.
  }
  (* sup_mode *) {
    inverts H10.
    unfolds in H6.
    inverts H6.
    assert (Cs (cursor_Q (R, F)) = Some (st i4 sp+ₐₙ($48))) as INS. {
    asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ  ($ 4)+ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4)). iauto.
    apply FUNC.
    }
    rewrite H11 in INS.
    clear H11. inverts INS.

    {
    inverts H12; try solve [false].
    inverts H5; try solve [false].
    repeat (split; auto); auto.
    unfold unexpected_trap in *.
    unfold trap_type in *.
    unfold eval_AddrExp in *.
    unfold eval_OpExp in *.
    asserts_rewrite(($ (-4096)) <=ᵢ ($ 48) && ($ 48) <=ᵢ ($ 4095) = true) in H4. {
       clear CSR H4.
       unfolds.
       asserts_rewrite (($ (-4096)) <=ᵢ ($ 48) = true). unfolds.
       asserts_rewrite (($ 48) >ᵢ ($ (-4096)) = true). mauto. auto. mauto. 
    }
    asserts_rewrite (word_aligned (get_R r14 R) +ᵢ ($ 48) = true) in H4. iauto.
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

  assert (R'#pc = R_#pc +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)+ᵢ ($4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)  +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) /\ normal_cursor (R',F')) as CSR'. {
    splits. {
      asserts_rewrite (get_R pc R' = get_R npc R). iauto.
      asserts_rewrite (get_R npc R = (get_R pc R) +ᵢ ($ 4)). apply CSR.
      asserts_rewrite (get_R pc R = (get_R pc R_) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)+ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)). apply CSR.
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

  assert ((exists Rx : RegFile, (Rx, F') = right_win 1 (R_save, F_save)) /\
        word_aligned_R (get_R r17 R_save) /\
        word_aligned_R (get_R r18 R_save) /\ word_aligned_R (get_R r14 R') +ᵢ ($ 48)) as ALIGN'. {
    splits; iauto.
    asserts_rewrite (F' = F). iauto. iauto.
    asserts_rewrite (get_R r14 R' = get_R r14 R). iauto. iauto.
  }

  assert (single_mask R'#cwp R'#wim) as MASK'. {
    asserts_rewrite (get_R cwp R' = get_R cwp R). iauto.
    asserts_rewrite (get_R wim R' = get_R wim R). iauto.
    apply MASK.
  }

  assert (D' = []) as DELAY'. {
    iauto.
  }

  assert (f_context F_save /\ f_context F') as CONT'. {
    splits; iauto.
    asserts_rewrite(F' = F). iauto. iauto.
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
    exists (R,F) D  (st i5 sp+ₐₙ($52)).
    splits.
    - substs. auto.
    - asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)); iauto. apply FUNC.
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
          R'#sp = R#sp /\ F' = F /\ D' = []). {
  inverts P__.
  (* usr_mode *) {
    false. apply (ModeDeq (R,F)); auto.
    apply IVR.
  }
  (* sup_mode *) {
    inverts H10.
    unfolds in H6.
    inverts H6.
    assert (Cs (cursor_Q (R, F)) = Some (st i5 sp+ₐₙ($52))) as INS. {
    asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ  ($ 4)+ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4)). iauto.
    apply FUNC.
    }
    rewrite H11 in INS.
    clear H11. inverts INS.

    {
    inverts H12; try solve [false].
    inverts H5; try solve [false].
    repeat (split; auto); auto.
    unfold unexpected_trap in *.
    unfold trap_type in *.
    unfold eval_AddrExp in *.
    unfold eval_OpExp in *.
    asserts_rewrite(($ (-4096)) <=ᵢ ($ 52) && ($ 52) <=ᵢ ($ 4095) = true) in H4. {
       clear CSR H4.
       unfolds.
       asserts_rewrite (($ (-4096)) <=ᵢ ($ 52) = true). unfolds.
       asserts_rewrite (($ 52) >ᵢ ($ (-4096)) = true). mauto. auto. mauto. 
    }
    asserts_rewrite (word_aligned (get_R r14 R) +ᵢ ($ 52) = true) in H4. iauto.
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

  assert (R'#pc = R_#pc +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)+ᵢ ($4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)  +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) /\ normal_cursor (R',F')) as CSR'. {
    splits. {
      asserts_rewrite (get_R pc R' = get_R npc R). iauto.
      asserts_rewrite (get_R npc R = (get_R pc R) +ᵢ ($ 4)). apply CSR.
      asserts_rewrite (get_R pc R = (get_R pc R_) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)+ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)). apply CSR.
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

  assert ((exists Rx : RegFile, (Rx, F') = right_win 1 (R_save, F_save)) /\
        word_aligned_R (get_R r17 R_save) /\
        word_aligned_R (get_R r18 R_save) /\ word_aligned_R (get_R r14 R') +ᵢ ($ 52)) as ALIGN'. {
    splits; iauto.
    asserts_rewrite (F' = F). iauto. iauto.
    asserts_rewrite (get_R r14 R' = get_R r14 R). iauto. iauto.
  }

  assert (single_mask R'#cwp R'#wim) as MASK'. {
    asserts_rewrite (get_R cwp R' = get_R cwp R). iauto.
    asserts_rewrite (get_R wim R' = get_R wim R). iauto.
    apply MASK.
  }

  assert (D' = []) as DELAY'. {
    iauto.
  }

  assert (f_context F_save /\ f_context F') as CONT'. {
    splits; iauto.
    asserts_rewrite(F' = F). iauto. iauto.
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
    exists (R,F) D  (st i6 sp+ₐₙ($56)).
    splits.
    - substs. auto.
    - asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)); iauto. apply FUNC.
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
          R'#sp = R#sp /\ F' = F /\ D' = []). {
  inverts P__.
  (* usr_mode *) {
    false. apply (ModeDeq (R,F)); auto.
    apply IVR.
  }
  (* sup_mode *) {
    inverts H10.
    unfolds in H6.
    inverts H6.
    assert (Cs (cursor_Q (R, F)) = Some (st i6 sp+ₐₙ($56))) as INS. {
    asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ  ($ 4)+ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4)). iauto.
    apply FUNC.
    }
    rewrite H11 in INS.
    clear H11. inverts INS.

    {
    inverts H12; try solve [false].
    inverts H5; try solve [false].
    repeat (split; auto); auto.
    unfold unexpected_trap in *.
    unfold trap_type in *.
    unfold eval_AddrExp in *.
    unfold eval_OpExp in *.
    asserts_rewrite(($ (-4096)) <=ᵢ ($ 56) && ($ 56) <=ᵢ ($ 4095) = true) in H4. {
       clear CSR H4.
       unfolds.
       asserts_rewrite (($ (-4096)) <=ᵢ ($ 56) = true). unfolds.
       asserts_rewrite (($ 56) >ᵢ ($ (-4096)) = true). mauto. auto. mauto. 
    }
    asserts_rewrite (word_aligned (get_R r14 R) +ᵢ ($ 56) = true) in H4. iauto.
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

  assert (R'#pc = R_#pc +ᵢ ($ 4)+ᵢ ($4) +ᵢ ($4) +ᵢ ($4)+ᵢ ($4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)  +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) /\ normal_cursor (R',F')) as CSR'. {
    splits. {
      asserts_rewrite (get_R pc R' = get_R npc R). iauto.
      asserts_rewrite (get_R npc R = (get_R pc R) +ᵢ ($ 4)). apply CSR.
      asserts_rewrite (get_R pc R = (get_R pc R_) +ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)+ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)). apply CSR.
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

  assert ((exists Rx : RegFile, (Rx, F') = right_win 1 (R_save, F_save)) /\
        word_aligned_R (get_R r17 R_save) /\
        word_aligned_R (get_R r18 R_save) /\ word_aligned_R (get_R r14 R') +ᵢ ($ 56)) as ALIGN'. {
    splits; iauto.
    asserts_rewrite (F' = F). iauto. iauto.
    asserts_rewrite (get_R r14 R' = get_R r14 R). iauto. iauto.
  }

  assert (single_mask R'#cwp R'#wim) as MASK'. {
    asserts_rewrite (get_R cwp R' = get_R cwp R). iauto.
    asserts_rewrite (get_R wim R' = get_R wim R). iauto.
    apply MASK.
  }

  assert (D' = []) as DELAY'. {
    iauto.
  }

  assert (f_context F_save /\ f_context F') as CONT'. {
    splits; iauto.
    asserts_rewrite(F' = F). iauto. iauto.
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
    exists (R,F) D  (st i7 sp+ₐₙ($60)).
    splits.
    - substs. auto.
    - asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)); iauto. apply FUNC.
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
          R'#sp = R#sp /\ F' = F /\ D' = []). {
  inverts P__.
  (* usr_mode *) {
    false. apply (ModeDeq (R,F)); auto.
    apply IVR.
  }
  (* sup_mode *) {
    inverts H10.
    unfolds in H6.
    inverts H6.
    assert (Cs (cursor_Q (R, F)) = Some (st i7 sp+ₐₙ($60))) as INS. {
    asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ  ($ 4)+ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4)). iauto.
    apply FUNC.
    }
    rewrite H11 in INS.
    clear H11. inverts INS.

    {
    inverts H12; try solve [false].
    inverts H5; try solve [false].
    repeat (split; auto); auto.
    unfold unexpected_trap in *.
    unfold trap_type in *.
    unfold eval_AddrExp in *.
    unfold eval_OpExp in *.
    asserts_rewrite(($ (-4096)) <=ᵢ ($ 60) && ($ 60) <=ᵢ ($ 4095) = true) in H4. {
       clear CSR H4.
       unfolds.
       asserts_rewrite (($ (-4096)) <=ᵢ ($ 60) = true). unfolds.
       asserts_rewrite (($ 60) >ᵢ ($ (-4096)) = true). mauto. auto. mauto. 
    }
    asserts_rewrite (word_aligned (get_R r14 R) +ᵢ ($ 60) = true) in H4. iauto.
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

  assert (R'#pc = R_#pc +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($4) +ᵢ ($4) +ᵢ ($4)+ᵢ ($4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)  +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) /\ normal_cursor (R',F')) as CSR'. {
    splits. {
      asserts_rewrite (get_R pc R' = get_R npc R). iauto.
      asserts_rewrite (get_R npc R = (get_R pc R) +ᵢ ($ 4)). apply CSR.
      asserts_rewrite (get_R pc R = (get_R pc R_) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)+ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4)). apply CSR.
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

  assert ((exists Rx : RegFile, (Rx, F') = right_win 1 (R_save, F_save)) /\
        word_aligned_R (get_R r17 R_save) /\
        word_aligned_R (get_R r18 R_save)) as ALIGN'. {
    splits; iauto.
    asserts_rewrite (F' = F). iauto. iauto.
  }

  assert (single_mask R'#cwp R'#wim) as MASK'. {
    asserts_rewrite (get_R cwp R' = get_R cwp R). iauto.
    asserts_rewrite (get_R wim R' = get_R wim R). iauto.
    apply MASK.
  }

  assert (D' = []) as DELAY'. {
    iauto.
  }

  assert (f_context F_save /\ f_context F') as CONT'. {
    splits; iauto.
    asserts_rewrite(F' = F). iauto. iauto.
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
    exists (R,F) D  (restore g0 g0 ᵣ g0).
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
          R'#cwp = post_cwp 1 R /\ R'#l1 = R_save#l1 /\ R'#l2 = R_save#l2 /\ D' = [] /\ (exists Rx,(Rx,F') = left_win 1 (R,F))). {
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
    asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)); iauto. apply FUNC.
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
    } iauto.

    {
    asserts_rewrite (get_R r17 (next R'0 # r0 <- ((get_R r0 R) +ᵢ a)) = get_R r17 R'0). iauto.
    assert((exists Rx : RegFile, (Rx, F) = right_win 1 (R_save, F_save))). iauto.
    destruct H0 as (Rx & H0).
    simpl. apply (right_then_left_il r17 R_save F_save Rx F R F' R'0); iauto.
    }

    {
    asserts_rewrite (get_R r18 (next R'0 # r0 <- ((get_R r0 R) +ᵢ a)) = get_R r18 R'0). iauto.
    assert((exists Rx : RegFile, (Rx, F) = right_win 1 (R_save, F_save))). iauto.
    destruct H0 as (Rx & H0).
    simpl. apply (right_then_left_il r18 R_save F_save Rx F R F' R'0); iauto.
    }
    auto.

    iauto.

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
    asserts_rewrite((get_R cwp R') = post_cwp 1 R). iauto.
    apply (cwp_cycle_post R). apply IVR.
  }

  assert (word_aligned_R R'#r17 /\ word_aligned_R R'#r18) as ALIGN'. {
    splits; iauto.
    asserts_rewrite (get_R r17 R' = get_R r17 R_save). iauto. iauto.
    asserts_rewrite (get_R r18 R' = get_R r18 R_save). iauto. iauto.
  }

  assert (single_mask (pre_cwp 1 R') R'#wim) as MASK'. {
    clear GOAL CSR CSR' ALIGN ALIGN'.
    asserts_rewrite (pre_cwp 1 R' = get_R cwp R).
    symmetry.
    apply (post_is_pre R R'); iauto. apply IVR.
    asserts_rewrite (get_R wim R' = get_R wim R). iauto.
    apply MASK.
  }

  assert (D' = []) as DELAY'. {
    iauto.
  }

  assert (f_context F') as CONT'. {
    assert (exists Rx : RegFile, (Rx, F') = left_win 1 (R, F)). iauto.
    destruct H0 as (Rx & H0).
    apply (hold_context_left R Rx F F'); iauto.
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
    exists (R,F) D  (or g0 l7 ᵣ g1).
    splits.
    - substs. auto.
    - asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)); iauto. apply FUNC.
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
          R'#cwp = R#cwp /\ R'#l1 = R#l1 /\ R'#l2 = R#l2 /\ D' = [] /\ F' = F). {
  inverts P__.
  (* usr_mode *) {
    false. apply (ModeDeq (R,F)); auto.
    apply IVR.
  }
   (* sup_mode *) {
    inverts H10.
    unfolds in H6.
    inverts H6.
    assert (Cs (cursor_Q (R, F)) = Some (or g0 l7 ᵣ g1)) as INS. {
    asserts_rewrite (cursor_Q (R, F) = (cursor_Q (R_, F_)) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)); iauto. apply FUNC.
    }
    rewrite H11 in INS.
    clear H11. inverts INS.

    {
    inverts H12; try solve [false].
    inverts H5; try solve [false].
    inverts H4; repeat (split; auto); auto.
    }

    (* annul? no !*){
    inverts H5.
    false.
    apply (AnnulDeq R).
    apply H8. apply IVR.
    }
  }
  }

  assert (R'#pc = R_#pc +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4) +ᵢ ($ 4)+ᵢ ($4) +ᵢ ($4) +ᵢ ($4)+ᵢ ($4) +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)  +ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($ 4)+ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) +ᵢ ($4) /\ normal_cursor (R',F')) as CSR'. {
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
    try asserts_rewrite ((get_R cwp R') = (get_R cwp R)); 
    try asserts_rewrite ((get_R annul R') = (get_R annul R)); 
    try asserts_rewrite ((get_R et R') = (get_R et R));
    try asserts_rewrite ((get_R trap R') = (get_R trap R));
    try asserts_rewrite ((get_R s R') = (get_R s R));
    iauto; try apply IVR.
  }

  assert (word_aligned_R R'#r17 /\ word_aligned_R R'#r18) as ALIGN'. {
    splits; iauto.
    asserts_rewrite (get_R r17 R' = get_R r17 R). iauto. iauto.
    asserts_rewrite (get_R r18 R' = get_R r18 R). iauto. iauto.
  }

  assert (single_mask (pre_cwp 1 R') R'#wim) as MASK'. {
    unfold pre_cwp.
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

  assert (single_mask (pre_cwp 1 R') R'#wim) as MASK'. {
    unfold pre_cwp.
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
      apply (mask_cwp_post2 R); iauto. apply IVR.
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
      apply (mask_cwp_post2 R); iauto. apply IVR.
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

  assert (single_mask (pre_cwp 2 R') R'#wim) as MASK'. {
    asserts_rewrite (pre_cwp 2 R' = pre_cwp 1 R).
    symmetry. apply (pre_pre_is_pre2 R R'); iauto.
    apply IVR.
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

}}}}}}}}}}}}}}}}}}}}}}}}}}}}}
Qed.




