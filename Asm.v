Require Import SMTC.Coqlib.
Require Import SMTC.Integers.


Require Import Maps.
Open Scope Z_scope.
Import ListNotations.


Definition Word := int.

Inductive GenReg: Type := 
  | r0: GenReg  | r1: GenReg  | r2: GenReg  | r3: GenReg  | r4: GenReg  | r5: GenReg  | r6: GenReg  | r7: GenReg
  | r8: GenReg  | r9: GenReg  | r10: GenReg | r11: GenReg | r12: GenReg | r13: GenReg | r14: GenReg | r15: GenReg
  | r16: GenReg | r17: GenReg | r18: GenReg | r19: GenReg | r20: GenReg | r21: GenReg | r22: GenReg | r23: GenReg
  | r24: GenReg | r25: GenReg | r26: GenReg | r27: GenReg | r28: GenReg | r29: GenReg | r30: GenReg | r31: GenReg.


Inductive AsReg: Type :=
  | asr0: AsReg  | asr1: AsReg  | asr2: AsReg  | asr3: AsReg  | asr4: AsReg  | asr5: AsReg  | asr6: AsReg  | asr7: AsReg
  | asr8: AsReg  | asr9: AsReg  | asr10: AsReg | asr11: AsReg | asr12: AsReg | asr13: AsReg | asr14: AsReg | asr15: AsReg
  | asr16: AsReg | asr17: AsReg | asr18: AsReg | asr19: AsReg | asr20: AsReg | asr21: AsReg | asr22: AsReg | asr23: AsReg
  | asr24: AsReg | asr25: AsReg | asr26: AsReg | asr27: AsReg | asr28: AsReg | asr29: AsReg | asr30: AsReg | asr31: AsReg.

Inductive Symbol: Type :=
  | psr: Symbol
  | wim: Symbol
  | tbr: Symbol
  | y: Symbol
  | Sasr: AsReg -> Symbol.
Coercion Sasr: AsReg >-> Symbol.

Inductive OpExp: Type :=
  | Or: GenReg -> OpExp
  | Ow: Word -> OpExp.

Inductive AddrExp: Type :=
  | Ao: OpExp-> AddrExp
  | Aro: GenReg -> OpExp -> AddrExp.

Inductive TrapExp: Type :=
  | Tr: GenReg -> TrapExp
  | Trr: GenReg -> GenReg -> TrapExp
  | Trw: GenReg -> Word -> TrapExp
  | Tw: Word -> TrapExp.

Inductive TestCond: Type :=
  | al: TestCond    (**r always *)
  | nv: TestCond    (**r never *)
  | ne: TestCond    (**r not equal *)
  | eq: TestCond    (**r equal *).

Inductive SparcIns: Type :=
  | bicc: TestCond -> AddrExp -> SparcIns
  | bicca: TestCond -> AddrExp -> SparcIns
  | jmpl: AddrExp -> GenReg -> SparcIns
  | ld: AddrExp -> GenReg -> SparcIns
  | st: GenReg -> AddrExp -> SparcIns
  | ticc: TestCond -> TrapExp -> SparcIns
  | save: GenReg -> OpExp -> GenReg -> SparcIns
  | restore: GenReg -> OpExp -> GenReg -> SparcIns
  | rett: AddrExp -> SparcIns
  | rd: Symbol -> GenReg -> SparcIns
  | wr: GenReg -> OpExp -> Symbol -> SparcIns
  | sll: GenReg -> OpExp -> GenReg -> SparcIns
  | srl: GenReg -> OpExp -> GenReg -> SparcIns
  | or: GenReg -> OpExp -> GenReg -> SparcIns
  | and: GenReg -> OpExp -> GenReg -> SparcIns
  | nop: SparcIns.

Inductive PsrSeg: Type :=
  | n: PsrSeg
  | z: PsrSeg
  | v: PsrSeg
  | c: PsrSeg
  | pil: PsrSeg
  | s: PsrSeg
  | ps: PsrSeg
  | et: PsrSeg
  | cwp: PsrSeg.

Inductive TbrSeg: Type :=
  | tba: TbrSeg
  | tt: TbrSeg.

Inductive RegName: Type :=
  | Rr: GenReg -> RegName
  | Rp: PsrSeg -> RegName
  | Rt: TbrSeg -> RegName
  | Rwim: RegName
  | Ry: RegName
  | Rasr: AsReg -> RegName
  | pc: RegName
  | npc: RegName
  | trap: RegName
  | annul: RegName.
Coercion Rr: GenReg >-> RegName.
Coercion Rp: PsrSeg >-> RegName.
Coercion Rt: TbrSeg >-> RegName.
Coercion Rasr: AsReg >-> RegName.

Lemma RegName_eq: forall (x y: RegName), {x=y} + {x<>y}.
Proof. repeat decide equality. Defined.
Module RegNameEq.
  Definition t := RegName.
  Definition eq := RegName_eq.
End RegNameEq.
Module RegMap := EMap(RegNameEq).
Definition RegFile := RegMap.t Word.

Definition Frame: Type := list Word.

Definition FrameList: Type := list Frame.

Definition DelayCycle := nat.

Definition DelayItem: Type := DelayCycle * Symbol * Word.

Definition DelayList: Type := list DelayItem.

Definition RState: Type := RegFile * FrameList.

Definition Address: Type := Word.

Module WordEq.
  Definition t := Word.
  Definition eq := Int.eq_dec.
End WordEq.
Module WordMap := EMap(WordEq).
Definition Memory := WordMap.t (option Word).

Definition Label: Type := Word.

Definition CodeHeap := WordMap.t (option SparcIns).

Definition CodePair: Type := CodeHeap * CodeHeap.

Definition MemPair: Type := Memory * Memory.

Definition State: Type := MemPair * RState * DelayList.

Definition World: Type := CodePair * State.

Definition Event: Type := Word.

Definition EventList := list (option Event).

Notation "$ n" := (Int.repr n)(at level 1) : sparc_scope.
Notation "a <<ᵢ b" := (Int.shl a b)(at level 1) : sparc_scope.
Notation "a >>ᵢ b" := (Int.shru a b)(at level 1) : sparc_scope.
Notation "a &ᵢ b" := (Int.and a b)(at level 1) : sparc_scope.
Notation "a |ᵢ b" := (Int.or a b)(at level 1) : sparc_scope.
Notation "a +ᵢ b" := (Int.add a b)(at level 1) : sparc_scope.
Notation "a -ᵢ b" := (Int.sub a b)(at level 1) : sparc_scope.
Notation "a =ᵢ b" := (Int.eq a b)(at level 1) : sparc_scope.
Notation "a <ᵢ b" := (Int.lt a b)(at level 1) : sparc_scope.
Notation "a >ᵢ b" := (Int.lt b a)(at level 1) : sparc_scope.
Notation "a <=ᵢ b" := (orb(Int.lt a b)(Int.eq a b))(at level 1) : sparc_scope.
Notation "a >=ᵢ b" := (orb(Int.lt b a)(Int.eq a b))(at level 1) : sparc_scope.
Notation "a !=ᵢ b" := (negb(Int.eq a b))(at level 1) : sparc_scope.
Notation "a 'modu' b" := (Int.modu a b)(at level 1) : sparc_scope.
Notation "a 'xor' b" := (Int.xor a b)(at level 1) : sparc_scope.

Local Open Scope sparc_scope.

Definition N : Word := $8.
Definition X : DelayCycle := 2%nat.

Inductive Item: Type :=
  | Ir: RegName -> Item
  | Is: Symbol -> Item.

Coercion Ir: RegName >-> Item.
Coercion Is: Symbol >-> Item.

Definition get_range: Z -> Z -> Word -> Word :=
  fun i j N =>
    N &ᵢ (((($1)<<ᵢ($(j-i+1))) -ᵢ($1)) <<ᵢ($i)).

Notation " 'hi' n " := (get_range 10 31 n)(at level 1) : asm_scope.

Definition set_range: Z -> Z -> Word -> Word -> Word :=
  fun i j n N =>
    n |ᵢ (N &ᵢ (Int.not (((($1)<<ᵢ($(j-i+1))) -ᵢ($1)) <<ᵢ($i)))).

Definition get_bit: Z -> Word -> Word :=
  fun i N => get_range i i N.

Definition set_bit: Z -> Word -> Word -> Word :=
  fun i b N => set_range i i b N.

Definition get_R: Item -> RegFile -> Word :=
  fun i R =>
    match i with
    | Ir rn =>
      match rn with
      | r0 => $0
      | _ => R rn
      end
    | Is psr => set_bit 23 (R n)(
                set_bit 22 (R z)(
                set_bit 21 (R v)(
                set_bit 20 (R c)(
                set_range 8 11 (R pil)(
                set_bit 7 (R s)(
                set_bit 6 (R ps)(
                set_bit 5 (R et)(
                set_range 0 4 (R cwp)(
                ($0))))))))))
    | Is tbr => set_range 12 31 (R tba)(
                set_range 4 11 (R tt) ($0))
    | Is wim => R Rwim
    | Is y => R Ry
    | Is (Sasr asri) => R (Rasr asri)
    end.


Definition set_R: Item -> Word -> RegFile -> RegFile :=
  fun i w R =>
    match i with
    | Ir rn =>
      match rn with
      | r0 => R
      | _ => RegMap.set rn w R
      end
    | Is psr => RegMap.set n (get_bit 23 w)(
                RegMap.set z (get_bit 22 w)(
                RegMap.set v (get_bit 21 w)(
                RegMap.set c (get_bit 20 w)(
                RegMap.set s (get_bit 7 w)(
                RegMap.set ps (get_bit 6 w)(
                (R)))))))
    | Is tbr => RegMap.set tba (get_range 12 31 w) R
    | Is wim => RegMap.set Rwim (get_range 0 ((Int.unsigned N)-1) w) R
    | Is y => RegMap.set Ry w R
    | Is (Sasr asri) => RegMap.set (Rasr asri) w R
    end.

Notation "a # b" := (get_R b a) (at level 1, only parsing) : sparc_scope.
Notation "a # b <- c" := (set_R b c a) (at level 1, b at next level) : sparc_scope.

Hint Unfold get_R.
Hint Unfold set_R.


Definition eval_TestCond: TestCond -> RegFile -> bool :=
  fun c R =>
    match c with
    | al => true
    | nv => false
    | ne => if (R#z) =ᵢ($0) then true else false
    | eq => if (R#z) !=ᵢ($0) then true else false
    end.

Definition eval_OpExp: OpExp -> RegFile -> option Word :=
  fun o R =>
    match o with
    | Or r => Some R#r
    | Ow w => if andb (($-4096) <=ᵢ w) (w <=ᵢ ($4095)) then Some w else None
    end.

Definition eval_AddrExp: AddrExp -> RegFile -> option Word :=
  fun a R =>
    match a with
    | Ao o => eval_OpExp o R
    | Aro r o =>
      match eval_OpExp o R with
      | Some w => Some ((R#r) +ᵢ w)
      | None => None
      end
    end.

Definition eval_TrapExp: TrapExp -> RegFile -> option Word :=
  fun t R =>
    match t with
    | Tr r => Some R#r
    | Trr ri rj => Some ((R#ri) +ᵢ (R#rj))
    | Trw r w => if andb (($-64) <=ᵢ w) (w <=ᵢ ($63)) then Some ((R#r) +ᵢ w) else None
    | Tw w => if andb (($0) <=ᵢ w) (w <=ᵢ ($127)) then Some w else None
    end.

Definition next: RegFile -> RegFile :=
  fun R =>
    R#pc  <- (R#npc)
      #npc <- (R#npc +ᵢ ($4)).

Definition next_Q: RState -> RState :=
  fun Q => 
    let (R,F) := Q in (next R,F).

Hint Unfold next.

Definition djmp: Word -> RegFile -> RegFile :=
  fun w R =>
    R#pc  <- (R#npc)
      #npc <- w.

Hint Unfold djmp.

Definition tbr_jmp: RegFile -> RegFile :=
  fun R =>
    R#pc  <- (R#tbr)
      #npc <- (R#tbr +ᵢ ($4)).

Hint Unfold tbr_jmp.

Definition set_annul: RegFile -> RegFile :=
  fun R => R#annul <- ($1).

Definition clear_annul: RegFile -> RegFile :=
  fun R => R#annul <- ($0).

Definition clear_annul_Q: RState -> RState :=
  fun Q => let (R,F) := Q in (clear_annul R,F).

Definition to_usr: RegFile -> RegFile :=
  fun R => R#s <- ($0).

Definition to_sup: RegFile -> RegFile :=
  fun R => R#s <- ($1).

Definition save_mode: RegFile -> RegFile :=
  fun R => R#ps <- (R#s).

Definition restore_mode: RegFile -> RegFile :=
  fun R => R#s <- (R#ps).

Definition enable_trap: RegFile -> RegFile :=
  fun R => R#et <- ($1).

Definition disable_trap: RegFile -> RegFile :=
  fun R => R#et <- ($0).

Definition set_trap: RegFile -> RegFile :=
  fun R => R#trap <- ($1).

Definition clear_trap: RegFile -> RegFile :=
  fun R => R#trap <- ($0).

Definition annuled: RegFile -> bool :=
  fun R => if R#annul =ᵢ ($1) then true else false.

Definition annuled_R: RegFile -> Prop :=
  fun R => annuled R = true.

Definition annuled_Q: RState -> Prop :=
  fun Q => let (R,_) := Q in annuled_R R.

Definition not_annuled_R: RegFile -> Prop :=
  fun R => annuled R = false.

Definition not_annuled_Q: RState -> Prop :=
  fun Q => let (R,_) := Q in not_annuled_R R.

Definition has_trap: RegFile -> bool :=
  fun R => if R#trap =ᵢ ($1) then true else false.

Definition has_trap_R: RegFile -> Prop :=
  fun R => has_trap R = true.

Definition no_trap_R: RegFile -> Prop :=
  fun R => has_trap R = false.

Definition no_trap_Q: RState -> Prop :=
  fun Q => let (R,_) := Q in no_trap_R R.

Definition no_trap_S : State -> Prop :=
  fun S => let '(_,Q,_) := S in no_trap_Q Q.

Definition has_trap_Q: RState -> Prop :=
  fun Q => let (R,_) := Q in has_trap_R R.

Definition has_trap_S : State -> Prop :=
  fun S => let '(_,Q,_) := S in has_trap_Q Q.

Definition trap_enabled: RegFile -> bool :=
  fun R => if R#et =ᵢ ($1) then true else false.

Definition trap_enabled_R: RegFile -> Prop :=
  fun R => trap_enabled R = true.

Definition trap_disabled_R: RegFile -> Prop :=
  fun R => trap_enabled R = false.

Definition trap_disabled_Q: RState -> Prop :=
  fun Q => let (R,_) := Q in trap_disabled_R R.

Definition trap_disabled_S : State -> Prop :=
  fun S => let '(_,Q,_) := S in trap_disabled_Q Q.

Definition usr_mode: RegFile -> bool :=
  fun R => if R#s =ᵢ ($0) then true else false.

Definition usr_mode_R: RegFile -> Prop :=
  fun R => usr_mode R = true.

Definition usr_mode_Q: RState -> Prop :=
  fun Q => let (R,_) := Q in usr_mode_R R.

Definition usr_mode_S : State -> Prop :=
  fun S => let '(_,Q,_) := S in usr_mode_Q Q.

Definition sup_mode_R: RegFile -> Prop :=
  fun R => usr_mode R = false.

Definition sup_mode_Q: RState -> Prop :=
  fun Q => let (R,_) := Q in sup_mode_R R.

Definition sup_mode_S : State -> Prop :=
  fun S => let '(_,Q,_) := S in sup_mode_Q Q.

Definition word_aligned: Word -> bool :=
  fun w => if (get_range 0 1 w) =ᵢ ($0) then true else false.

Definition word_aligned_R: Word -> Prop :=
  fun w => word_aligned w = true.

Definition win_masked: Word -> RegFile -> bool :=
  fun w R => if ((($1)<<ᵢw) &ᵢ (R#wim)) !=ᵢ ($0) then true else false.

Definition win_masked_R: Word -> RegFile -> Prop :=
  fun w R => win_masked w R = true.

Definition save_pc: GenReg -> RegFile -> RegFile :=
  fun r R => R#r <- (R#pc).

Hint Unfold save_pc.

Definition save_pc_npc: GenReg -> GenReg -> RegFile -> RegFile :=
  fun ri rj R =>
    if negb (annuled R)
      then
        R#ri <- (R#pc)
          #rj <- (R#npc)
      else clear_annul(
        R#ri <- (R#npc)
          #rj <- (R#npc +ᵢ ($4))).

Hint Unfold save_pc_npc.

Definition fench: RegFile -> FrameList :=
  fun R =>
    [[R#r8;R#r9;R#r10;R#r11;R#r12;R#r13;R#r14;R#r15];
     [R#r16;R#r17;R#r18;R#r19;R#r20;R#r21;R#r22;R#r23];
     [R#r24;R#r25;R#r26;R#r27;R#r28;R#r29;R#r30;R#r31]].

Definition replace: FrameList -> RegFile -> RegFile :=
  fun l R =>
    match l with
    | [[w8;w9;w10;w11;w12;w13;w14;w15];
       [w16;w17;w18;w19;w20;w21;w22;w23];
       [w24;w25;w26;w27;w28;w29;w30;w31]] => 
        R#r8  <- w8    #r16 <- w16   #r24 <- w24
         #r9  <- w9    #r17 <- w17   #r25 <- w25
         #r10 <- w10   #r18 <- w18   #r26 <- w26
         #r11 <- w11   #r19 <- w19   #r27 <- w27
         #r12 <- w12   #r20 <- w20   #r28 <- w28
         #r13 <- w13   #r21 <- w21   #r29 <- w29
         #r14 <- w14   #r22 <- w22   #r30 <- w30
         #r15 <- w15   #r23 <- w23   #r31 <- w31
    | _ => R
    end.

Definition left: FrameList -> FrameList -> FrameList * FrameList :=
  fun L l =>
    match L,l with
    | i::j::L',p::q::l' => (L'++[p;q],l'++[i;j])
    | _,_ => (L,l)
    end.

Definition right: FrameList -> FrameList -> FrameList * FrameList :=
  fun L l =>
    let (L',l') := left (rev L) (rev l) in (rev L',rev l').

Fixpoint left_iter (k : nat) : FrameList -> FrameList -> FrameList * FrameList :=
  fun L l =>
    match k with
    | O => (L,l)
    | S k' => let (L',l') := left L l in left_iter k' L' l'
    end.


Fixpoint right_iter (k : nat) : FrameList -> FrameList -> FrameList * FrameList :=
  fun L l =>
    match k with
    | O => (L,l)
    | S k' => let (L',l') := right L l in right_iter k' L' l'
    end.


Definition post_cwp: Z -> RegFile -> Word :=
   fun k R => (R#cwp +ᵢ ($k)) modu N.

Definition pre_cwp: Z -> RegFile -> Word :=
   fun k R => (R#cwp +ᵢ N -ᵢ ($k)) modu N.

Definition left_win: Z -> RState -> RState :=
  fun k Q =>
    let (R,F) := Q in
    let (F',l) := left_iter (Z.to_nat k) F (fench R) in
    let R' := replace l R in
    (R'#cwp <- (post_cwp k R),F').

Definition right_win: Z -> RState -> RState :=
  fun k Q =>
    let (R,F) := Q in
    let (F',l) := right_iter (Z.to_nat k) F (fench R) in
    let R' := replace l R in
    (R'#cwp <- (pre_cwp k R),F').

Definition inc_win: RState -> option RState :=
  fun Q =>
    let (R,F) := Q in
      if negb (win_masked (post_cwp 1 R) R)
        then Some (left_win 1 Q)
       else None.

Definition dec_win: RState -> option RState :=
  fun Q =>
    let (R,F) := Q in
      if negb (win_masked (pre_cwp 1 R) R)
        then Some (right_win 1 Q)
       else None.

Definition set_win: Word -> RState -> RState :=
  fun w Q =>
    let (R,F) := Q in
      if Int.unsigned w >? Int.unsigned (R#cwp)
        then left_win (Int.unsigned (w -ᵢ (R#cwp))) Q
      else if Int.unsigned w <? Int.unsigned (R#cwp)
        then right_win (Int.unsigned((R#cwp) -ᵢ w)) Q
      else Q.

Definition set_user_trap: Word -> RegFile -> RegFile :=
  fun k R =>
    set_trap (R#tt <- (($128) +ᵢ k)).

Definition rett_f: RState -> option RState :=
  fun Q =>
    match inc_win Q with
    | None => None
    | Some (R',F') => Some (restore_mode(enable_trap R'),F')
    end.

Fixpoint exe_delay (Q: RState) (D: DelayList) : (RState * DelayList) :=
  match D with
  | (O,syb,w)::D' =>
    let (Q',D'') := exe_delay Q D' in
    let (R',F') := Q' in
    match syb with
    | psr => (set_win (get_range 0 4 w) (R'#syb <- w,F'),D'')
    | _ => ((R'#syb <- w,F'),D'')
    end
  | (S k,syb,w)::D' =>
    let (Q',D'') := exe_delay Q D' in
    (Q',(k,syb,w)::D'')
 | nil => (Q,D)
 end.


Definition set_delay: Symbol -> Word -> DelayList -> DelayList :=
  fun syb w D =>
    (X,syb,w)::D.


Definition illegal_ins := $2.
Definition privileged_ins := $3.
Definition mem_not_align := $7.
Definition div_by_zero := $42.
Definition win_overflow := $5.
Definition win_underflow := $6.


Definition interrupt: Word -> RState -> option RState :=
  fun w Q =>
    let (R,F) := Q in
      if andb (1%Z <=? Int.signed w) (Int.signed w <=? 15%Z) then
    if andb (andb (negb (has_trap R)) (trap_enabled R)) (orb (Int.signed w =? 15) (Int.signed R#pil <? Int.signed w))
      then Some (set_trap (R#tt <- ($(16 + Int.signed w))),F)
      else None
    else None.

Definition abort_ins: SparcIns -> RState -> Memory -> bool :=
  fun i Q M =>
    let (R,F) := Q in
    match i with
    | ld a _ =>
      match eval_AddrExp a R with
      | None => true
      | Some w =>
        match M w with
        | None => true
        | _ => false
        end
      end
    | st _ a =>
      match eval_AddrExp a R with
      | None => true
      | Some w => false
      end
    | bicc _ a
    | bicca _ a
    | jmpl a _ =>
      match eval_AddrExp a R with
      | None => true
      | _ => false
      end
    | rett a =>
      match eval_AddrExp a R with
      | None => true
      | Some w => 
          match word_aligned w,usr_mode R,inc_win Q with
          | false,_,_
          | _,true,_
          | _,_,None => true
          | _,_,_ => false
          end
      end
    | ticc _ a =>
      match eval_TrapExp a R with
      | None => true
      | _ => false
      end
    | and _ a _
    | or _ a _
    | sll _ a _
    | srl _ a _
    | save _ a _
    | restore _ a _
    | wr _ a _ =>
      match eval_OpExp a R with
      | None => true
      | _ => false
      end
    | _ => false
    end.

Definition trap_type: SparcIns -> RState -> option Word :=
  fun i Q =>
    let (R,F) := Q in
    match i with
    | rd psr _ | rd wim _ | rd tbr _ =>
        if usr_mode R then Some privileged_ins else None
    | wr r a psr =>
        if usr_mode R then Some privileged_ins else
        match eval_OpExp a R with
        | Some w => if (get_range 0 4 ((R#r)xor w)) >=ᵢ N then Some illegal_ins else None
        | None => None
        end
    | wr _ _ wim | wr _ _ tbr =>
        if usr_mode R then Some privileged_ins else None
    | save _ _ _ =>
        match dec_win Q with
        | None => Some win_overflow
        | _ => None
        end
    | restore _ _ _ =>
        match inc_win Q with
        | None => Some win_underflow
        | _ => None
        end
    | rett _ =>
        if trap_enabled R then
          if usr_mode R then Some privileged_ins
          else Some illegal_ins
        else None
    | ld a _ | st _ a | jmpl a _ | bicc _ a | bicca _ a =>
        match eval_AddrExp a R with
        | Some w =>
            if negb (word_aligned w)
              then Some mem_not_align
              else None
        | None => None
        end
    | _ => None
    end.

Definition unexpected_trap: SparcIns -> RState -> option RState :=
  fun i Q =>
    let (R,F) := Q in
    match trap_type i Q with
    | Some w => Some (set_trap(R#tt <- w),F)
    | None => None
    end.

Definition exe_trap: RState -> option RState :=
  fun Q =>
    let (R,F) := Q in
    if trap_enabled R then
      let (R',F') := right_win 1 Q in
      let R'' := to_sup(save_mode(disable_trap R')) in
      Some (clear_trap(save_pc_npc r17 r18 R''),F')
    else None.


Definition get_tt: RState -> Word :=
  fun Q => let (R,F) := Q in R#tt.


Inductive R__ : Memory * RegFile -> SparcIns -> Memory * RegFile -> Prop :=
  | Bicc_false:
        forall tc addr i w M R,
        i = bicc tc addr ->
        eval_AddrExp addr R = Some w ->
        word_aligned_R w ->
        eval_TestCond tc R = false ->
        R__ (M,R) i (M,next R)
  | Bicc_true:
        forall tc addr i w M R,
        i = bicc tc addr ->
        eval_AddrExp addr R = Some w ->
        word_aligned_R w ->
        eval_TestCond tc R = true ->
        R__ (M,R) i (M,djmp w R)
  | Bicca_false:
        forall tc addr i w M R,
        i = bicca tc addr ->
        eval_AddrExp addr R = Some w ->
        word_aligned_R w ->
        eval_TestCond tc R = false ->
        R__ (M,R) i (M,set_annul(next R))
  | Bicca_always:
        forall addr i w M R,
        i = bicca al addr ->
        eval_AddrExp addr R = Some w ->
        word_aligned_R w ->
        R__ (M,R) i (M,set_annul(djmp w R))
  | Bicca:
        forall tc addr i w M R,
        i = bicca tc addr ->
        eval_AddrExp addr R = Some w ->
        word_aligned_R w ->
        tc <> al ->
        eval_TestCond tc R = true ->
        R__ (M,R) i (M,djmp w R)
  | Jmpl:
        forall ri addr i w M R R',
        i = jmpl addr ri ->
        eval_AddrExp addr R = Some w ->
        word_aligned_R w ->
        save_pc ri R = R' ->
        R__ (M,R) i (M,djmp w R')
  | Ld:
        forall ri addr i w v M R R',
        i = ld addr ri ->
        eval_AddrExp addr R = Some w ->
        word_aligned_R w ->
        M w = Some v ->
        R' = R#ri <- v ->
        R__ (M,R) i (M,next R')
  | St:
        forall ri addr i w M M' R,
        i = st ri addr ->
        eval_AddrExp addr R = Some w ->
        word_aligned_R w ->
        M' = WordMap.set w (Some(R#ri)) M ->
        R__ (M,R) i (M',next R)
  | Nop:
        forall i M R,
        i = nop ->
        R__ (M,R) i (M,next R)
  | Ticc_false:
        forall tc st i a M R,
        i = ticc tc st ->
        eval_TrapExp st R = Some a ->
        eval_TestCond tc R = false ->
        R__ (M,R) i (M,next R)
  | Ticc_true:
        forall tc st i a M R,
        i = ticc tc st ->
        eval_TrapExp st R = Some a ->
        eval_TestCond tc R = true ->
        R__ (M,R) i (M,set_user_trap (get_range 0 6 a) R)
  | Rd_sup:
        forall syb ri i M R R',
        i = rd syb ri ->
        sup_mode_R R ->
        R' = R#ri <- (R#syb) ->
        R__ (M,R) i (M,next R')
  | Rd_usr:
        forall syb ri i M R R',
        i = rd syb ri ->
        usr_mode_R R ->
        syb <> tbr /\ syb <> wim /\ syb <> psr ->
        R' = R#ri <- (R#syb) ->
        R__ (M,R) i (M,next R')
  | And_:
        forall ri o rj i a w M R R',
        i = and ri o rj ->
        eval_OpExp o R = Some a ->
        Int.and (R#ri) a = w ->
        R' = R#rj <- w ->
        R__ (M,R) i (M,next R')
  | Or_:
        forall ri o rj i a w M R R',
        i = or ri o rj ->
        eval_OpExp o R = Some a ->
        Int.or (R#ri) a = w ->
        R' = R#rj <- w ->
        R__ (M,R) i (M,next R')
  | Sll:
        forall ri o rj i a w M R R',
        i = sll ri o rj ->
        eval_OpExp o R = Some a ->
        (R#ri) <<ᵢ (get_range 0 4 a) = w ->
        R' = R#rj <- w ->
        R__ (M,R) i (M,next R')
  | Srl:
        forall ri o rj i a w M R R',
        i = srl ri o rj ->
        eval_OpExp o R = Some a ->
        (R#ri) >>ᵢ (get_range 0 4 a) = w ->
        R' = R#rj <- w ->
        R__ (M,R) i (M,next R').


Inductive Q__:  Memory * RState * DelayList -> SparcIns -> Memory * RState * DelayList -> Prop :=
  | MR:
        forall i M R M' R' F D,
        R__ (M,R) i (M',R') ->
        Q__ (M,(R,F),D) i (M',(R',F),D)
  | Save:
        forall ri o rj i a M R R' R'' F F' D,
        i = save ri o rj ->
        dec_win (R,F) = Some (R',F') ->
        eval_OpExp o R = Some a ->
        R'' = R'#rj <- ((R#ri) +ᵢ a) ->
        Q__ (M,(R,F),D) i (M,(next R'',F'),D)
  | Restore:
        forall ri o rj i a M R R' R'' F F' D,
        i = restore ri o rj ->
        inc_win (R,F) = Some (R',F') ->
        eval_OpExp o R = Some a ->
        R'' = R'#rj <- ((R#ri) +ᵢ a) ->
        Q__ (M,(R,F),D) i (M,(next R'',F'),D)
  | Rett:
        forall addr i w M R R' F F' D, 
        i = rett addr ->
        trap_disabled_R R ->
        sup_mode_R R ->
        eval_AddrExp addr R = Some w ->
        word_aligned_R w ->
        rett_f (R,F) = Some (R',F') ->
        Q__ (M,(R,F),D) i (M,(djmp w R',F'),D)
  | Wr_usr:
        forall ri o syb i a w M R F D D',
        i = wr ri o syb ->
        usr_mode_R R ->
        syb <> tbr /\ syb <> wim /\ syb <> psr ->
        eval_OpExp o R = Some a ->
        R#ri xor a = w ->
        D' = set_delay syb w D ->
        Q__ (M,(R,F),D) i (M,(next R,F),D')
  | Wr_sup:
        forall ri o syb i a w M R F D D',
        i = wr ri o syb ->
        sup_mode_R R ->
        syb <>  psr ->
        eval_OpExp o R = Some a ->
        R#ri xor a = w ->
        D' = set_delay syb w D ->
        Q__ (M,(R,F),D) i (M,(next R,F),D')
  | Wr_psr:
        forall ri o i a w M R R' F D D',
        i = wr ri o psr ->
        sup_mode_R R ->
        eval_OpExp o R = Some a ->
        R#ri xor a = w ->
        (get_range 0 4 w) >=ᵢ N = false ->
        D' = set_delay psr w D ->
        R' = R#et <- (get_bit 5 w)
              #pil <- (get_range 8 11 w) ->
        Q__ (M,(R,F),D) i (M,(next R',F),D')
  | Trap_ins:
        forall i M Q Q' D,
        unexpected_trap i Q = Some Q' ->
        Q__ (M,Q,D) i (M,Q',D).

Definition cursor_R (R: RegFile) := R#pc.

Definition cursor_Q (Q: RState) :=
   let (R,_) := Q in cursor_R R.

Definition cursor_S (S: State) :=
   let '(_,Q,_) := S in cursor_Q Q.

Inductive H__: CodeHeap -> Memory * RState * DelayList -> Memory * RState * DelayList -> Prop :=
  | Normal:
        forall i C M M' Q Q' Q'' D D' D'',
        exe_delay Q D = (Q',D') ->
        not_annuled_Q Q' ->
        C (cursor_Q Q') = Some i ->
        Q__ (M,Q',D') i (M',Q'',D'') ->
        H__ C (M,Q,D) (M',Q'',D'')
  | Annul:
        forall C M Q Q' Q'' D D',
        exe_delay Q D = (Q',D') ->
        annuled_Q Q' ->
        clear_annul_Q Q' = Q'' ->
        H__ C (M,Q,D) (M,next_Q Q'',D').

Inductive P__: CodePair -> State -> State -> Prop :=
  | Nor_usr:
        forall Q Q' Cs Cu Ms Mu Mu' D D',
        no_trap_Q Q ->
        usr_mode_Q Q ->
        H__ Cu (Mu,Q,D) (Mu',Q',D') ->
        P__ (Cu,Cs) ((Mu,Ms),Q,D) ((Mu',Ms),Q',D')
  | Nor_sup:
        forall Q Q' Cs Cu Ms Ms' Mu D D',
        no_trap_Q Q ->
        sup_mode_Q Q ->
        H__ Cs (Ms,Q,D) (Ms',Q',D') ->
        P__ (Cu,Cs) ((Mu,Ms),Q,D) ((Mu,Ms'),Q',D').


Inductive E__: CodePair -> State -> Event -> State -> Prop :=
  | Interrupt:
        forall Q Q' Q'' Q''' w e Cs Cu Ms Ms' Mu D D',
        interrupt w Q = Some Q' ->
        get_tt Q' = e ->
        exe_trap Q' = Some Q'' ->
        H__  Cs (Ms,Q'',D) (Ms',Q''',D') ->
        E__ (Cu,Cs) ((Mu,Ms),Q,D) e ((Mu,Ms'),Q''',D')
  | Trap:
        forall Q Q' Q'' e Cs Cu Ms Ms' Mu D D',
        has_trap_Q Q ->
        get_tt Q = e ->
        exe_trap Q = Some Q' ->
        H__  Cs (Ms,Q',D) (Ms',Q'',D') ->
        E__ (Cu,Cs) ((Mu,Ms),Q,D) e ((Mu,Ms'),Q'',D').


Inductive Z__: CodePair -> State -> EventList -> nat -> State -> Prop :=
  | Zero:
        forall CP S,
        Z__ CP S nil 0 S
  | No_Event:
        forall CP E n S S' S'',
        Z__ CP S E n S'' ->
        P__ CP S'' S' ->
        Z__ CP S (None::E) (Datatypes.S n) S'
  | Has_Event:
        forall CP e E n S S' S'',
        Z__ CP S E n S'' ->
        E__ CP S'' e S' ->
        Z__ CP S ((Some e)::E) (Datatypes.S n) S'.
