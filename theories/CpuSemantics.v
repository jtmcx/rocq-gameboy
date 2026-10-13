From Stdlib Require Import ZArith.
From ITree Require Import ITree ITreeFacts.
From ITree Require Import Events.State.
From GameBoy Require Import Stdint.
From GameBoy Require Import Asm AsmEncoding.
Import ITreeNotations.
Import MonadNotation.
Open Scope monad_scope.
Open Scope u8_scope.

(*|
The SM83 has eight 8-bit registers: `A`, `B`, `C`, `D`, `E`, `F`,
`H` and `L`. All registers are general purpose except for `F`, which
contains flags used for arithmetic and jumps. There are two 16-bit
registers: `SP` (the stack pointer) and `PC` (the program counter).
|*)

Variant reg8 : Type := A | B | C | D | E | F | H | L.
Variant reg16 : Type := SP | PC.

(*|
8-bit registers form *pairs*. There are four valid register pairs: `AF`,
`BC`, `DE`, and `HL`. In some contexts, register pairs can be used as if
they're a single 16-bit register. For example, `LDW BC, #0x1234` loads
`0x12` into `B` and `0x34` into `C`.
|*)

Variant regpair : Type := BC | DE | HL | AF.

Definition unpair (p : regpair) : reg8 * reg8 :=
  match p with
  | BC => (B, C)
  | DE => (D, E)
  | HL => (H, L)
  | AF => (A, F)
  end.

(*|
It's a little cumbersome to have to differentiate between `reg8`s,
`reg16`s, and `regpair`s all the time. To make life easier, we define
a unified `reg` type that can handle all three. The `reg` type is
indexed by the value it holds, so we can restrict its inhabitants
to contexts that expect 8-bit or 16-bit registers. Finally, we can
implicitly coerce any `reg8`, `reg16`, or `regpair` into a `reg`.
|*)

Variant reg : Type -> Type :=
  | Reg8 : reg8 -> reg u8
  | Reg16 : reg16 -> reg u16
  | RegPair : regpair -> reg u16.


Variant flag : Type :=
  | FZ    (* Zero *) 
  | FN    (* Negative *)
  | FH    (* Half-carry *)
  | FC.   (* Carry *)

Definition flagmask (f : flag) : byte :=
  match f with
  | FZ => 0x80
  | FN => 0x40
  | FH => 0x20
  | FC => 0x10
  end.

Coercion Reg8 : reg8 >-> reg.
Coercion Reg16 : reg16 >-> reg.
Coercion RegPair : regpair >-> reg.

Definition reg_of_reg8 : Asm.opreg8 -> reg8
  := fun r => match r with
    | Asm.A => A
    | Asm.B => B
    | Asm.C => C
    | Asm.D => D
    | Asm.E => E
    | Asm.H => H
    | Asm.L => L
  end.

Definition reg_of_bcdehl : Asm.bcdehl -> regpair 
  := fun r => match r with
    | Asm.BC => BC
    | Asm.DE => DE
    | Asm.HL => HL
  end.

Definition reg_of_preg16 : Asm.preg16 -> reg u16 
  := fun r => match r with
    | Asm.InP r => reg_of_bcdehl r
    | Asm.SP => SP
  end.

Definition reg_of_qreg16 : Asm.qreg16 -> regpair
  := fun r => match r with
    | Asm.InQ r => reg_of_bcdehl r
    | Asm.AF => AF
  end.

Coercion reg_of_reg8 : Asm.opreg8 >-> reg8.
Coercion reg_of_bcdehl : Asm.bcdehl >-> regpair.
Coercion reg_of_preg16 : Asm.preg16 >-> reg.
Coercion reg_of_qreg16 : Asm.qreg16 >-> regpair.

(* Processor Events *)

Variant CpuE : Type -> Type :=
  | GetReg8 : reg8 -> CpuE u8
  | SetReg8 : reg8 -> u8 -> CpuE unit
  | GetReg16 : reg16 -> CpuE u16
  | SetReg16 : reg16 -> u16 -> CpuE unit
  | SetIme : bool -> CpuE unit.

Section CpuE.
Context {E: Type -> Type}.
Context `{HasCpu : CpuE -< E}.

Definition getreg {i} (r : reg i) : itree E i :=
  match r with
  | Reg8 r =>
      trigger (GetReg8 r)
  | Reg16 r =>
      trigger (GetReg16 r)
  | RegPair p =>
      let (r, s) := unpair p in
      hi <- trigger (GetReg8 r) ;;
      lo <- trigger (GetReg8 s) ;;
      ret (Uint16.concat hi lo)
  end.

Definition setreg {i} (r : reg i) : i -> itree E unit :=
  match r with
  | Reg8 r => fun x =>
      trigger (SetReg8 r x)
  | Reg16 r => fun x =>
      trigger (SetReg16 r x)
  | RegPair p => fun x =>
      let (r, s) := unpair p in
      trigger (SetReg8 r (Uint16.hi x)) ;; 
      trigger (SetReg8 s (Uint16.lo x))
  end.

Definition setime : bool -> itree E unit := embed SetIme.

End CpuE.

(* Memory Events *)

Variant MemE : Type -> Type :=
  | MemRead  : u16 -> MemE u8
  | MemWrite : u16 -> u8 -> MemE unit.

Section MemE.
Context {E: Type -> Type}.
Context `{HasMem : MemE -< E}.

Definition memread : u16 -> itree E u8 := embed MemRead.
Definition memwrite : u16 -> u8 -> itree E unit := embed MemWrite.

End MemE.

(* Semantics *)

Section Semantics.
Context {E : Type -> Type}.
Context {HasCpu : CpuE -< E}.
Context {HasMem : MemE -< E}.

(*|
Load or store a byte at the address pointed to by a given 16-bit register.
|*)

Definition load : reg u16 -> itree E u8
  := fun r => addr <- getreg r ;; memread addr.

Definition store : reg u16 -> u8 -> itree E unit
  := fun r x => addr <- getreg r ;; memwrite addr x.

(*|
Increment or decrement the value in a register.
|*)

Definition inc {i} : reg i -> itree E unit
  := fun r => match r with
      | Reg8 r => x <- getreg r ;; setreg r (Uint8.succ x)
      | Reg16 r | RegPair r => x <- getreg r ;; setreg r (Uint16.succ x)
    end.

Definition dec {i} : reg i -> itree E unit
  := fun r => match r with
      | Reg8 r => x <- getreg r ;; setreg r (Uint8.pred x)
      | Reg16 r | RegPair r => x <- getreg r ;; setreg r (Uint16.pred x)
    end.

(*|
Push or pop a byte from the stack. The stack grows downward. The stack
pointer always points to the last value pushed.
|*)

Definition push : u8 -> itree E unit
  := fun x => dec SP ;; store SP x.

Definition pop : itree E u8
  := x <- load SP ;; inc SP ;; ret x.

(*|
Push or pop a 16-bit value from the stack. Note that 16-bit words are
stored in little-endian order on the stack; the high byte is pushed first.
|*)

Definition push16 : u16 -> itree E unit 
  := fun x => push (Uint16.hi x) ;; push (Uint16.lo x).

Definition pop16 : itree E u16
  := lo <- pop ;; hi <- pop ;; ret (Uint16.concat hi lo).

(*|
The `readhi` and `writehi` instructions are specializations of `memread`
and `memwrite` that read and write to the highest page.  These functions
take an 8-bit value `x` and read/write to address `0xFF00 + x`. See
documentation for the `LDH` instruction.
|*)

Definition readhi : u8 -> itree E u8
  := fun addr => memread (Uint16.concat 0xFF addr).

Definition writehi : u8 -> u8 -> itree E unit
  := fun addr => memwrite (Uint16.concat 0xFF addr).

Definition getflag (f : flag) : itree E bool :=
  x <- getreg F ;; 
  let mask := flagmask f in
  ret (x .& mask =? mask)%u8.

Definition setflag : flag -> bool -> itree E unit
  := fun f v => match v with
    | true => x <- getreg F ;; setreg F (x .| flagmask f)%u8
    | false => x <- getreg F ;; setreg F (x .& (.~ flagmask f))%u8
  end.
  

(* Instruction Semantics *)

Parameter denote_adc : u8 -> itree E unit.
Parameter denote_add : u8 -> itree E unit.
Parameter denote_addp : u16 -> itree E unit.
Parameter denote_addsp : u8 -> itree E unit.
Parameter denote_cp : u8 -> itree E unit.
Parameter denote_sbc : u8 -> itree E unit.
Parameter denote_sub : u8 -> itree E unit.
Parameter denote_bit : Asm.opbit -> u8 -> itree E unit.

(* AND A, r  /  AND A, u8  /  AND A, [HL] *)
Definition denote_and (x : u8) : itree E unit :=
  a <- getreg A ;;
  setreg A (a .& x)%u8 ;;
  setflag FZ (a .& x =? 0)%u8 ;;
  setflag FN false ;;
  setflag FH true ;;
  setflag FC false.

(* OR A, r  /  OR A, u8  /  OR A, [HL] *)
Definition denote_or (x : u8) : itree E unit :=
  a <- getreg A ;;
  setreg A (a .| x)%u8 ;;
  setflag FZ (a .| x =? 0)%u8 ;;
  setflag FN false ;;
  setflag FH false ;;
  setflag FC false.

(* XOR A, r  /  XOR A, u8  /  XOR A, [HL] *)
Definition denote_xor (x : u8) : itree E unit :=
  a <- getreg A ;;
  setreg A (a .^ x)%u8 ;;
  setflag FZ (a .^ x =? 0)%u8 ;;
  setflag FN false ;;
  setflag FH false ;;
  setflag FC false.

(* CCF - Complement carry flag *)
Definition denote_ccf :=
  x <- getflag FC ;;
  setflag FN false ;;
  setflag FH false ;;
  setflag FC (negb x).

(* SCF - Set carry flag *)
Definition denote_scf :=
  setflag FN false ;;
  setflag FH false ;;
  setflag FC true.

(* CPL - Complement A *)
Definition denote_cpl :=
  x <- getreg A ;;
  setreg A (.~ x)%u8 ;;
  setflag FN true ;;
  setflag FH true.

(* Convert a [bool] to a [byte]. *)

Definition boolbit : bool -> u8
  := fun b => if b then 0x01 else 0x00.

(* RL - Rotate left through carry *)
Definition denote_rl (old : u8) : itree E u8 :=
  c <- getflag FC ;;
  let new := (old << 1 .| boolbit c)%u8 in
  setflag FZ (new =? 0)%u8 ;;
  setflag FN false ;;
  setflag FH false ;;
  setflag FC (old .& 0x80 =? 0x80)%u8 ;;
  ret new.

(* RLA - Rotate left through carry (register A). *)
Parameter denote_rla : u8 -> itree E u8.

(* RLC - Rotate left *)
Definition denote_rlc (old : u8) : itree E u8 :=
  let new := (old << 1 .| boolbit (old .& 0x80 =? 0x80))%u8 in
  setflag FZ (new =? 0)%u8 ;;
  setflag FN false ;;
  setflag FH false ;;
  setflag FC (old .& 0x80 =? 0x80)%u8 ;;
  ret new.

(* RLCA - Rotate left (register A) *)
Parameter denote_rlca : u8 -> itree E u8.

(* SLA - Shift left *)
Parameter denote_sla : u8 -> itree E u8.

(* SRA - Arithmetic shift right *)
Parameter denote_sra : u8 -> itree E u8.

(* SRL - Logical shift right *)
Parameter denote_srl : u8 -> itree E u8.


(* RST u8 *)
Definition denote_rst (addr : Asm.oprst) : itree E unit
  := setreg PC (Uint16.concat 0x00 (Asm.oprst_to_u8 addr)).

Definition denote_swap (x : u8) :=
  setflag FZ (x =? 0)%u8 ;;
  setflag FN false ;;
  setflag FH false ;;
  setflag FC false ;;
  ret (x >> 0x04 .| x << 0x04)%u8.


Parameter denote_daa : itree E unit.

Definition satisfies : Asm.opcond -> itree E bool
  := fun c => match c with
    | Asm.FZ  => getflag FZ
    | Asm.FNZ => x <- getflag FZ ;; ret (negb x)
    | Asm.FC  => getflag FC
    | Asm.FNC => x <- getflag FC ;; ret (negb x)
   end.

Definition denote_instr : Asm.instruction -> itree E unit
  := fun instr => match instr with
  | $[ADC A, #x] =>
      denote_adc x
  | $[ADC A, [HL]] =>
      load HL >>= denote_adc
  | $[ADC A, r] =>
      getreg r >>= denote_adc
  | $[ADD A, #x] =>
      denote_add x
  | $[ADD A, [HL]] =>
      load HL >>= denote_add
  | $[ADD HL, r] =>
      getreg r >>= denote_addp
  | $[ADD A, r] =>
      getreg r >>= denote_add
  | $[ADD SP, #x] =>
      denote_addsp x
  | $[AND A, #x] =>
      denote_and x
  | $[AND A, [HL]] =>
      load HL >>= denote_and
  | $[AND A, r] =>
      getreg r >>= denote_and
  | $[BIT b, [HL]] =>
      load HL >>= denote_bit b
  | $[BIT b, r] =>
      getreg r >>= denote_bit b
  | $[CALL #addr] =>
      getreg PC >>= push16 ;; setreg PC addr
  | $[CALL cc, #addr] =>
      b <- satisfies cc ;;
      match b with
        | true  => getreg PC >>= push16 ;; setreg PC addr
        | false => ret tt
      end
  | $[CCF] =>
      denote_ccf
  | $[CPL] =>
      denote_cpl
  | $[CP A, #x] =>
      denote_cp x
  | $[CP A, [HL]] =>
      load HL >>= denote_cp
  | $[CP A, r] =>
      getreg r >>= denote_cp
  | $[DAA] =>
      denote_daa
  | $[DEC [HL]] =>
      x <- load HL ;; store HL (Uint8.pred x)
  | $[DECW r] =>
      dec r
  | $[DEC r] =>
      dec r
  | $[DI] =>
      setime false
  | $[EI] =>
      setime true
  | $[HALT] =>
      ret tt (* TODO *)
  | $[INC [HL]] =>
      x <- load HL ;; store HL (Uint8.succ x)
  | $[INCW r] =>
      inc r
  | $[INC r] =>
      inc r
  | $[JP #addr] =>
      setreg PC addr
  | $[JP cc, #addr] =>
      b <- satisfies cc ;;
      match b with
        | true  => setreg PC addr
        | false => ret tt
      end
  | $[JP HL] =>
      getreg HL >>= setreg PC
  | $[JR #_] =>
      ret tt (* TODO *)
  | $[JR _, #_] =>
      ret tt (* TODO *)
  | $[LD A, [BC]] =>
      load BC >>= setreg A
  | $[LD A, [DE]] =>
      load DE >>= setreg A
  | $[LD A, [HL+]] =>
      load HL >>= setreg A ;; inc HL
  | $[LD A, [HL-]] =>
      load HL >>= setreg A ;; dec HL
  | $[LD A, [#x]] =>
      memread x >>= setreg A
  | $[LDH A, [C]] =>
      c <- getreg C ;;
      v <- memread (Uint16.concat 0xFF c) ;;
      setreg A v
  | $[LDH A, [#x]] =>
      v <- memread (Uint16.concat 0xFF x) ;;
      setreg A v
  | $[LDH [C], A] =>
      c <- getreg C ;;
      v <- getreg A ;;
      memwrite (Uint16.concat 0xFF c) v
  | $[LDH [#x], A] =>
      v <- getreg A ;;
      memwrite (Uint16.concat 0xFF x) v
  | $[LD [HL], #x] =>
      store HL x
  | $[LD [HL], r] =>
      getreg r >>= store HL
  | $[LDW r, #x] =>
      setreg r x
  | $[LD r, #x] =>
      setreg r x
  | $[LD r, [HL]] =>
      load HL >>= setreg r
  | $[LD r, s] =>
      getreg s >>= setreg r
  | $[LD [BC], A] =>
      getreg A >>= store BC
  | $[LD [DE], A] =>
      getreg A >>= store DE
  | $[LD [HL+], A] =>
      getreg A >>= store HL ;; inc HL
  | $[LD [HL-], A] =>
      getreg A >>= store HL ;; dec HL
  | $[LDW HL, SP + #_] =>
      ret tt (* TODO *)
  | $[LDW [#x], SP] =>
      ret tt (* TODO *)
      (*
      sp <- getreg SP ;;
      memwrite x (Uint16.hi sp) ;;
      memwrite (Uint16.succ x) (Uint16.lo sp)
      *)
  | $[LDW SP, HL] =>
      getreg HL >>= setreg SP
  | $[LD [#x], A] =>
      getreg A >>= memwrite x
  | $[NOP] =>
      ret tt
  | $[OR A, #x] =>
      denote_or x
  | $[OR A, [HL]] =>
      load HL >>= denote_or
  | $[OR A, r] =>
      getreg r >>= denote_or
  | $[POP r] =>
      pop16 >>= setreg r
  | $[PUSH r] =>
      getreg r >>= push16
  | $[RLCA] =>
      ret tt (* TODO *)
  | $[RES b, [HL]] =>
      x <- load HL ;;
      store HL (x .& .~ Asm.opbit_mask b)%u8
  | $[RES b, r] =>
      x <- getreg r ;;
      setreg r (x .& .~ Asm.opbit_mask b)%u8
  | $[RET] =>
      pop16 >>= setreg PC
  | $[RET cc] =>
      b <- satisfies cc ;;
      match b with
        | true  => pop16 >>= setreg PC
        | false => ret tt
      end
  | $[RETI] =>
      setime true ;;
      pop16 >>= setreg PC
  | $[RLA] =>
      ret tt (* TODO *)
  | $[RLC [HL]] =>
      x <- load HL ;;
      denote_rlc x >>= store HL
  | $[RLC r] =>
      x <- getreg r ;;
      denote_rlc x >>= setreg r
  | $[RL [HL]] =>
      x <- load HL ;;
      denote_rl x >>= store HL
  | $[RL r] =>
      x <- getreg r ;;
      denote_rl x >>= setreg r
  | $[RRA] =>
      ret tt (* TODO *)
  | $[RRCA] =>
      ret tt (* TODO *)
  | $[RRC [HL]] =>
      ret tt (* TODO *)
  | $[RRC _] =>
      ret tt (* TODO *)
  | $[RR [HL]] =>
      ret tt (* TODO *)
  | $[RR _] =>
      ret tt (* TODO *)
  | $[RST addr] =>
      getreg PC >>= push16 ;; denote_rst addr
  | $[SBC A, #x] =>
      denote_sbc x
  | $[SBC A, [HL]] =>
      load HL >>= denote_sbc
  | $[SBC A, r] =>
      getreg r >>= denote_sbc
  | $[SCF] =>
      denote_scf
  | $[SET b, [HL]] =>
      x <- load HL ;;
      store HL (x .| Asm.opbit_mask b)%u8
  | $[SET b, r] =>
      x <- getreg r ;;
      setreg r (x .| Asm.opbit_mask b)%u8
  | $[SLA [HL]] =>
      x <- load HL ;;
      denote_sla x >>= store HL
  | $[SLA r] =>
      x <- getreg r ;;
      denote_sla x >>= setreg r
  | $[SRA [HL]] =>
      x <- load HL ;;
      denote_sra x >>= store HL
  | $[SRA r] =>
      x <- getreg r ;;
      denote_sra x >>= setreg r
  | $[SRL [HL]] =>
      x <- load HL ;;
      denote_srl x >>= store HL
  | $[SRL r] =>
      x <- getreg r ;;
      denote_srl x >>= setreg r
  | $[STOP] =>
      ret tt (* TODO *)
  | $[SUB A, #x] =>
      denote_sub x
  | $[SUB A, [HL]] =>
      load HL >>= denote_sub
  | $[SUB A, r] =>
      getreg r >>= denote_sub
  | $[SWAP [HL]] =>
      x <- load HL ;;
      denote_swap x >>= store HL
  | $[SWAP r] =>
      x <- getreg r ;;
      denote_swap x >>= setreg r
  | $[XOR A, #x] =>
      denote_xor x
  | $[XOR A, [HL]] =>
      load HL >>= denote_xor
  | $[XOR A, r] =>
      getreg r >>= denote_xor
  | $[ILLEGAL _] =>
      ret tt (* Illegal opcode; behave as if it's a NOP *)
  end.

(** [handle_fetch] is a handler that converts [Fetch] events into
    [MemRead] events using the current PC. *)

Definition handle_fetch : FetchE ~> itree E :=
  fun _ e => match e with
    | Fetch => x <- load PC ;; inc PC ;; ret x
  end.

Definition denote_fetch : itree E instruction
  := interp handle_fetch asm_decode.

Definition denote_step : itree E unit := 
  op <- denote_fetch ;;
  denote_instr op.

End Semantics.
