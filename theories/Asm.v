From GameBoy.Stdint Require Import Stdint.

(*|
This module defines the syntax for SM83 assembly programs.  It takes
inspiration from "Coq: The World's Best Macro Assembler?"  [@kennedy2013],
and provides definitions that allow for the creation of assembly programs
directly in Rocq. For example:

```
$[
  WITH waitvblank done,
    waitvblank:;
      LDH A, [#0x44];
      CP A, #144;
      JP FC, #waitvblank;
    done:;
      HALT
]
```

# Instructions

This definition of `instruction` is *precise*. We do not allow for the
construction of invalid assembly instructions.  For example, `INC` only
accepts `BC`, `DE`, `HL`, and `SP` as operands; we make it impossible to
construct the invalid `INC AF` instruction. To accomplish this, we define
several register subsets. 16-bit registers are divided into three subsets:
`preg16`, `qreg16`, and `sreg16`.

- *preg16*: This subset consists of the registers `BC`, `DE`, `HL` and
  `SP`. These are the possible 16-bit register operands for `INC`, `DEC`,
  `ADD`, and `LD`.

- *qreg16*: This subset consists of the registers `BC`, `DE`, `HL`, and
  `AF`. These are the possible 16-bit operands for `PUSH` and `POP`.

- *sreg16*: This subset is a special set used for 16-bit indirect loads
  (e.g. `LD A, [BC]`). It consists of `BC`, `DE`, `HL+`, and `HL-`, where
  `HL+` and `HL-` are post-increments and post-decrements on `HL`.

Each register is defined *once*. We use the injectors `InB`, `InP`, `InQ`,
and `InS` to inject smaller register subsets into larger ones. We then
can use Rocq coercions to hide the injectors so that they're never seen.
This allows us to write `BC` for any `preg16`, `qreg16`, or `sreg16`.

## Instruction Suffixes

Mnemonics are extremely overloaded. For example, the `ADD` instruction
compiles to one of five different opcodes depending on the arguments
it's given. In Rocq, we define five different constructors for the
`ADD` instruction, and distinguish each one with a different suffix.
Possible suffixes are:

| ------ | ----------------------------------------------------------- |
| Suffix | Operand                                                     |
| ------ | ----------------------------------------------------------- |
| A      | The register `A`.                                           |
| C      | The register `C`.                                           |
| I      | An 8-bit immediate operand.                                 |
| J      | The 16-bit register `HL`.                                   |
| K      | The 16-bit register `SP`.                                   |
| L      | A 16-bit immediate operand.                                 |
| M      | A store to `[HL]`.                                          |
| P      | A `preg16` register: `BC`, `DE`, `HL`, or `SP`.             |
| Q      | A `qreg16` register: `BC`, `DE`, `HL`, or `AF`.             |
| R      | An 8-bit register: `A`, `B`, `C`, `D`, `E`, `H`, or `L`.    |
| S      | A `sreg16` store to `[BC]`, `[DE]`, `[HL+]`, or `[HL-]`.    |
| ------ | ----------------------------------------------------------- |
|*)

(* 8-bit register operands. *)
Variant opreg8 := A | B | C | D | E | H | L.

(* 16-bit register operands. *)
Variant bcde := BC | DE.
Variant bcdehl := InB (r : bcde) | HL.
Variant preg16 := InP (r : bcdehl) | SP.
Variant qreg16 := InQ (r : bcdehl) | AF.
Variant sreg16 := InS (r : bcde) | HLI | HLD.

Coercion InB : bcde >-> bcdehl.
Coercion InP : bcdehl >-> preg16.
Coercion InQ : bcdehl >-> qreg16.
Coercion InS : bcde >-> sreg16.

(* Condition codes for CALL, JP, JR, and RET. *)
Variant opcond := FZ | FNZ | FC | FNC.

(* Possible target addresses for RST. *)
Variant oprst := R00 | R08 | R10 | R18 | R20 | R28 | R30 | R38.

(* Bit index for BIT, RES, and SET. B0 is the LSB. *)
Variant opbit := B0 | B1 | B2 | B3 | B4 | B5 | B6 | B7.

(* Illegal opcodes. *)
Variant opillegal :=
  UD3 | UDB | UDD | UE3 | UE4 | UEB | UEC | UED | UF4 | UFC | UFD.

(* Non-branching instructions. *)
Variant instruction :=
  | Iadc_I : u8 -> instruction                    (* ADC A, #u8 *)
  | Iadc_M : instruction                          (* ADC A, [HL] *)
  | Iadc_R : opreg8 -> instruction                (* ADC A, r8 *)
  | Iadd_I : u8 -> instruction                    (* ADD A, #u8 *)
  | Iadd_K : i8 -> instruction                    (* ADD SP, #i8 *)
  | Iadd_M : instruction                          (* ADD A, [HL] *)
  | Iadd_P : preg16 -> instruction                (* ADD HL, r16 *)
  | Iadd_R : opreg8 -> instruction                (* ADD A, r8 *)
  | Iand_I : u8 -> instruction                    (* AND A, #u8 *)
  | Iand_M : instruction                          (* AND A, [HL] *)
  | Iand_R : opreg8 -> instruction                (* AND A, r8 *)
  | Ibit_M : opbit -> instruction                 (* BIT b, [HL] *)
  | Ibit_R : opbit -> opreg8 -> instruction       (* BIT b, r8 *)
  | Icall : option opcond -> u16 -> instruction   (* CALL cc, u16 *)
  | Iccf : instruction                            (* CCF *)
  | Icp_I : u8 -> instruction                     (* CP A, #u8 *)
  | Icp_M : instruction                           (* CP A, [HL] *)
  | Icp_R : opreg8 -> instruction                 (* CP A, r8 *)
  | Icpl : instruction                            (* CPL *)
  | Idaa : instruction                            (* DAA *)
  | Idec_M : instruction                          (* DEC [HL] *)
  | Idec_P : preg16 -> instruction                (* DEC r16 *)
  | Idec_R : opreg8 -> instruction                (* DEC r8 *)
  | Idi : instruction                             (* DI *)
  | Iei : instruction                             (* EI *)
  | Ihalt : instruction                           (* HALT *)
  | Iinc_M : instruction                          (* INC [HL] *)
  | Iinc_P : preg16 -> instruction                (* INC r16 *)
  | Iinc_R : opreg8 -> instruction                (* INC r8 *)
  | Ijp : option opcond -> u16 -> instruction     (* JP cc, u16 *)
  | Ijphl : instruction                           (* JP HL *)
  | Ijr : option opcond -> i8 -> instruction      (* JR cc, #i8 *)
  | Ild_AS : sreg16 -> instruction                (* LD A, [r16] *)
  | Ild_AX : u16 -> instruction                   (* LD A, [u16] *)
  | Ild_JK : u8 -> instruction                    (* LDW HL, SP+#u8 *)
  | Ild_KJ : instruction                          (* LDW SP, HL *)
  | Ild_LK : u16 -> instruction                   (* LDW [u16], SP *)
  | Ild_MI : u8 -> instruction                    (* LD [HL], #u8 *)
  | Ild_MR : opreg8 -> instruction                (* LD [HL], r8 *)
  | Ild_PL : preg16 -> u16 -> instruction         (* LDW r16, u16 *)
  | Ild_RI : opreg8 -> u8 -> instruction          (* LD r8, #u8 *)
  | Ild_RM : opreg8 -> instruction                (* LD r8, [HL] *)
  | Ild_RR : opreg8 -> opreg8 -> instruction      (* LD r8, r8 *)
  | Ild_SA : sreg16 -> instruction                (* LD [r16], A *)
  | Ild_XA : u16 -> instruction                   (* LD [u16], A *)
  | Ildh_AC : instruction                         (* LDH A, [C] *)
  | Ildh_AI : u8 -> instruction                   (* LDH A, [#u8] *)
  | Ildh_CA : instruction                         (* LDH [C], A *)
  | Ildh_IA : u8 -> instruction                   (* LDH [#u8], A *)
  | Inop : instruction                            (* NOP *)
  | Ior_I : u8 -> instruction                     (* OR A, #u8 *)
  | Ior_M : instruction                           (* OR A, [HL] *)
  | Ior_R : opreg8 -> instruction                 (* OR A, r8 *)
  | Ipop : qreg16 -> instruction                  (* POP r16 *)
  | Ipush : qreg16 -> instruction                 (* PUSH r16 *)
  | Ires_M : opbit -> instruction                 (* RES b, [HL] *)
  | Ires_R : opbit -> opreg8 -> instruction       (* RES b, r8 *)
  | Iret : option opcond -> instruction           (* RET cc *)
  | Ireti : instruction                           (* RETI *)
  | Irl_M : instruction                           (* RL [HL] *)
  | Irl_R : opreg8 -> instruction                 (* RL r8 *)
  | Irla : instruction                            (* RLA *)
  | Irlc_M : instruction                          (* RLC [HL] *)
  | Irlc_R : opreg8 -> instruction                (* RLC r8 *)
  | Irlca : instruction                           (* RLCA *)
  | Irr_M : instruction                           (* RR [HL] *)
  | Irr_R : opreg8 -> instruction                 (* RR r8 *)
  | Irra : instruction                            (* RRA *)
  | Irrc_M : instruction                          (* RRC [HL] *)
  | Irrc_R : opreg8 -> instruction                (* RRC r8 *)
  | Irrca : instruction                           (* RRCA *)
  | Irst : oprst -> instruction                   (* RST u8 *)
  | Isbc_I : u8 -> instruction                    (* SBC A, #u8 *)
  | Isbc_M : instruction                          (* SBC A, [HL] *)
  | Isbc_R : opreg8 -> instruction                (* SBC A, r8 *)
  | Iscf : instruction                            (* SCF *)
  | Iset_M : opbit -> instruction                 (* SET b, [HL] *)
  | Iset_R : opbit -> opreg8 -> instruction       (* SET b, r8 *)
  | Isla_M : instruction                          (* SLA [HL] *)
  | Isla_R : opreg8 -> instruction                (* SLA r8 *)
  | Isra_M : instruction                          (* SRA [HL] *)
  | Isra_R : opreg8 -> instruction                (* SRA r8 *)
  | Isrl_M : instruction                          (* SRL [HL] *)
  | Isrl_R : opreg8 -> instruction                (* SRL r8 *)
  | Istop : instruction                           (* STOP *)
  | Isub_I : u8 -> instruction                    (* SUB A, #u8 *)
  | Isub_M : instruction                          (* SUB A, [HL] *)
  | Isub_R : opreg8 -> instruction                (* SUB A, r8 *)
  | Iswap_M : instruction                         (* SWAP [HL] *)
  | Iswap_R : opreg8 -> instruction               (* SWAP r8 *)
  | Ixor_I : u8 -> instruction                    (* XOR A, #u8 *)
  | Ixor_M : instruction                          (* XOR A, [HL] *)
  | Ixor_R : opreg8 -> instruction                (* XOR A, r8 *)
  | Iillegal : opillegal -> instruction.

(*|
# Programs

The definition of programs is similar to the one provided in
[@kennedy2013].  Programs are sequences of instructions and labels. Labels
may be introduced abstractly using `Pwith`, in a fashion resembling
higher-order abstract syntax.
|*)

Inductive program :=
  | Pinstr : instruction -> program
  | Plabel : u16 -> program
  | Pseq : program -> program -> program
  | Pwith : (u16 -> program) -> program.

Coercion Pinstr : instruction >-> program.

(*|
# Integer Conversions and Notations for Operands
|*)

Definition opbit_to_u8 : opbit -> u8 :=
  fun i => match i with
    | B0 => 0%u8
    | B1 => 1%u8
    | B2 => 2%u8
    | B3 => 3%u8
    | B4 => 4%u8
    | B5 => 5%u8
    | B6 => 6%u8
    | B7 => 7%u8
  end.

Definition opbit_of_u8 : u8 -> option opbit :=
  fun b => match b with
    | 0%u8 => Some B0
    | 1%u8 => Some B1
    | 2%u8 => Some B2
    | 3%u8 => Some B3
    | 4%u8 => Some B4
    | 5%u8 => Some B5
    | 6%u8 => Some B6
    | 7%u8 => Some B7
    | _%u8 => None
  end.

Definition opbit_mask : opbit -> u8 :=
  fun i => match i with
    | B0 => 0x01%u8
    | B1 => 0x02%u8
    | B2 => 0x04%u8
    | B3 => 0x08%u8
    | B4 => 0x10%u8
    | B5 => 0x20%u8
    | B6 => 0x40%u8
    | B7 => 0x80%u8
  end.

Definition oprst_to_u8 : oprst -> u8 :=
  fun r => match r with
    | R00 => 0x00%u8
    | R08 => 0x08%u8
    | R10 => 0x10%u8
    | R18 => 0x18%u8
    | R20 => 0x20%u8
    | R28 => 0x28%u8
    | R30 => 0x30%u8
    | R38 => 0x38%u8
  end.

Definition oprst_of_u8 : u8 -> option oprst :=
  fun r => match r with
    | 0x00%u8 => Some R00
    | 0x08%u8 => Some R08
    | 0x10%u8 => Some R10
    | 0x18%u8 => Some R18
    | 0x20%u8 => Some R20
    | 0x28%u8 => Some R28
    | 0x30%u8 => Some R30
    | 0x38%u8 => Some R38
    | _ => None
  end.

Definition opillegal_to_u8 : opillegal -> u8 :=
  fun x => match x with
    | UD3 => 0xD3%u8
    | UDB => 0xDB%u8
    | UDD => 0xDD%u8
    | UE3 => 0xE3%u8
    | UE4 => 0xE4%u8
    | UEB => 0xEB%u8
    | UEC => 0xEC%u8
    | UED => 0xED%u8
    | UF4 => 0xF4%u8
    | UFC => 0xFC%u8
    | UFD => 0xFD%u8
  end.

Definition opillegal_of_u8 : u8 -> option opillegal :=
  fun x => match x with
    | 0xD3%u8 => Some UD3
    | 0xDB%u8 => Some UDB
    | 0xDD%u8 => Some UDD
    | 0xE3%u8 => Some UE3
    | 0xE4%u8 => Some UE4
    | 0xEB%u8 => Some UEB
    | 0xEC%u8 => Some UEC
    | 0xED%u8 => Some UED
    | 0xF4%u8 => Some UF4
    | 0xFC%u8 => Some UFC
    | 0xFD%u8 => Some UFD
    | _ => None
  end.

(* Number notation for `opbit`. *)

Declare Scope opbit_scope.
Delimit Scope opbit_scope with opbit.
Bind Scope opbit_scope with opbit.

Definition opbit_to_num : opbit -> Number.int :=
  fun r => Uint8.to_num (opbit_to_u8 r).

Definition opbit_of_num : Number.int -> option opbit :=
  fun n => match Uint8.of_num n with
  | None => None
  | Some x => opbit_of_u8 x
  end.

Number Notation opbit opbit_of_num opbit_to_num : opbit_scope.


(* Number notation for `oprst`. *)

Declare Scope oprst_scope.
Delimit Scope oprst_scope with oprst.
Bind Scope oprst_scope with oprst.

Definition oprst_to_hex_num : oprst -> Number.int :=
  fun r => Uint8.to_hex (oprst_to_u8 r).

Definition oprst_of_num : Number.int -> option oprst :=
  fun n => match Uint8.of_num n with
  | None => None
  | Some x => oprst_of_u8 x
  end.

Number Notation oprst oprst_of_num oprst_to_hex_num : oprst_scope.


(* Number notation for `opillegal`. *)

Declare Scope opillegal_scope.
Delimit Scope opillegal_scope with opillegal.
Bind Scope opillegal_scope with opillegal.

Definition opillegal_to_hex_num : opillegal -> Number.int :=
  fun r => Uint8.to_hex (opillegal_to_u8 r).

Definition opillegal_of_num : Number.int -> option opillegal :=
  fun n => match Uint8.of_num n with
  | None => None
  | Some x => opillegal_of_u8 x
  end.

Number Notation opillegal opillegal_of_num opillegal_to_hex_num : opillegal_scope.


(*|
# Instruction Notation

The assembly notation syntax does a pretty good job of resembling
Z80-style syntax, with a few exceptions. 

First, all immediate 8-bit and 16-bit values are prefixed with `#`
(e.g. `ADD A, #42`). Doing so helps the notation parser resolve ambiguity
between register operands and immediate operands. Second, a few mnemonics
are suffixed with a `W` in order to distinguish between their 8-bit and
16-bit versions (the `W` stands for "Word").  They are: `INC`/`INCW`,
`DEC`/`DECW`, and `LD`/`LDW`.  Finally, it's worth noting that we don't
bother with special syntax for `opcond`. The classic Z80-style syntax
for a conditional jump looks something like: `JP Z, label`, but in our
syntax, it's written as `JP FZ, #label` using the Rocq term `FZ`.
|*)

Declare Custom Entry asm.

Notation "$[ x ]" := x
  (at level 0, x custom asm at level 0, format "$[ x ]").

Notation "( x )" := x
  (in custom asm at level 0, x custom asm at level 200).

Notation "'ADC' 'A' ',' r" := (Iadc_R r)
  (in custom asm at level 0, r constr at level 0,
    format "ADC  A ,  r").

Notation "'ADC' 'A' ',' '#' n" := (Iadc_I n)
  (in custom asm at level 0, n constr at level 0,
    format "ADC  A ,  # n").

Notation "'ADC' 'A' ',' '[' 'HL' ']'" := Iadc_M
  (in custom asm at level 0,
    format "ADC  A ,  [ HL ]").

Notation "'ADD' 'A' ',' r" := (Iadd_R r)
  (in custom asm at level 0, r constr at level 0,
    format "ADD  A ,  r").

Notation "'ADD' 'A' ',' '#' n" := (Iadd_I n)
  (in custom asm at level 0, n constr at level 0,
    format "ADD  A ,  # n").

Notation "'ADD' 'A' ',' '[' 'HL' ']'" := Iadd_M
  (in custom asm at level 0,
    format "ADD  A ,  [ HL ]").

Notation "'ADD' 'HL' ',' r" := (Iadd_P r)
  (in custom asm at level 0, r constr at level 0,
    format "ADD  HL ,  r").

Notation "'ADD' 'SP' ',' '#' n" := (Iadd_K n)
  (in custom asm at level 0, n constr at level 0,
    format "ADD  SP ,  # n").

Notation "'AND' 'A' ',' r" := (Iand_R r)
  (in custom asm at level 0, r constr at level 0,
    format "AND  A ,  r").

Notation "'AND' 'A' ',' '#' n" := (Iand_I n)
  (in custom asm at level 0, n constr at level 0,
    format "AND  A ,  # n").

Notation "'AND' 'A' ',' '[' 'HL' ']'" := Iand_M
  (in custom asm at level 0,
    format "AND  A ,  [ HL ]").

Notation "'BIT' b ',' r" := (Ibit_R b r)
  (in custom asm at level 0, b constr at level 0, r constr at level 0,
    format "BIT  b ,  r").

Notation "'BIT' b ',' '[' 'HL' ']'" := (Ibit_M b)
  (in custom asm at level 0, b constr at level 0,
    format "BIT  b ,  [ HL ]").

Notation "'CALL' '#' n" := (Icall None n)
  (in custom asm at level 0, n constr at level 0,
    format "CALL  # n").

Notation "'CALL' cc ',' '#' n" := (Icall (Some cc) n)
  (in custom asm at level 0, cc constr at level 0, n constr at level 0,
    format "CALL  cc ,  # n").

Notation "'CCF'" := Iccf
  (in custom asm at level 0).

Notation "'CP' 'A' ',' r" := (Icp_R r)
  (in custom asm at level 0, r constr at level 0,
    format "CP  A ,  r").

Notation "'CP' 'A' ',' '#' n" := (Icp_I n)
  (in custom asm at level 0, n constr at level 0,
    format "CP  A ,  # n").

Notation "'CP' 'A' ',' '[' 'HL' ']'" := Icp_M
  (in custom asm at level 0,
    format "CP  A ,  [ HL ]").

Notation "'CPL'" := Icpl
  (in custom asm at level 0).

Notation "'DAA'" := Idaa
  (in custom asm at level 0).

Notation "'DEC' r" := (Idec_R r)
  (in custom asm at level 0, r constr at level 1,
    format "DEC  r").

Notation "'DEC' '[' 'HL' ']'" := Idec_M
  (in custom asm at level 0, format "DEC  [ HL ]").

Notation "'DECW' r" := (Idec_P r)
  (in custom asm at level 0, r constr at level 1,
    format "DECW  r").

Notation "'DI'" := Idi
  (in custom asm at level 0).

Notation "'EI'" := Iei
  (in custom asm at level 0).

Notation "'HALT'" := Ihalt
  (in custom asm at level 0).

Notation "'INC' r" := (Iinc_R r)
  (in custom asm at level 0, r constr at level 1,
    format "INC  r").

Notation "'INC' '[' 'HL' ']'" := Iinc_M
  (in custom asm at level 0, format "INC  [ HL ]").

Notation "'INCW' r" := (Iinc_P r)
  (in custom asm at level 0, r constr at level 1,
    format "INCW  r").

Notation "'JP' '#' n" := (Ijp None n)
  (in custom asm at level 0, n constr at level 0,
    format "JP  # n").

Notation "'JP' cc ',' '#' n" := (Ijp (Some cc) n)
  (in custom asm at level 0, cc constr at level 0, n constr at level 0,
    format "JP  cc ,  # n").

Notation "'JP' 'HL'" := Ijphl
  (in custom asm at level 0, format "JP  HL").

Notation "'JR' '#' n" := (Ijr None n)
  (in custom asm at level 0, n constr at level 0,
    format "JR  # n").

Notation "'JR' cc ',' '#' n" := (Ijr (Some cc) n)
  (in custom asm at level 0, cc constr at level 0, n constr at level 0,
    format "JR  cc ,  # n").

Notation "'LD' r ',' s" := (Ild_RR r s)
  (in custom asm at level 0, r constr at level 0, s constr at level 0,
    format "LD  r ,  s").

Notation "'LD' r ',' '#' n" := (Ild_RI r n)
  (in custom asm at level 0, r constr at level 0, n constr at level 0,
    format "LD  r ,  # n").

Notation "'LD' r ',' '[' 'HL' ']'" := (Ild_RM r)
  (in custom asm at level 0, r constr at level 0,
    format "LD  r ,  [ HL ]").

Notation "'LD' '[' 'HL' ']' ',' r" := (Ild_MR r)
  (in custom asm at level 0, r constr at level 0,
    format "LD  [ HL ] ,  r").

Notation "'LD' '[' 'HL' ']' ',' # n" := (Ild_MI n)
  (in custom asm at level 0, n constr at level 0,
    format "LD  [ HL ] ,  # n").

Notation "'LDW' r ',' '#' n" := (Ild_PL r n)
  (in custom asm at level 0, r constr at level 0, n constr at level 0,
    format "LDW  r ,  # n").

Notation "'LD' 'A' ',' '[' 'BC' ']'" := (Ild_AS (InS BC))
  (in custom asm at level 0, format "LD  A ,  [ BC ]").

Notation "'LD' 'A' ',' '[' 'DE' ']'" := (Ild_AS (InS DE))
  (in custom asm at level 0, format "LD  A ,  [ DE ]").

Notation "'LD' 'A' ',' '[' 'HL+' ']'" := (Ild_AS HLI)
  (in custom asm at level 0, format "LD  A ,  [ HL+ ]").

Notation "'LD' 'A' ',' '[' 'HL-' ']'" := (Ild_AS HLD)
  (in custom asm at level 0, format "LD  A ,  [ HL- ]").

Notation "'LD' '[' 'BC' ']' ',' 'A'" := (Ild_SA (InS BC))
  (in custom asm at level 0, format "LD  [ BC ] ,  A").

Notation "'LD' '[' 'DE' ']' ',' 'A'" := (Ild_SA (InS DE))
  (in custom asm at level 0, format "LD  [ DE ] ,  A").

Notation "'LD' '[' 'HL+' ']' ',' 'A'" := (Ild_SA HLI)
  (in custom asm at level 0, format "LD  [ HL+ ] ,  A").

Notation "'LD' '[' 'HL-' ']' ',' 'A'" := (Ild_SA HLD)
  (in custom asm at level 0, format "LD  [ HL- ] ,  A").

Notation "'LD' 'A' ',' '[' '#' n ']'" := (Ild_AX n)
  (in custom asm at level 0, n constr at level 0,
    format "LD  A ,  [ # n ]").

Notation "'LD' '[' '#' n ']' ',' 'A'" := (Ild_XA n)
  (in custom asm at level 0, n constr at level 0,
    format "LD  [ # n ] ,  A").

Notation "'LDW' '[' '#' n ']' ',' 'SP'" := (Ild_LK n)
  (in custom asm at level 0, n constr at level 0,
    format "LDW  [ # n ] ,  SP").

Notation "'LDW' 'SP' ',' 'HL'" := Ild_KJ
  (in custom asm at level 0, format "LDW  SP ,  HL").

Notation "'LDW' 'HL' ',' 'SP'" := (Ild_JK 0)
  (in custom asm at level 0, format "LDW  HL ,  SP").

Notation "'LDW' 'HL' ',' 'SP' '+' '#' n" := (Ild_JK n)
  (in custom asm at level 0, n constr at level 0,
    format "LDW  HL ,  SP  +  # n").

Notation "'LDH' '[' '#' n ']' ',' 'A'" := (Ildh_IA n)
  (in custom asm at level 0, n constr at level 0,
    format "LDH  [ # n ] ,  A").

Notation "'LDH' 'A' ',' '[' '#' n ']'" := (Ildh_AI n)
  (in custom asm at level 0, n constr at level 0,
    format "LDH  A ,  [ # n ]").

Notation "'LDH' '[' 'C' ']' ',' 'A'" := Ildh_CA
  (in custom asm at level 0, format "LDH  [ C ] ,  A").

Notation "'LDH' 'A' ',' '[' 'C' ']'" := Ildh_AC
  (in custom asm at level 0, format "LDH  A ,  [ C ]").

Notation "'NOP'" := Inop
  (in custom asm at level 0).

Notation "'OR' 'A' ',' r" := (Ior_R r)
  (in custom asm at level 0, r constr at level 0,
    format "OR  A ,  r").

Notation "'OR' 'A' ',' '#' n" := (Ior_I n)
  (in custom asm at level 0, n constr at level 0,
    format "OR  A ,  # n").

Notation "'OR' 'A' ',' '[' 'HL' ']'" := Ior_M
  (in custom asm at level 0,
    format "OR  A ,  [ HL ]").

Notation "'POP' r" := (Ipop r)
  (in custom asm at level 0, r constr at level 0,
    format "POP  r").

Notation "'PUSH' r" := (Ipush r)
  (in custom asm at level 0, r constr at level 0,
    format "PUSH  r").

Notation "'RES' b ',' r" := (Ires_R b r)
  (in custom asm at level 0, b constr at level 0, r constr at level 0,
    format "RES  b ,  r").

Notation "'RES' b ',' '[' 'HL' ']'" := (Ires_M b)
  (in custom asm at level 0, b constr at level 0,
    format "RES  b ,  [ HL ]").

Notation "'RET'" := (Iret None)
  (in custom asm at level 0).

Notation "'RET' cc" := (Iret (Some cc))
  (in custom asm at level 0, cc constr at level 0,
    format "RET  cc").

Notation "'RETI'" := Ireti
  (in custom asm at level 0).

Notation "'RL' r" := (Irl_R r)
  (in custom asm at level 0, r constr at level 0,
    format "RL  r").

Notation "'RL' '[' 'HL' ']'" := Irl_M
  (in custom asm at level 0,
    format "RL  [ HL ]").

Notation "'RLA'" := Irla
  (in custom asm at level 0).

Notation "'RLC' r" := (Irlc_R r)
  (in custom asm at level 0, r constr at level 0,
    format "RLC  r").

Notation "'RLC' '[' 'HL' ']'" := Irlc_M
  (in custom asm at level 0,
    format "RLC  [ HL ]").

Notation "'RLCA'" := Irlca
  (in custom asm at level 0).

Notation "'RR' r" := (Irr_R r)
  (in custom asm at level 0, r constr at level 0,
    format "RR  r").

Notation "'RR' '[' 'HL' ']'" := Irr_M
  (in custom asm at level 0,
    format "RR  [ HL ]").

Notation "'RRA'" := Irra
  (in custom asm at level 0).

Notation "'RRC' r" := (Irrc_R r)
  (in custom asm at level 0, r constr at level 0,
    format "RRC  r").

Notation "'RRC' '[' 'HL' ']'" := Irrc_M
  (in custom asm at level 0,
    format "RRC  [ HL ]").

Notation "'RRCA'" := Irrca
  (in custom asm at level 0).

Notation "'RST' n" := (Irst n)
  (in custom asm at level 0, n constr at level 0,
    format "RST  n").

Notation "'SBC' 'A' ',' r" := (Isbc_R r)
  (in custom asm at level 0, r constr at level 0,
    format "SBC  A ,  r").

Notation "'SBC' 'A' ',' '#' n" := (Isbc_I n)
  (in custom asm at level 0, n constr at level 0,
    format "SBC  A ,  # n").

Notation "'SBC' 'A' ',' '[' 'HL' ']'" := Isbc_M
  (in custom asm at level 0,
    format "SBC  A ,  [ HL ]").

Notation "'SCF'" := Iscf
  (in custom asm at level 0).

Notation "'SET' b ',' r" := (Iset_R b r)
  (in custom asm at level 0, b constr at level 0, r constr at level 0,
    format "SET  b ,  r").

Notation "'SET' b ',' '[' 'HL' ']'" := (Iset_M b)
  (in custom asm at level 0, b constr at level 0,
    format "SET  b ,  [ HL ]").

Notation "'SLA' r" := (Isla_R r)
  (in custom asm at level 0, r constr at level 0,
    format "SLA  r").

Notation "'SLA' '[' 'HL' ']'" := Isla_M
  (in custom asm at level 0,
    format "SLA  [ HL ]").

Notation "'SRA' r" := (Isra_R r)
  (in custom asm at level 0, r constr at level 0,
    format "SRA  r").

Notation "'SRA' '[' 'HL' ']'" := Isra_M
  (in custom asm at level 0,
    format "SRA  [ HL ]").

Notation "'SRL' r" := (Isrl_R r)
  (in custom asm at level 0, r constr at level 0,
    format "SRL  r").

Notation "'SRL' '[' 'HL' ']'" := Isrl_M
  (in custom asm at level 0,
    format "SRL  [ HL ]").

Notation "'STOP'" := Istop
  (in custom asm at level 0).

Notation "'SUB' 'A' ',' r" := (Isub_R r)
  (in custom asm at level 0, r constr at level 0,
    format "SUB  A ,  r").

Notation "'SUB' 'A' ',' '#' n" := (Isub_I n)
  (in custom asm at level 0, n constr at level 0,
    format "SUB  A ,  # n").

Notation "'SUB' 'A' ',' '[' 'HL' ']'" := Isub_M
  (in custom asm at level 0,
    format "SUB  A ,  [ HL ]").

Notation "'SWAP' r" := (Iswap_R r)
  (in custom asm at level 0, r constr at level 0,
    format "SWAP  r").

Notation "'SWAP' '[' 'HL' ']'" := Iswap_M
  (in custom asm at level 0,
    format "SWAP  [ HL ]").

Notation "'XOR' 'A' ',' r" := (Ixor_R r)
  (in custom asm at level 0, r constr at level 0,
    format "XOR  A ,  r").

Notation "'XOR' 'A' ',' '#' n" := (Ixor_I n)
  (in custom asm at level 0, n constr at level 0,
    format "XOR  A ,  # n").

Notation "'XOR' 'A' ',' '[' 'HL' ']'" := Ixor_M
  (in custom asm at level 0,
    format "XOR  A ,  [ HL ]").

Notation "'ILLEGAL' x" := (Iillegal x)
  (in custom asm at level 0, x constr at level 0).

(*|
## Notation Tests
|*)

Goal True.
  Tactic Notation "test" constr(T) :=
    let H := fresh "OK" in assert (H: T) by reflexivity.

  (* Misc ALU instructions *)
  test ($[ADC A, B] = Iadc_R B).
  test ($[ADC A, #42] = Iadc_I 42).
  test ($[ADC A, [HL]] = Iadc_M).
  test ($[ADD A, B] = Iadd_R B).
  test ($[ADD A, #42] = Iadd_I 42).
  test ($[ADD A, [HL]] = Iadd_M).
  test ($[ADD HL, BC] = Iadd_P BC).
  test ($[ADD SP, #0x42] = Iadd_K 0x42).

  (* Misc LD instructions *)
  test ($[LD A, B] = Ild_RR A B).
  test ($[LD A, #42] = Ild_RI A 42).
  test ($[LD [HL], A] = Ild_MR A).
  test ($[LD [HL], #42] = Ild_MI 42).
  test ($[LDW BC, #0x1234] = Ild_PL BC 0x1234).
  test ($[LD A, [HL]] = Ild_RM A).
  test ($[LD A, [BC]] = Ild_AS BC).
  test ($[LD A, [DE]] = Ild_AS DE).
  test ($[LD A, [HL+]] = Ild_AS HLI).
  test ($[LD A, [HL-]] = Ild_AS HLD).
  test ($[LD [HL], A] = Ild_MR A).
  test ($[LD [HL+], A] = Ild_SA HLI).
  test ($[LD [HL-], A] = Ild_SA HLD).
  test ($[LDW SP, HL] = Ild_KJ).
  test ($[LDW HL, SP] = Ild_JK 0%u8).
  test ($[LDW HL, SP + #0] = Ild_JK 0).
  test ($[LDW HL, SP + #0xFF] = Ild_JK 0xFF).
  test ($[LDH A, [C]] = Ildh_AC).
  test ($[LDH [C], A] = Ildh_CA).

  (* Some LD instructions with quantifiers. *)
  test (forall r s, $[LD r, s] = Ild_RR r s).
  test (forall r, $[LD A, r] = Ild_RR A r).
  test (forall r n, $[LD r, #n] = Ild_RI r n).
  test (forall r, $[LD [HL], r] = Ild_MR r).
  test (forall n, $[LD [HL], #n] = Ild_MI n).
  test (forall r n, $[LDW r, #n] = Ild_PL r n).
  test (forall n, $[LD A, [#n]] = Ild_AX n).
  test (forall n, $[LD [#n], A] = Ild_XA n).
  test (forall n, $[LDW [#n], SP] = Ild_LK n).
  test (forall n, $[LDH A, [#n]] = Ildh_AI n).
  test (forall n, $[LDH [#n], A] = Ildh_IA n).

  (* Jumps *)
  test (forall n, $[JP #n] = Ijp None n).
  test (forall n, $[JP FZ, #n] = Ijp (Some FZ) n).
  test (forall f n, $[JP f, #n] = Ijp (Some f) n).
  test (forall n, $[JR #n] = Ijr None n).
  test (forall n, $[JR FZ, #n] = Ijr (Some FZ) n).
  test (forall f, $[JR f, #(-32)] = Ijr (Some f) (-32)).

  (* Numbers *)
  test ($[BIT 1, A] = Ibit_R B1 A).
  test ($[BIT 0x7, A] = Ibit_R B7 A).
  test ($[RST 0x00] = Irst R00).
  test ($[RST 0x38] = Irst R38).
  test ($[ILLEGAL 0xFD] = Iillegal UFD).
Abort.


(*|
# Program Notation
|*)

Notation "P ; Q" := (Pseq P Q)
  (in custom asm at level 10, right associativity).

Notation "L :" := (Plabel L)
  (in custom asm at level 0, L constr at level 0, format "L :").

Notation "'WITH' x .. y , P" := (Pwith (fun x => .. (Pwith (fun y => P)) ..))
  (in custom asm at level 0, x binder, y binder, P at level 200).

Example waitvblank_example : program := $[
  WITH waitvblank done,
    waitvblank:;
      LDH A, [#0x44];
      CP A, #144;
      JP FC, #waitvblank;
    done:;
      HALT
].
