From GameBoy.Stdint Require Import Stdint.
Open Scope u8_scope.

(*|
This module defines a data type for SM83 assembly instructions.

Definitions
=======================================================================

The SM83 has eight 8-bit registers: ``A``, ``B``, ``C``, ``D``, ``E``,
``F``, ``H`` and ``L``. All registers are general purpose except for
``F``, which contains flags used for arithmetic and jumps. The ``F``
register is never used as a operand, so it's omitted here.
|*)

Variant reg8 := A | B | C | D | E | H | L.

(*|
Next we define 16-bit registers. The SM83 has two 16-bit registers:
``SP`` and ``PC``, and four register *pairs*: ``BC``, ``DE``, ``HL``,
and ``AF``. ``PC`` is "internal" and never appears as an operand.

Defining 16-bit registers is a little tricky. Some instructions only
accept a strict subset of registers.  For example, ``INC`` only accepts
the 16-bit registers ``BC``, ``DE``, ``HL``, and ``SP`` as operands
(``INC AF`` is an invalid instruction). In order to be prescise in
our definitions, we define three 16-bit register subsets: ``preg16``,
``qreg16``, and ``sreg16``.

preg16
    The ``preg16`` subset consists of the registers ``BC``, ``DE``,
    ``HL`` and ``SP``. These are the possible 16-bit register operands
    for ``INC``, ``DEC``, ``ADD``, and ``LD``.

qreg16
    The ``qreg16`` subset consists of the registers ``BC``, ``DE``,
    ``HL``, and ``AF``. These are the possible 16-bit operands for
    ``PUSH`` and ``POP``.

sreg16
    The ``sreg16`` subset is a special set used for 16-bit indirect loads
    (e.g. ``LD A, [BC]``). It consists of ``BC``, ``DE``, ``HL+``,
    and ``HL-``, where ``HL+`` and ``HL-`` are post-increments and
    post-decrements on ``HL``.

The sets ``preg16``, ``qreg16`` and ``sreg16`` all share common
registers. We define each register *once*, and then use constructors to
inject smaller subsets into larger ones.
|*)

Variant bcde := BC | DE.
Variant bcdehl := InB (r : bcde) | HL.
Variant preg16 := InP (r : bcdehl) | SP.
Variant qreg16 := InQ (r : bcdehl) | AF.
Variant sreg16 := InS (r : bcde) | HLI | HLD.

(*|
The injectors are automatically coerced. This allows us to write terms
like ``PUSH BC`` instead of ``PUSH (InQ (InB BC))`` without fancy notation.
|*)

Coercion InB : bcde >-> bcdehl.
Coercion InP : bcdehl >-> preg16.
Coercion InQ : bcdehl >-> qreg16.
Coercion InS : bcde >-> sreg16.

(* Condition codes for CALL, JP, JR, and RET. *)
Variant cond := FZ | FNZ | FC | FNC.

(* Possible target addresses for RST. *)
Variant rst := R00 | R08 | R10 | R18 | R20 | R28 | R30 | R38.

(* Bit index for BIT, RES, and SET. B0 is the LSB. *)
Variant bitindex := B0 | B1 | B2 | B3 | B4 | B5 | B6 | B7.

Definition bitmask : bitindex -> u8 :=
  fun i => match i with
    | B0 => 0x01
    | B1 => 0x02
    | B2 => 0x04
    | B3 => 0x08
    | B4 => 0x10
    | B5 => 0x20
    | B6 => 0x40
    | B7 => 0x80
  end.

(*|
There are eleven illegal opcodes. When decoding instructions, we keep
track of which illegal opcodes were encountered so that we get perfect
roundtrips when re-encoding.
|*)

Variant unknownop := 
  UD3 | UDB | UDD | UE3 | UE4 | UEB | UEC | UED | UF4 | UFC | UFD.

(*|
Now we get to the definition for instructions.

Note that mnemonics are extremely overloaded. The opcode for a given
mnemonic may differ based on the types of operands it's given. We
distinguish each overloaded instruction by adding suffixes to each
constructor's name. The suffixes are:

======  ===============================================================
Suffix  Operand
======  ===============================================================
A       The register ``A``
C       The register ``C``
I       An 8-bit immediate operand
J       The 16-bit register ``HL``
K       The 16-bit register ``SP``
L       A 16-bit immediate operand
M       A store to ``[HL]``
P       A 16-bit register: ``BC``, ``DE``, ``HL``, or ``SP``
Q       A 16-bit register: ``BC``, ``DE``, ``HL``, or ``AF``
R       An 8-bit register: ``A``, ``B``, ``C``, ``D``, ``E``, ``H``, or ``L``
S       A store to ``[BC]``, ``[DE]``, ``[HL+]``, or ``[HL-]``
======  ===============================================================
|*)

Variant instr :=
  | IadcI : u8 -> instr                         (* ADC A, #u8 *)
  | IadcM : instr                               (* ADC A, [HL] *)
  | IadcR : reg8 -> instr                       (* ADC A, r8 *)
  | IaddI : u8 -> instr                         (* ADD A, #u8 *)
  | IaddK : i8 -> instr                         (* ADD SP, #i8 *)
  | IaddM : instr                               (* ADD A, [HL] *)
  | IaddP : preg16 -> instr                     (* ADD HL, r16 *)
  | IaddR : reg8 -> instr                       (* ADD A, r8 *)
  | IandI : u8 -> instr                         (* AND A, #u8 *)
  | IandM : instr                               (* AND A, [HL] *)
  | IandR : reg8 -> instr                       (* AND A, r8 *)
  | IbitM : bitindex -> instr                   (* BIT b, [HL] *)
  | IbitR : bitindex -> reg8 -> instr           (* BIT b, r8 *)
  | Icall : option cond -> u16 -> instr         (* CALL cc, u16 *)
  | Iccf : instr                                (* CCF *)
  | IcpI : u8 -> instr                          (* CP A, #u8 *)
  | IcpM : instr                                (* CP A, [HL] *)
  | IcpR : reg8 -> instr                        (* CP A, r8 *)
  | Icpl : instr                                (* CPL *)
  | Idaa : instr                                (* DAA *)
  | IdecM : instr                               (* DEC [HL] *)
  | IdecP : preg16 -> instr                     (* DEC r16 *)
  | IdecR : reg8 -> instr                       (* DEC r8 *)
  | Idi : instr                                 (* DI *)
  | Iei : instr                                 (* EI *)
  | Ihalt : instr                               (* HALT *)
  | IincM : instr                               (* INC [HL] *)
  | IincP : preg16 -> instr                     (* INC r16 *)
  | IincR : reg8 -> instr                       (* INC r8 *)
  | Ijp : option cond -> u16 -> instr           (* JP cc, u16 *)
  | Ijphl : instr                               (* JP HL *)
  | Ijr : option cond -> i8 -> instr            (* JR cc, #i8 *)
  | IldAS : sreg16 -> instr                     (* LD A, [r16] *)
  | IldAX : u16 -> instr                        (* LD A, [u16] *)
  | IldJK : u8 -> instr                         (* LDW HL, SP+#u8 *)
  | IldKJ : instr                               (* LDW SP, HL *)
  | IldLK : u16 -> instr                        (* LDW [u16], SP *)
  | IldMI : u8 -> instr                         (* LD [HL], #u8 *)
  | IldMR : reg8 -> instr                       (* LD [HL], r8 *)
  | IldPL : preg16 -> u16 -> instr              (* LDW r16, u16 *)
  | IldRI : reg8 -> u8 -> instr                 (* LD r8, #u8 *)
  | IldRM : reg8 -> instr                       (* LD r8, [HL] *)
  | IldRR : reg8 -> reg8 -> instr               (* LD r8, r8 *)
  | IldSA : sreg16 -> instr                     (* LD [r16], A *)
  | IldXA : u16 -> instr                        (* LD [u16], A *)
  | IldhAC : instr                              (* LDH A, [C] *)
  | IldhAI : u8 -> instr                        (* LDH A, [#u8] *)
  | IldhCA : instr                              (* LDH [C], A *)
  | IldhIA : u8 -> instr                        (* LDH [#u8], A *)
  | Inop : instr                                (* NOP *)
  | IorI : u8 -> instr                          (* OR A, #u8 *)
  | IorM : instr                                (* OR A, [HL] *)
  | IorR : reg8 -> instr                        (* OR A, r8 *)
  | Ipop : qreg16 -> instr                      (* POP r16 *)
  | Ipush : qreg16 -> instr                     (* PUSH r16 *)
  | IresM : bitindex -> instr                   (* RES b, [HL] *)
  | IresR : bitindex -> reg8 -> instr           (* RES b, r8 *)
  | Iret : option cond -> instr                 (* RET cc *)
  | Ireti : instr                               (* RETI *)
  | IrlM : instr                                (* RL [HL] *)
  | IrlR : reg8 -> instr                        (* RL r8 *)
  | Irla : instr                                (* RLA *)
  | IrlcM : instr                               (* RLC [HL] *)
  | IrlcR : reg8 -> instr                       (* RLC r8 *)
  | Irlca : instr                               (* RLCA *)
  | IrrM : instr                                (* RR [HL] *)
  | IrrR : reg8 -> instr                        (* RR r8 *)
  | Irra : instr                                (* RRA *)
  | IrrcM : instr                               (* RRC [HL] *)
  | IrrcR : reg8 -> instr                       (* RRC r8 *)
  | Irrca : instr                               (* RRCA *)
  | Irst : rst -> instr                         (* RST u8 *)
  | IsbcI : u8 -> instr                         (* SBC A, #u8 *)
  | IsbcM : instr                               (* SBC A, [HL] *)
  | IsbcR : reg8 -> instr                       (* SBC A, r8 *)
  | Iscf : instr                                (* SCF *)
  | IsetM : bitindex -> instr                   (* SET b, [HL] *)
  | IsetR : bitindex -> reg8 -> instr           (* SET b, r8 *)
  | IslaM : instr                               (* SLA [HL] *)
  | IslaR : reg8 -> instr                       (* SLA r8 *)
  | IsraM : instr                               (* SRA [HL] *)
  | IsraR : reg8 -> instr                       (* SRA r8 *)
  | IsrlM : instr                               (* SRL [HL] *)
  | IsrlR : reg8 -> instr                       (* SRL r8 *)
  | Istop : instr                               (* STOP *)
  | IsubI : u8 -> instr                         (* SUB A, #u8 *)
  | IsubM : instr                               (* SUB A, [HL] *)
  | IsubR : reg8 -> instr                       (* SUB A, r8 *)
  | IswapM : instr                              (* SWAP [HL] *)
  | IswapR : reg8 -> instr                      (* SWAP r8 *)
  | IxorI : u8 -> instr                         (* XOR A, #u8 *)
  | IxorM : instr                               (* XOR A, [HL] *)
  | IxorR : reg8 -> instr                       (* XOR A, r8 *)
  | Iunknown : unknownop -> instr.

(*|
Number Notations
-----------------------------------------------------------------------
|*)

Declare Scope bitindex_scope.
Delimit Scope bitindex_scope with bitindex.
Bind Scope bitindex_scope with bitindex.

Definition bitindex_to_u8 : bitindex -> u8 :=
  fun i => match i with
    | B0 => 0
    | B1 => 1
    | B2 => 2
    | B3 => 3
    | B4 => 4
    | B5 => 5
    | B6 => 6
    | B7 => 7
  end.

Definition bitindex_of_u8 : u8 -> option bitindex :=
  fun b => match b with
    | 0 => Some B0
    | 1 => Some B1
    | 2 => Some B2
    | 3 => Some B3
    | 4 => Some B4
    | 5 => Some B5
    | 6 => Some B6
    | 7 => Some B7
    | _ => None
  end.

Definition bitindex_to_num : bitindex -> Number.uint :=
  fun r => Uint8.to_num_unsigned (bitindex_to_u8 r).

Definition bitindex_of_num : Number.uint -> option bitindex :=
  fun n => match Uint8.of_num_unsigned n with
  | None => None
  | Some x => bitindex_of_u8 x
  end.

Number Notation bitindex
  bitindex_of_num bitindex_to_num : bitindex_scope.


Declare Scope rst_scope.
Delimit Scope rst_scope with rst.
Bind Scope rst_scope with rst.

Definition rst_to_u8 : rst -> u8 :=
  fun r => match r with
    | R00 => 0x00
    | R08 => 0x08
    | R10 => 0x10
    | R18 => 0x18
    | R20 => 0x20
    | R28 => 0x28
    | R30 => 0x30
    | R38 => 0x38
  end.

Definition rst_of_u8 : u8 -> option rst :=
  fun r => match r with
    | 0x00 => Some R00
    | 0x08 => Some R08
    | 0x10 => Some R10
    | 0x18 => Some R18
    | 0x20 => Some R20
    | 0x28 => Some R28
    | 0x30 => Some R30
    | 0x38 => Some R38
    | _ => None
  end.

Definition rst_to_hex_num : rst -> Number.uint :=
  fun r => Uint8.to_hex_unsigned (rst_to_u8 r).

Definition rst_of_num : Number.uint -> option rst :=
  fun n => match Uint8.of_num_unsigned n with
  | None => None
  | Some x => rst_of_u8 x
  end.

Number Notation rst rst_of_num rst_to_hex_num : rst_scope.


Declare Scope unknownop_scope.
Delimit Scope unknownop_scope with unknownop.
Bind Scope unknownop_scope with unknownop.

Definition unknownop_to_u8 : unknownop -> u8 :=
  fun x => match x with
    | UD3 => 0xD3
    | UDB => 0xDB
    | UDD => 0xDD
    | UE3 => 0xE3
    | UE4 => 0xE4
    | UEB => 0xEB
    | UEC => 0xEC
    | UED => 0xED
    | UF4 => 0xF4
    | UFC => 0xFC
    | UFD => 0xFD
  end.

Definition unknownop_of_u8 : u8 -> option unknownop :=
  fun x => match x with
    | 0xD3 => Some UD3
    | 0xDB => Some UDB
    | 0xDD => Some UDD
    | 0xE3 => Some UE3
    | 0xE4 => Some UE4
    | 0xEB => Some UEB
    | 0xEC => Some UEC
    | 0xED => Some UED
    | 0xF4 => Some UF4
    | 0xFC => Some UFC
    | 0xFD => Some UFD
    | _ => None
  end.

Definition unknownop_to_hex_num : unknownop -> Number.uint :=
  fun r => Uint8.to_hex_unsigned (unknownop_to_u8 r).

Definition unknownop_of_num : Number.uint -> option unknownop :=
  fun n => match Uint8.of_num_unsigned n with
  | None => None
  | Some x => unknownop_of_u8 x
  end.

Number Notation unknownop
  unknownop_of_num unknownop_to_hex_num : unknownop_scope.

(*|
Instruction Notations
-----------------------------------------------------------------------

Now we define syntax notations for assembly instructions.  The assembly
notation syntax does a pretty good job of resembling Z80-style syntax,
with a few exceptions.

First, all immediate 8-bit and 16-bit values are prefixed with the sigil
``#`` (e.g. ``ADD A, #42``). Doing so helps the notation parser resolve
ambiguity between register operands and immediate operands.

Second, a few mnemonics are suffixed with a ``W`` in order to distinguish
between their 8-bit and 16-bit versions (the ``W`` stands for "Word").
They are: ``INC``/``INCW``, ``DEC``/``DECW``, and ``LD``/``LDW``.

Finally, it's worth noting that all instruction operands live in ``constr``
grammar. We don't bother with special syntax for ``cond``, ``rst``,
``bitindex``, or ``unknownop``.  For example, the classic Z80-style
syntax for a conditional jump looks something like: ``JP Z, label``,
but in our syntax, the condition field simply uses the [cond] definition,
so it's written here as ``JP FZ, #label`` using the Rocq term ``FZ``.
|*)

Declare Custom Entry asm.

Notation "'$[' x ']'" := x
  (x custom asm at level 100, format "$[ x ]").

Notation "'ADC' 'A' ',' r" := (IadcR r)
  (in custom asm at level 1, r constr at level 0,
    format "ADC  A ,  r").

Notation "'ADC' 'A' ',' '#' n" := (IadcI n)
  (in custom asm at level 1, n constr at level 0,
    format "ADC  A ,  # n").

Notation "'ADC' 'A' ',' '[' 'HL' ']'" := IadcM
  (in custom asm at level 1,
    format "ADC  A ,  [ HL ]").

Notation "'ADD' 'A' ',' r" := (IaddR r)
  (in custom asm at level 1, r constr at level 0,
    format "ADD  A ,  r").

Notation "'ADD' 'A' ',' '#' n" := (IaddI n)
  (in custom asm at level 1, n constr at level 0,
    format "ADD  A ,  # n").

Notation "'ADD' 'A' ',' '[' 'HL' ']'" := IaddM
  (in custom asm at level 1,
    format "ADD  A ,  [ HL ]").

Notation "'ADD' 'HL' ',' r" := (IaddP r)
  (in custom asm at level 1, r constr at level 0,
    format "ADD  HL ,  r").

Notation "'ADD' 'SP' ',' '#' n" := (IaddK n)
  (in custom asm at level 1, n constr at level 0,
    format "ADD  SP ,  # n").

Notation "'AND' 'A' ',' r" := (IandR r)
  (in custom asm at level 1, r constr at level 0,
    format "AND  A ,  r").

Notation "'AND' 'A' ',' '#' n" := (IandI n)
  (in custom asm at level 1, n constr at level 0,
    format "AND  A ,  # n").

Notation "'AND' 'A' ',' '[' 'HL' ']'" := IandM
  (in custom asm at level 1,
    format "AND  A ,  [ HL ]").

Notation "'BIT' b ',' r" := (IbitR b r)
  (in custom asm at level 1, b constr at level 0, r constr at level 0,
    format "BIT  b ,  r").

Notation "'BIT' b ',' '[' 'HL' ']'" := (IbitM b)
  (in custom asm at level 1, b constr at level 0,
    format "BIT  b ,  [ HL ]").

Notation "'CALL' '#' n" := (Icall None n)
  (in custom asm at level 1, n constr at level 0,
    format "CALL  # n").

Notation "'CALL' cc ',' '#' n" := (Icall (Some cc) n)
  (in custom asm at level 1, cc constr at level 0, n constr at level 0,
    format "CALL  cc ,  # n").

Notation "'CCF'" := Iccf
  (in custom asm at level 0).

Notation "'CP' 'A' ',' r" := (IcpR r)
  (in custom asm at level 1, r constr at level 0,
    format "CP  A ,  r").

Notation "'CP' 'A' ',' '#' n" := (IcpI n)
  (in custom asm at level 1, n constr at level 0,
    format "CP  A ,  # n").

Notation "'CP' 'A' ',' '[' 'HL' ']'" := IcpM
  (in custom asm at level 1,
    format "CP  A ,  [ HL ]").

Notation "'CPL'" := Icpl
  (in custom asm at level 0).

Notation "'DAA'" := Idaa
  (in custom asm at level 0).

Notation "'DEC' r" := (IdecR r)
  (in custom asm at level 1, r constr at level 1,
    format "DEC  r").

Notation "'DEC' '[' 'HL' ']'" := IdecM
  (in custom asm at level 1, format "DEC  [ HL ]").

Notation "'DECW' r" := (IdecP r)
  (in custom asm at level 1, r constr at level 1,
    format "DECW  r").

Notation "'DI'" := Idi
  (in custom asm at level 0).

Notation "'EI'" := Iei
  (in custom asm at level 0).

Notation "'HALT'" := Ihalt
  (in custom asm at level 0).

Notation "'INC' r" := (IincR r)
  (in custom asm at level 1, r constr at level 1,
    format "INC  r").

Notation "'INC' '[' 'HL' ']'" := IincM
  (in custom asm at level 1, format "INC  [ HL ]").

Notation "'INCW' r" := (IincP r)
  (in custom asm at level 1, r constr at level 1,
    format "INCW  r").

Notation "'JP' '#' n" := (Ijp None n)
  (in custom asm at level 1, n constr at level 0,
    format "JP  # n").

Notation "'JP' cc ',' '#' n" := (Ijp (Some cc) n)
  (in custom asm at level 1, cc constr at level 0, n constr at level 0,
    format "JP  cc ,  # n").

Notation "'JP' 'HL'" := Ijphl
  (in custom asm at level 1, format "JP  HL").

Notation "'JR' '#' n" := (Ijr None n)
  (in custom asm at level 1, n constr at level 0,
    format "JR  # n").

Notation "'JR' cc ',' '#' n" := (Ijr (Some cc) n)
  (in custom asm at level 1, cc constr at level 0, n constr at level 0,
    format "JR  cc ,  # n").

Notation "'LD' r ',' s" := (IldRR r s)
  (in custom asm at level 1, r constr at level 0, s constr at level 0,
    format "LD  r ,  s").

Notation "'LD' r ',' '#' n" := (IldRI r n)
  (in custom asm at level 1, r constr at level 0, n constr at level 0,
    format "LD  r ,  # n").

Notation "'LD' r ',' '[' 'HL' ']'" := (IldRM r)
  (in custom asm at level 1, r constr at level 0,
    format "LD  r ,  [ HL ]").

Notation "'LD' '[' 'HL' ']' ',' r" := (IldMR r)
  (in custom asm at level 1, r constr at level 0,
    format "LD  [ HL ] ,  r").

Notation "'LD' '[' 'HL' ']' ',' # n" := (IldMI n)
  (in custom asm at level 1, n constr at level 0,
    format "LD  [ HL ] ,  # n").

Notation "'LDW' r ',' '#' n" := (IldPL r n)
  (in custom asm at level 1, r constr at level 0, n constr at level 0,
    format "LDW  r ,  # n").

(*|
For ``IldAS``, we can't define the notation as ``"LD A , [ r ]"`` because
there are conflicts with ``IldRR`` and ``IldRM``.  Expanding out all four
cases of the source register ``r`` magically resolves the conflict. We
do the same for ``IldSA``.

Oddly, we have to explicitly state ``InS BC`` and ``InS DE`` instead of
``BC`` and ``DE`` here. Otherwise, printing notations don't work for
``IldAS`` or ``IldSA``. Note that parsing still works fine. I think this
is a small bug in Rocq.
|*)

Notation "'LD' 'A' ',' '[' 'BC' ']'" := (IldAS (InS BC))
  (in custom asm at level 1, format "LD  A ,  [ BC ]").

Notation "'LD' 'A' ',' '[' 'DE' ']'" := (IldAS (InS DE))
  (in custom asm at level 1, format "LD  A ,  [ DE ]").

Notation "'LD' 'A' ',' '[' 'HL+' ']'" := (IldAS HLI)
  (in custom asm at level 1, format "LD  A ,  [ HL+ ]").

Notation "'LD' 'A' ',' '[' 'HL-' ']'" := (IldAS HLD)
  (in custom asm at level 1, format "LD  A ,  [ HL- ]").

Notation "'LD' '[' 'BC' ']' ',' 'A'" := (IldSA (InS BC))
  (in custom asm at level 1, format "LD  [ BC ] ,  A").

Notation "'LD' '[' 'DE' ']' ',' 'A'" := (IldSA (InS DE))
  (in custom asm at level 1, format "LD  [ DE ] ,  A").

Notation "'LD' '[' 'HL+' ']' ',' 'A'" := (IldSA HLI)
  (in custom asm at level 1, format "LD  [ HL+ ] ,  A").

Notation "'LD' '[' 'HL-' ']' ',' 'A'" := (IldSA HLD)
  (in custom asm at level 1, format "LD  [ HL- ] ,  A").

Notation "'LD' 'A' ',' '[' '#' n ']'" := (IldAX n)
  (in custom asm at level 1, n constr at level 0,
    format "LD  A ,  [ # n ]").

Notation "'LD' '[' '#' n ']' ',' 'A'" := (IldXA n)
  (in custom asm at level 1, n constr at level 0,
    format "LD  [ # n ] ,  A").

Notation "'LDW' '[' '#' n ']' ',' 'SP'" := (IldLK n)
  (in custom asm at level 1, n constr at level 0,
    format "LDW  [ # n ] ,  SP").

Notation "'LDW' 'SP' ',' 'HL'" := IldKJ
  (in custom asm at level 1, format "LDW  SP ,  HL").

Notation "'LDW' 'HL' ',' 'SP'" := (IldJK x00)
  (in custom asm at level 1, format "LDW  HL ,  SP").

Notation "'LDW' 'HL' ',' 'SP' '+' '#' n" := (IldJK n)
  (in custom asm at level 1, n constr at level 0,
    format "LDW  HL ,  SP  +  # n").

Notation "'LDH' '[' '#' n ']' ',' 'A'" := (IldhIA n)
  (in custom asm at level 1, n constr at level 0,
    format "LDH  [ # n ] ,  A").

Notation "'LDH' 'A' ',' '[' '#' n ']'" := (IldhAI n)
  (in custom asm at level 1, n constr at level 0,
    format "LDH  A ,  [ # n ]").

Notation "'LDH' '[' 'C' ']' ',' 'A'" := IldhCA
  (in custom asm at level 1, format "LDH  [ C ] ,  A").

Notation "'LDH' 'A' ',' '[' 'C' ']'" := IldhAC
  (in custom asm at level 1, format "LDH  A ,  [ C ]").

Notation "'NOP'" := Inop
  (in custom asm at level 0).

Notation "'OR' 'A' ',' r" := (IorR r)
  (in custom asm at level 1, r constr at level 0,
    format "OR  A ,  r").

Notation "'OR' 'A' ',' '#' n" := (IorI n)
  (in custom asm at level 1, n constr at level 0,
    format "OR  A ,  # n").

Notation "'OR' 'A' ',' '[' 'HL' ']'" := IorM
  (in custom asm at level 1,
    format "OR  A ,  [ HL ]").

Notation "'POP' r" := (Ipop r)
  (in custom asm at level 1, r constr at level 0, format "POP  r").

Notation "'PUSH' r" := (Ipush r)
  (in custom asm at level 1, r constr at level 0, format "PUSH  r").

Notation "'RES' b ',' r" := (IresR b r)
  (in custom asm at level 1, b constr at level 0, r constr at level 0,
    format "RES  b ,  r").

Notation "'RES' b ',' '[' 'HL' ']'" := (IresM b)
  (in custom asm at level 1, b constr at level 0,
    format "RES  b ,  [ HL ]").

Notation "'RET'" := (Iret None)
  (in custom asm at level 1).

Notation "'RET' cc" := (Iret (Some cc))
  (in custom asm at level 1, cc constr at level 0,
    format "RET  cc").

Notation "'RETI'" := Ireti
  (in custom asm at level 0).

Notation "'RL' r" := (IrlR r)
  (in custom asm at level 1, r constr at level 0,
    format "RL  r").

Notation "'RL' '[' 'HL' ']'" := IrlM
  (in custom asm at level 1,
    format "RL  [ HL ]").

Notation "'RLA'" := Irla
  (in custom asm at level 0).

Notation "'RLC' r" := (IrlcR r)
  (in custom asm at level 1, r constr at level 0,
    format "RLC  r").

Notation "'RLC' '[' 'HL' ']'" := IrlcM
  (in custom asm at level 1,
    format "RLC  [ HL ]").

Notation "'RLCA'" := Irlca
  (in custom asm at level 0).

Notation "'RR' r" := (IrrR r)
  (in custom asm at level 1, r constr at level 0,
    format "RR  r").

Notation "'RR' '[' 'HL' ']'" := IrrM
  (in custom asm at level 1,
    format "RR  [ HL ]").

Notation "'RRA'" := Irra
  (in custom asm at level 0).

Notation "'RRC' r" := (IrrcR r)
  (in custom asm at level 1, r constr at level 0,
    format "RRC  r").

Notation "'RRC' '[' 'HL' ']'" := IrrcM
  (in custom asm at level 1,
    format "RRC  [ HL ]").

Notation "'RRCA'" := Irrca
  (in custom asm at level 0).

Notation "'RST' n" := (Irst n)
  (in custom asm at level 1, n constr at level 0,
    format "RST  n").

Notation "'SBC' 'A' ',' r" := (IsbcR r)
  (in custom asm at level 1, r constr at level 0,
    format "SBC  A ,  r").

Notation "'SBC' 'A' ',' '#' n" := (IsbcI n)
  (in custom asm at level 1, n constr at level 0,
    format "SBC  A ,  # n").

Notation "'SBC' 'A' ',' '[' 'HL' ']'" := IsbcM
  (in custom asm at level 1,
    format "SBC  A ,  [ HL ]").

Notation "'SCF'" := Iscf
  (in custom asm at level 0).

Notation "'SET' b ',' r" := (IsetR b r)
  (in custom asm at level 1, b constr at level 0, r constr at level 0,
    format "SET  b ,  r").

Notation "'SET' b ',' '[' 'HL' ']'" := (IsetM b)
  (in custom asm at level 1, b constr at level 0,
    format "SET  b ,  [ HL ]").

Notation "'SLA' r" := (IslaR r)
  (in custom asm at level 1, r constr at level 0,
    format "SLA  r").

Notation "'SLA' '[' 'HL' ']'" := IslaM
  (in custom asm at level 1,
    format "SLA  [ HL ]").

Notation "'SRA' r" := (IsraR r)
  (in custom asm at level 1, r constr at level 0,
    format "SRA  r").

Notation "'SRA' '[' 'HL' ']'" := IsraM
  (in custom asm at level 1,
    format "SRA  [ HL ]").

Notation "'SRL' r" := (IsrlR r)
  (in custom asm at level 1, r constr at level 0,
    format "SRL  r").

Notation "'SRL' '[' 'HL' ']'" := IsrlM
  (in custom asm at level 1,
    format "SRL  [ HL ]").

Notation "'STOP'" := Istop
  (in custom asm at level 0).

Notation "'SUB' 'A' ',' r" := (IsubR r)
  (in custom asm at level 1, r constr at level 0,
    format "SUB  A ,  r").

Notation "'SUB' 'A' ',' '#' n" := (IsubI n)
  (in custom asm at level 1, n constr at level 0,
    format "SUB  A ,  # n").

Notation "'SUB' 'A' ',' '[' 'HL' ']'" := IsubM
  (in custom asm at level 1,
    format "SUB  A ,  [ HL ]").

Notation "'SWAP' r" := (IswapR r)
  (in custom asm at level 1, r constr at level 0,
    format "SWAP  r").

Notation "'SWAP' '[' 'HL' ']'" := IswapM
  (in custom asm at level 1,
    format "SWAP  [ HL ]").

Notation "'XOR' 'A' ',' r" := (IxorR r)
  (in custom asm at level 1, r constr at level 0,
    format "XOR  A ,  r").

Notation "'XOR' 'A' ',' '#' n" := (IxorI n)
  (in custom asm at level 1, n constr at level 0,
    format "XOR  A ,  # n").

Notation "'XOR' 'A' ',' '[' 'HL' ']'" := IxorM
  (in custom asm at level 1,
    format "XOR  A ,  [ HL ]").

Notation "'UNKNOWN' x" := (Iunknown x)
  (in custom asm at level 1, x constr at level 0).


(*|
Notation Tests
-----------------------------------------------------------------------
|*)

(* To debug the grammar: *)
(* Print Custom Grammar asm. *)

Goal True.
  Tactic Notation "test" constr(T) :=
    let H := fresh "OK" in assert (H: T) by reflexivity; clear H.

  (* Misc ALU instructions *)
  test ($[ADC A, B] = IadcR B).
  test ($[ADC A, #42] = IadcI 42).
  test ($[ADC A, [HL]] = IadcM).
  test ($[ADD A, B] = IaddR B).
  test ($[ADD A, #42] = IaddI 42).
  test ($[ADD A, [HL]] = IaddM).
  test ($[ADD HL, BC] = IaddP BC).
  test ($[ADD SP, #0x42] = IaddK 0x42).

  (* Misc LD instructions *)
  test ($[LD A, B] = IldRR A B).
  test ($[LD A, #42] = IldRI A 42).
  test ($[LD [HL], A] = IldMR A).
  test ($[LD [HL], #42] = IldMI 42).
  test ($[LDW BC, #0x1234] = IldPL BC 0x1234).
  test ($[LD A, [HL]] = IldRM A).
  test ($[LD A, [BC]] = IldAS BC).
  test ($[LD A, [DE]] = IldAS DE).
  test ($[LD A, [HL+]] = IldAS HLI).
  test ($[LD A, [HL-]] = IldAS HLD).
  test ($[LD [HL], A] = IldMR A).
  test ($[LD [HL+], A] = IldSA HLI).
  test ($[LD [HL-], A] = IldSA HLD).
  test ($[LDW SP, HL] = IldKJ).
  test ($[LDW HL, SP] = IldJK 0).
  test ($[LDW HL, SP + #0] = IldJK 0).
  test ($[LDW HL, SP + #0xFF] = IldJK 0xFF).
  test ($[LDH A, [C]] = IldhAC).
  test ($[LDH [C], A] = IldhCA).

  (* Some LD instructions with quantifiers. *)
  test (forall r s, $[LD r, s] = IldRR r s).
  test (forall r, $[LD A, r] = IldRR A r).
  test (forall r n, $[LD r, #n] = IldRI r n).
  test (forall r, $[LD [HL], r] = IldMR r).
  test (forall n, $[LD [HL], #n] = IldMI n).
  test (forall r n, $[LDW r, #n] = IldPL r n).
  test (forall n, $[LD A, [#n]] = IldAX n).
  test (forall n, $[LD [#n], A] = IldXA n).
  test (forall n, $[LDW [#n], SP] = IldLK n).
  test (forall n, $[LDH A, [#n]] = IldhAI n).
  test (forall n, $[LDH [#n], A] = IldhIA n).

  (* Jumps *)
  test (forall n, $[JP #n] = $[JP #n]).
  test (forall n, $[JP FZ, #n] = $[JP FZ, #n]).
  test (forall f n, $[JP f, #n] = $[JP f, #n]).
  test (forall n, $[JR #n] = $[JR #n]).
  test (forall n, $[JR FZ, #n] = $[JR FZ, #n]).
  test (forall f, $[JR f, #(-32)] = $[JR f, #(-32)]).

  (* Numbers *)
  test ($[BIT 1, A] = IbitR B1 A).
  test ($[BIT 7, A] = IbitR B7 A).
  test ($[RST 0x00] = Irst R00).
  test ($[RST 0x38] = Irst R38).
  test ($[UNKNOWN 0xFD] = Iunknown UFD).
Abort.


