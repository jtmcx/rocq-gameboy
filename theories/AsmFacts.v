From Stdlib Require Import List ZArith.

From GameBoy Require Import
  Asm
  AsmEncoding
  Stdint.

From ITree Require Import
  ITree
  ITreeFacts
  ITreeMonad
  Basics.Monad
  Events.State
  Events.StateFacts
  Events.Exception
  Events.ExceptionFacts.

From ExtLib Require Import Structures.Maps.

Import ITreeNotations.
Import MonadNotation.
Import ListNotations.
Import Monads.
Open Scope monad_scope.

(*|
A handler for ``Fetch`` that peels a byte off the head of a list.
If the list is empty, we simply return zeros instead of signaling an error.
|*)

Definition handle_fetch {E} : FetchE ~> stateT (list u8) (itree E) :=
  fun _ 'Fetch xs =>
    match xs with
    | []       => ret ([], 0x00)
    | x :: xs' => ret (xs', x)
    end.

Definition interp_fetch {E R}
    : itree (FetchE +' E) R -> stateT (list u8) (itree E) R :=
  fun R => interp_state (case_ handle_fetch pure_state) R.


(*|
We can interpret ``asm_decode`` using the ``handle_fetch`` handler:
``decode_list`` is an itree that decodes assembly instructions from
a list of bytes. It returns the decoded instruction, as well as the
remaining bytes.
|*)

Definition decode_list 
    : list u8 -> itree void1 (list u8 * instr) :=
  interp_fetch asm_decode.

(* Compute burn 8 (decode_list [0xFA; 0x34; 0x12]). *)
(* =>  = Ret ([], $[LD A, [#0x1234]])
       : itree void1 (list u8 * instr)
*)

Lemma interp_fetch_ret : forall E R x xs,
  @interp_fetch E R (Ret x) xs ≈ Ret (xs, x).
Proof.
  intros.
  unfold interp_fetch. 
  rewrite interp_state_ret.
  reflexivity.
Qed.

Lemma interp_fetch_bind : forall E R S xs,
  forall (t : itree (FetchE +' E) R)
         (k : R -> itree (FetchE +' E) S),
    @interp_fetch E S (t >>= k) xs
    ≈
    @interp_fetch E R t xs >>= (fun '(xs', x) => @interp_fetch E S (k x) xs').
Proof.
  intros.
  unfold interp_fetch.
  rewrite interp_state_bind.
  eapply eutt_clo_bind.
  reflexivity.
  intros.
  rewrite H.
  destruct u2. cbn.
  reflexivity.
Qed.

Lemma interp_fetch_trigger_fetch : forall E x xs,
  @interp_fetch E _ fetch (x :: xs) ≈ Ret (xs, x).
Proof.
  intros.
  unfold interp_fetch, fetch.
  rewrite interp_state_trigger. cbn.
  reflexivity.
Qed. 

Lemma interp_fetch_bind_fetch : forall E R x xs k,
  @interp_fetch E R (x <- fetch ;; k x) (x :: xs) 
  ≈
  @interp_fetch E R (k x) xs.
Proof.
  intros.
  rewrite interp_fetch_bind.
  rewrite interp_fetch_trigger_fetch.
  rewrite Eqit.bind_ret_l.
  reflexivity.
Qed.

Lemma interp_fetch_trigger_fetch16 : forall E lo hi xs,
  @interp_fetch E _ fetch16 (lo :: hi :: xs)
  ≈
  Ret (xs, Uint16.concat hi lo).
Proof.
  intros.
  unfold fetch16.
  rewrite interp_fetch_bind_fetch. cbn.
  rewrite interp_fetch_bind_fetch. cbn.
  rewrite interp_fetch_ret.
  reflexivity.
Qed. 

Lemma interp_fetch_bind_fetch16 : forall E R hi lo xs k,
  @interp_fetch E R (x <- fetch16;; k x) (lo :: hi :: xs) 
  ≈
  @interp_fetch E R (k (Uint16.concat hi lo)) xs.
Proof.
  intros.
  rewrite interp_fetch_bind.
  rewrite interp_fetch_trigger_fetch16.
  rewrite Eqit.bind_ret_l.
  reflexivity.
Qed.

Lemma concat_hi_lo : forall w,
  Uint16.concat (Uint16.hi w) (Uint16.lo w) = w.
Proof.
  unfold Uint16.concat, Uint16.hi, Uint16.lo.
  (* TODO: eta conversion? *)
Admitted.

(*|
Now we can prove that ``asm_encode`` and ``asm_decode`` are in harmony.
|*)

Lemma decode_encode : forall (i : instr),
  @interp_fetch void1 _ asm_decode (asm_encode i) ≈ Ret ([], i).
Proof.
  intros.
  unfold asm_decode.
(*|
The encode function is written as one giant match statement. We first
destruct the ``instr`` at hand, but we then need to go further and destruct
any register, conditional, etc for each instruction.  This enumerates
all 511 cases.
|*)
  destruct i; cbn.
  all: repeat match goal with 
    | x : reg8 |- _ => destruct x
    | x : bcde |- _ => destruct x
    | x : bcdehl |- _ => destruct x
    | x : preg16 |- _ => destruct x
    | x : qreg16 |- _ => destruct x
    | x : sreg16 |- _ => destruct x
    | x : bitindex |- _ => destruct x
    | x : option cond |- _ => destruct x
    | x : cond |- _ => destruct x
    | x : rst |- _ => destruct x
    | x : unknownop |- _ => destruct x
  end.
(*|
All goals are waiting to read the opcode. We advance every goal by
stepping over the fetch. We then keep stepping over fetches until
we get to a `Ret`. Most are solvable by reflexivity.
|*)
  all: rewrite interp_fetch_bind_fetch; cbn.
  all: repeat match goal with
    | |- interp_fetch (Ret _) _ ≈ _ =>
        rewrite interp_fetch_ret; try reflexivity
    | |- interp_fetch (_ <- fetch;; _) (_ :: _) ≈ _ =>
        rewrite interp_fetch_bind_fetch; cbn
    | |- interp_fetch (_ <- fetch16;; _) (_ :: _) ≈ _ =>
        rewrite interp_fetch_bind_fetch16; cbn
  end.
  all: rewrite concat_hi_lo.
  all: reflexivity.
Qed.

Section Disassembly.
Context {Mem : Type}.
Context {IsMap : Map N u8 Mem}.

Definition read_byte (mem : Mem) (addr : u16) : u8 :=
  match lookup (Uint16.to_N addr) mem with
  | Some x => x
  | None => 0
  end.

(*|
``read mem addr n`` reads a sequence of ``n`` bytes at a given ``addr``.
|*)

Definition read (mem : Mem) (addr : u16) (n : nat) : list u8 :=
  let fix rec acc n {struct n} :=
    match n with
    | O    => acc (* Note: we read bytes backwards. No rev here. *)
    | S n' => rec (read_byte mem (addr + Uint16.wrapN (N.of_nat n'))%u16 :: acc) n'
    end
  in rec [] n.

(*|
``handle_fetch_mem`` fetches bytes from memory. It's useful for
disassembling instructions at arbitrary addresses.
|*)
    
Definition handle_fetch_mem {E} : Mem -> FetchE ~> stateT u16 (itree E) :=
  fun rom _ e addr => match e with
    | Fetch => ret (Uint16.succ addr, read_byte rom addr)
  end.

Definition interp_fetch_mem {E}
    : Mem -> itree (FetchE +' E) ~> stateT u16 (itree E) :=
  fun mem => interp_state (case_ (handle_fetch_mem mem) pure_state).

(*|
``disassemble1 rom offset`` decodes a single assembly instruction at a
given ``addr`` in memory. It returns the decoded instruction as well as
the adjusted offset.
|*)

Definition disassemble1 {E} : Mem -> u16 -> itree E (u16 * instr) :=
  fun mem => interp_fetch_mem mem _ asm_decode.

(* [disassemble k] disassembles a run of [k] instructions. Each instruction
   is paired with its location in the ROM. Returns the list of instructions
   as well as the final adjusted offset. *)

Definition disassemble {E} (n : nat) (mem : Mem) (offset : u16)
    : itree E (list (u16 * instr) * u16) :=
  let fix rec acc offset n {struct n} :=
    match n with
    | O    => ret (List.rev acc, offset)
    | S n' => '(offset', op) <- disassemble1 mem offset ;;
              rec ((offset, op) :: acc) offset' n'
    end
  in rec [] offset n.

End Disassembly.

From GameBoy Require Import Test.Roms.cpu_instrs.
Section DisassemblyExamples.

(** The following code demonstrates how to disassemble parts of a ROM.
    The ROM used to test this is the "cpu_instrs" ROM from Blargg's test
    repository, which can be found here:
    
      https://github.com/retrio/gb-test-roms/tree/c240dd7d700e5c0b00a7bbba52b53e4ee67b5f15/cpu_instrs
      
    A local copy of the rom is avilable in the [Test.Roms.cpu_instrs]
    module.  The rom binary has been converted to a Rocq expression
    using the utility in tools/rom2rocq. It's imported and available
    as [rom]: *)

(* Check rom. *)
(* => rom : nmap u8 *)

Set Printing Depth 10.
Local Definition fuel : nat := 1024.

(** Aside: make sure we burn enough fuel! An unnormalized expression will
    contain the rom as a subterm. The rom is a binary tree with 64k+
    entries. Coq will grind to a halt trying to print it. We can 
    set the max printing depth to help truncate large outputs, but
    this is only a hack. *)

(** When the GameBoy boots, the entry point is always address 0x0100. The
    entry point almost always is a NOP followed by a JP. In this example,
    we immediately jump to address 0x0637. *)

(* Compute (burn fuel (disassemble 2 rom 0x100)). *)
(*    = Ret ([(256%N, $[NOP]);
              (257%N, $[JP #0x637])],
             260%N)
      : itree ?E (list (N * instr) * N)
*)

(** If we disassmble the code at 0x0637, we can see we're immediately
    redirected yet again to address 0x0430. *)

(* Compute (burn fuel (disassemble 2 rom 0x637)). *)
(*    = Ret ([(1591%N, $[JP #0x430]);
              (1594%N, $[RET])],
             1595%N)
      : itree ?E (list (N * instr) * N)
*)

(** Address 0x0430 has some real code. This is the setup function called
    before main. The source code can be found here:
    
      https://github.com/retrio/gb-test-roms/blob/c240dd7d700e5c0b00a7bbba52b53e4ee67b5f15/cpu_instrs/source/common/runtime.s#L72,L108 *)

(* Compute (burn fuel (disassemble 33 rom 0x430)). *)
(*    = Ret
          ([(1072%N, $[DI]);
            (1073%N, $[LDW SP, #0xdfff]);
            (1076%N, $[LD [#0xd600], A]);
            (1079%N, $[LD A, #0x0]);
            (1081%N, $[LDH [#0x7], A]);
            (1083%N, $[LD A, #0x0]);
            (1085%N, $[LDH [#0xf], A]);
            (1087%N, $[LD A, #0x0]);
            (1089%N, $[LDH [#0xff], A]);
            (1091%N, $[LD A, #0x0]);
            (1093%N, $[LDH [#0x26], A]);
            (1095%N, $[LD A, #0x80]);
            (1097%N, $[LDH [#0x26], A]);
            (1099%N, $[LD A, #0xff]);
            (1101%N, $[LDH [#0x25], A]);
            (1103%N, $[LD A, #0x77]);
            (1105%N, $[LDH [#0x24], A]);
            (1107%N, $[LDW HL, #0xb8f]);
            (1110%N, $[CALL #0x2a3]);
            (1113%N, $[CALL #0x38e]);
            (1116%N, $[CALL #0xb79]);
            (1119%N, $[CALL #0x25f]);
            (1122%N, $[PUSH AF]);
            (1123%N, $[LD A, #0x3]);
            (1125%N, $[CALL #0x22f]);
            (1128%N, $[LD A, #0xff]);
            (1130%N, $[CALL #0x222]);
            (1133%N, $[LD A, #0xcd]);
            (1135%N, $[CALL #0x213]);
            (1138%N, $[POP AF]);
            (1139%N, $[CALL #0x63b]);
            (1142%N, $[LD A, #0x0]);
            (1144%N, $[JP #0x47b])],
          1147%N)
     : itree ?E (N * list (N * instr))
*)

End DisassemblyExamples.
