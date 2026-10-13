From Stdlib Require Import
  ZArith
  Morphisms
  List.

From ITree Require Import
  ITree
  ITreeFacts
  ITreeDefinition
  Indexed.Sum
  Events.State
  Events.StateFacts.

From ExtLib Require Import
  Structures.Maps
  Structures.Reducible
  Data.Map.FMapPositive.

From GameBoy Require Import
  Stdint
  Data.Map.FMapNat
  Asm
  AsmEncoding
  AsmFacts
  CpuSemantics
  Test.Roms.cpu_instrs.

Import ITreeNotations.
Import MonadNotation.
Import ListNotations.
Import Monads.


Record regfile := RegFile {
  a : u8;
  b : u8;
  c : u8;
  d : u8;
  e : u8;
  f : u8;
  h : u8;
  l : u8;
  sp : u16;
  pc : u16;
}.

Definition regfile_zeroed :=
  {|
    a := 0x00;
    b := 0x00;
    c := 0x00;
    d := 0x00;
    e := 0x00;
    f := 0x00;
    h := 0x00;
    l := 0x00;
    sp := 0x0000;
    pc := 0x0000;
  |}.

Definition regfile_init :=
  {|
    a := 0x01;
    b := 0x00;
    c := 0x13;
    d := 0x00;
    e := 0xd8;
    f := 0xB0;
    h := 0x01;
    l := 0x4D;
    sp := 0xfffe;
    pc := 0x0100;
  |}.

Definition regfile_get8 (rf : regfile) (r : reg8) : u8 :=
  match r with
  | A => rf.(a)
  | B => rf.(b)
  | C => rf.(c)
  | D => rf.(d) 
  | E => rf.(e)
  | F => rf.(f)
  | H => rf.(h)
  | L => rf.(l) 
  end.

Definition regfile_get16 (rf : regfile) (r : reg16) : u16 :=
  match r with
  | SP => rf.(sp)
  | PC => rf.(pc)
  end.

(** Ugh! Rocq has no record update syntax. *)

Definition regfile_set8 (rf : regfile) (r : reg8) (x : u8) : regfile :=
  let '(RegFile a b c d e f h l sp pc) := rf in
  match r with
  | A => RegFile x b c d e f h l sp pc
  | B => RegFile a x c d e f h l sp pc
  | C => RegFile a b x d e f h l sp pc
  | D => RegFile a b c x e f h l sp pc
  | E => RegFile a b c d x f h l sp pc
  | F => RegFile a b c d e x h l sp pc
  | H => RegFile a b c d e f x l sp pc
  | L => RegFile a b c d e f h x sp pc
  end.

Definition regfile_set16 (rf : regfile) (r : reg16) (x : u16) : regfile :=
  let '(RegFile a b c d e f h l sp pc) := rf in
  match r with
  | SP => RegFile a b c d e f h l x pc
  | PC => RegFile a b c d e f h l sp x
  end.

Definition regfile_map8 (rf : regfile) (r : reg8) (f : u8 -> u8) : regfile :=
  let v := regfile_get8 rf r in
  regfile_set8 rf r (f v).

Definition regfile_map16 (rf : regfile) (r : reg16) (f : u16 -> u16) : regfile :=
  let v := regfile_get16 rf r in
  regfile_set16 rf r (f v).

(* Definition handle_cpu {E} : forall R, CpuE R -> regfile -> itree E (regfile * R) *)
Definition handle_cpu {E} : CpuE ~> stateT regfile (itree E)
  := fun _ e regs => match e with 
    | GetReg8 r => ret (regs, regfile_get8 regs r)
    | GetReg16 r => ret (regs, regfile_get16 regs r)
    | SetReg8 r x => ret (regfile_set8 regs r x, tt)
    | SetReg16 r x => ret (regfile_set16 regs r x, tt)
    | SetIme _ => ret (regs, tt) (* TODO! *)
    end.

(* Note: we could translate MemE events to mapE events, but we skip 
   the ceremony and use `nmap u8` directly. *)

Definition handle_mem {E} : MemE ~> stateT (nmap u8) (itree E)
  := fun _ e mem => match e with
    | MemRead x => ret (mem, read_byte mem x)
    | MemWrite x v => ret (nmap_insert (Uint16.to_N x) v mem, tt)
    end.


Definition interp_cpu {E} : itree (CpuE +' E) ~> stateT regfile (itree E)
  := interp_state (case_ handle_cpu pure_state).

Definition interp_mem {E} : itree (MemE +' E) ~> stateT (nmap u8) (itree E)
  := interp_state (case_ handle_mem pure_state).

Definition interp_gameboy {R}
     : itree (CpuE +' MemE +' void1) R
    -> regfile 
    -> nmap u8
    -> itree void1 (nmap u8 * (regfile * R)) :=
  fun t regs mem => (interp_mem _ (interp_cpu _ t regs)) mem.

(* The gameboy interpreter is compatible with the equivalence-up-to-tau. 
   This allows us to perform setoid rewrites within the interpreter. *)

#[global]
Instance eutt_interp_gameboy {R} :
  Proper (@eutt (CpuE +' MemE +' void1) R R eq 
    ==> eq 
    ==> eq 
    ==> @eutt void1 (nmap u8 * (regfile * R)) _ eq) interp_gameboy.
Proof.
  repeat intro.
  unfold interp_gameboy, interp_cpu, interp_mem.
  rewrite H, H0, H1.
  reflexivity.
Qed.

Lemma interp_gameboy_ret : forall R x regs mem,
  @interp_gameboy R (Ret x) regs mem ≈ Ret (mem, (regs, x)).
Proof.
  intros.
  unfold interp_gameboy.
  unfold interp_mem, interp_cpu.
  repeat rewrite interp_state_ret.
  reflexivity.
Qed.

Lemma interp_gameboy_bind : forall R1 R2 regs mem t k,
  @interp_gameboy R2 (t >>= k) regs mem
  ≈
  @interp_gameboy R1 t regs mem 
      >>= (fun '(mem', (regs', x)) => @interp_gameboy R2 (k x) regs' mem').
Proof.
  intros.
  unfold interp_gameboy, interp_mem, interp_cpu.
  repeat rewrite interp_state_bind.
  eapply eutt_clo_bind.
  reflexivity.
  intros.
  rewrite <- H; clear H.
  destruct u1 as (?&?&?).
  simpl.
  reflexivity.
Qed.


Lemma interp_gameboy_getreg8 : forall regs mem r,
  interp_gameboy (trigger (GetReg8 r)) regs mem
  ≈
  Ret (mem, (regs, regfile_get8 regs r)).
Proof.
  intros.
  unfold interp_gameboy, interp_cpu, interp_mem.
  rewrite interp_state_trigger. cbn.
  repeat rewrite interp_state_ret. 
  reflexivity.
Qed.

Lemma interp_gameboy_bind_getreg8 : forall R regs mem r k,
  @interp_gameboy R (x <- trigger (GetReg8 r);; k x) regs mem
  ≈
  @interp_gameboy R (k (regfile_get8 regs r)) regs mem.
Proof.
  intros.
  rewrite interp_gameboy_bind.
  rewrite interp_gameboy_getreg8.
  rewrite bind_ret_l.
  reflexivity.
Qed.

Lemma interp_gameboy_getreg16 : forall regs mem r,
  interp_gameboy (trigger (GetReg16 r)) regs mem
  ≈
  Ret (mem, (regs, regfile_get16 regs r)).
Proof.
  intros.
  unfold interp_gameboy, interp_cpu, interp_mem.
  rewrite interp_state_trigger. cbn.
  repeat rewrite interp_state_ret. 
  reflexivity.
Qed.

Lemma interp_gameboy_bind_getreg16 : forall R regs mem r k,
  @interp_gameboy R (x <- trigger (GetReg16 r);; k x) regs mem
  ≈
  @interp_gameboy R (k (regfile_get16 regs r)) regs mem.
Proof.
  intros.
  rewrite interp_gameboy_bind.
  rewrite interp_gameboy_getreg16.
  rewrite bind_ret_l.
  reflexivity.
Qed.

Lemma interp_gameboy_setreg8 : forall regs mem r x,
  interp_gameboy (trigger (SetReg8 r x)) regs mem
  ≈
  Ret (mem, (regfile_set8 regs r x, tt)).
Proof.
  intros.
  unfold interp_gameboy, interp_cpu, interp_mem.
  rewrite interp_state_trigger. cbn.
  repeat rewrite interp_state_ret. 
  reflexivity.
Qed.

Lemma interp_gameboy_bind_setreg8 : forall R regs mem r x k,
  @interp_gameboy R (trigger (SetReg8 r x);; k) regs mem
  ≈
  @interp_gameboy R k (regfile_set8 regs r x) mem.
Proof.
  intros.
  rewrite interp_gameboy_bind.
  rewrite interp_gameboy_setreg8.
  rewrite bind_ret_l.
  reflexivity.
Qed.

Lemma interp_gameboy_setreg16 : forall regs mem r x,
  interp_gameboy (trigger (SetReg16 r x)) regs mem
  ≈
  Ret (mem, (regfile_set16 regs r x, tt)).
Proof.
  intros.
  unfold interp_gameboy, interp_cpu, interp_mem.
  rewrite interp_state_trigger. cbn.
  repeat rewrite interp_state_ret. 
  reflexivity.
Qed.

Lemma interp_gameboy_bind_setreg16 : forall R regs mem r x k,
  @interp_gameboy R (trigger (SetReg16 r x);; k) regs mem
  ≈
  @interp_gameboy R k (regfile_set16 regs r x) mem .
Proof.
  intros.
  rewrite interp_gameboy_bind.
  rewrite interp_gameboy_setreg16.
  rewrite bind_ret_l.
  reflexivity.
Qed.

Lemma interp_gameboy_memread : forall regs mem addr,
  (* interp_gameboy (trigger (MemRead addr)) regs mem *)
  interp_gameboy (memread addr) regs mem
  ≈
  Ret (mem, (regs, (read_byte mem addr))).
Proof.
  (* intros.
  unfold interp_gameboy, interp_cpu, interp_mem.
  rewrite interp_state_trigger. cbn.
  repeat rewrite interp_state_ret.  *)
Admitted.

Lemma interp_gameboy_fetch : forall R regs mem k,
  @interp_gameboy R (interp handle_fetch (x <- fetch;; k x)) regs mem
  ≈
  @interp_gameboy R
    (interp handle_fetch (k (read_byte mem (regs.(pc)))))
    (regfile_set16 regs PC (Uint16.succ (pc regs))) mem.
Proof.
  intros.
  rewrite interp_bind. unfold fetch.
  rewrite interp_trigger; cbn.
  repeat rewrite interp_gameboy_bind.
  rewrite interp_gameboy_getreg16.
  rewrite bind_ret_l.
  rewrite interp_gameboy_memread.
  rewrite bind_ret_l.
  rewrite interp_gameboy_bind.
  rewrite interp_gameboy_bind_getreg16.
  rewrite interp_gameboy_setreg16.
  rewrite bind_ret_l.
  rewrite interp_gameboy_ret.
  rewrite bind_ret_l.
  reflexivity.
Qed.

Lemma interp_gameboy_fetch16 : forall R regs mem k,
  @interp_gameboy R (interp handle_fetch (x <- fetch16;; k x)) regs mem
  ≈
  @interp_gameboy R
    (interp handle_fetch (k (read_u16le mem (regs.(pc)))))
    (regfile_set16 regs PC (regs.(pc) + 2))%u16 mem.
Proof.
  intros.
  rewrite interp_bind. unfold fetch16.
  rewrite interp_gameboy_bind.
  rewrite interp_gameboy_fetch. cbn.
  rewrite interp_gameboy_fetch.
  rewrite interp_ret.
  rewrite interp_gameboy_ret.
  rewrite bind_ret_l.
Admitted.


Example stepping_through : forall R, exists RESULT,
  @interp_gameboy R (ITree.forever denote_step) regfile_init rom
  ≈
  ret RESULT.
Proof.
  intros.
  eapply ex_intro.
  unfold regfile_init.

  rewrite unfold_forever.
  unfold denote_step.
  rewrite interp_gameboy_bind.
  rewrite interp_gameboy_bind.
  unfold denote_fetch, asm_decode.
  rewrite interp_gameboy_fetch; cbn.
  rewrite interp_ret.
  rewrite interp_gameboy_ret.
  rewrite bind_ret_l. cbn.
  rewrite interp_gameboy_ret.
  rewrite bind_ret_l.
  rewrite tau_eutt.

  rewrite unfold_forever.
  rewrite interp_gameboy_bind.
  rewrite interp_gameboy_bind.
  rewrite interp_gameboy_fetch; cbn.
  rewrite interp_gameboy_fetch16. cbn.
  unfold read_u16le, Uint16.concat; cbn.
  rewrite interp_ret.
  rewrite interp_gameboy_ret.
  rewrite bind_ret_l. cbn.
  rewrite interp_gameboy_setreg16. cbn.
  rewrite bind_ret_l.
  rewrite tau_eutt.

  rewrite unfold_forever.
  rewrite interp_gameboy_bind.
  rewrite interp_gameboy_bind.
  rewrite interp_gameboy_fetch; cbn.
  rewrite interp_gameboy_fetch16. cbn.
  unfold read_u16le, Uint16.concat; cbn.
  rewrite interp_ret.
  rewrite interp_gameboy_ret.
  rewrite bind_ret_l. cbn.
  rewrite interp_gameboy_setreg16. cbn.
  rewrite bind_ret_l.
  rewrite tau_eutt.
Abort.
