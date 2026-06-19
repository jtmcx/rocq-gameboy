From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From GameBoy.Stdint Require Export Byte.
Local Open Scope bool_scope.

(*|
This module defines machine-width integers. It defines the
types ``Int8.t``, ``Int16.t``, ``Uint8.t``, and ``Uint16.t``
(abbreviated as ``i8``, ``i16``, ``u8``, and ``u16``,
respectively). It takes heavy inspiration from the `Integers
<https://compcert.org/doc/html/compcert.lib.Integers.html>`_ module
in Compcert.

Each integer type has its own notation scope (including number notations),
which make it easy to perform arbitrary modular arithmetic in Rocq::

    Compute ((0x55 .^ 0xAA) + 0x42)%u8.
        = 0x41%u8 : Uint8.t

The definitions in this file roughly mirror the definitions in the
`ocaml-stdint <https://ocaml.org/p/stdint/latest>`_ library. Extracting
code after importing ``StdintExtraction`` will generate OCaml code that
uses the ocaml-stdint library. (This is a work in progress).

Definitions
-----------------------------------------------------------------------

We start by defining a functor ``MakeInt`` that provides operations
common to all integers. It's parameterized by ``IntType``, which defines
the integer's underlying type ``t``, its width, and some functions that
convert between ``t`` and ``N``. Conversions to and from ``N`` must be
coherent, so we require some proofs concerning round-trips.

All integer operations (add, sub, etc) are defined roughly the same
way: we first convert any ``IntType.t`` into an ``N`` or ``Z``, perform
the operation in that domain, and then wrap the result using ``wrapN``
or ``wrapZ``. Note that ``MakeInt`` defines both signed *and* unsigned
operations for a given ``IntType``.
|*)

Module Type IntType.
  Parameter t : Type.
  Parameter width : positive.
  Parameter to_N : t -> N.
  Parameter wrapN : N -> t.

  Parameter wrap_to_N : forall x,
    wrapN (to_N x) = x.
  Parameter to_N_wrap : forall n, 
    to_N (wrapN n) = (n mod 2^(Npos width))%N.
End IntType.

Module MakeInt(I : IntType).
  Include I.

  Definition modulus : N := 2 ^ (Npos width).
  Definition half_modulus : N := modulus / 2.
  Definition zmodulus : Z := 2 ^ (Zpos width).
  Definition zhalf_modulus : Z := zmodulus / 2.

  Definition to_Z : t -> Z :=
    fun x => let z := Z.of_N (to_N x) in 
      if (zhalf_modulus <=? z)%Z then (z - zmodulus)%Z else z.

  Definition wrapZ : Z -> t :=
    fun z => wrapN (Z.to_N (z mod zmodulus)).

  Definition in_signed_range : Z -> bool :=
    fun z => (-zhalf_modulus <=? z)%Z && (z <? zhalf_modulus)%Z.

  Definition in_unsigned_range : N -> bool :=
    fun n => (n <? modulus)%N.

  Definition add : t -> t -> t :=
    fun x y => wrapZ (to_Z x + to_Z y).

  Definition sub : t -> t -> t :=
    fun x y => wrapZ (to_Z x - to_Z y).

  Definition mul : t -> t -> t :=
    fun x y => wrapZ (to_Z x * to_Z y).

  Definition succ : t -> t :=
    fun x => wrapZ (Z.succ (to_Z x)).

  Definition pred : t -> t :=
    fun x => wrapZ (Z.pred (to_Z x)).

  Definition land : t -> t -> t :=
    fun x y => wrapN (N.land (to_N x) (to_N y)).

  Definition lor : t -> t -> t :=
    fun x y => wrapN (N.lor (to_N x) (to_N y)).

  Definition lxor : t -> t -> t :=
    fun x y => wrapN (N.lxor (to_N x) (to_N y)).

  Definition lnot : t -> t :=
    fun x => wrapN (N.lnot (to_N x) 8).

  Definition shl : t -> t -> t :=
    fun x k => wrapN (N.shiftl (to_N x) (to_N k)).

  Definition unsigned_shr : t -> t -> t :=
    fun x k => wrapN (N.shiftr (to_N x) (to_N k)).

  Definition signed_shr : t -> t -> t :=
    fun x k => wrapZ (Z.shiftr (to_Z x) (Z.of_N (to_N k))).

  Definition eqb : t -> t -> bool :=
    fun x y => N.eqb (to_N x) (to_N y).

  Definition signed_compare : t -> t -> comparison :=
    fun x y => Z.compare (to_Z x) (to_Z y).

  Definition unsigned_compare : t -> t -> comparison :=
    fun x y => N.compare (to_N x) (to_N y).

  Definition signed_ltb : t -> t -> bool :=
    fun x y => Z.ltb (to_Z x) (to_Z y).

  Definition unsigned_ltb : t -> t -> bool :=
    fun x y => N.ltb (to_N x) (to_N y).

  Definition signed_leb : t -> t -> bool :=
    fun x y => Z.leb (to_Z x) (to_Z y).

  Definition unsigned_leb : t -> t -> bool :=
    fun x y => N.leb (to_N x) (to_N y).

  Definition signed_gtb : t -> t -> bool :=
    fun x y => Z.ltb (to_Z y) (to_Z x).

  Definition unsigned_gtb : t -> t -> bool :=
    fun x y => N.ltb (to_N y) (to_N x).

  Definition signed_geb : t -> t -> bool :=
    fun x y => Z.leb (to_Z y) (to_Z x).

  Definition unsigned_geb : t -> t -> bool :=
    fun x y => N.leb (to_N y) (to_N x).

  Definition signed_lt : t -> t -> Prop :=
    fun x y => signed_ltb x y = true.

  Definition unsigned_lt : t -> t -> Prop :=
    fun x y => unsigned_ltb x y = true.

  Definition signed_le : t -> t -> Prop :=
    fun x y => signed_leb x y = true.

  Definition unsigned_le : t -> t -> Prop :=
    fun x y => unsigned_leb x y = true.

  Definition signed_ge : t -> t -> Prop :=
    fun x y => signed_geb x y = true.

  Definition unsigned_ge : t -> t -> Prop :=
    fun x y => unsigned_geb x y = true.

  Definition signed_gt : t -> t -> Prop :=
    fun x y => signed_gtb x y = true.

  Definition unsigned_gt : t -> t -> Prop :=
    fun x y => unsigned_gtb x y = true.

  Definition to_num_signed : t -> Number.int :=
    fun b => Z.to_num_int (to_Z b).

  Definition to_num_unsigned : t -> Number.uint :=
    fun b => N.to_num_uint (to_N b).

  Definition to_hex_signed : t -> Number.int :=
    fun b => Z.to_num_hex_int (to_Z b).

  Definition to_hex_unsigned : t -> Number.uint :=
    fun b => N.to_num_hex_uint (to_N b).

  Definition of_num_signed : Number.int -> option t :=
    fun i => let z := Z.of_num_int i in
      if in_signed_range z then Some (wrapZ z) else None.

  Definition of_num_unsigned : Number.uint -> option t :=
    fun i => let n := N.of_num_uint i in
      if in_unsigned_range n then Some (wrapN n) else None.

End MakeInt.

(*|
``IntOps`` defines an interface common to all integer types. The ``Int8``,
``Int16``, ``Uint8`` and ``Uint16`` modules all implement this interface.
Note that some operations behave differently for signed and unsigned
integers. In particular, ``shr`` is a logical right shift if ``t``
is unsigned, and arithmetic if ``t`` is signed.
|*)

Module Type IntOps.
  Include IntType.
  Parameter add : t -> t -> t.
  Parameter sub : t -> t -> t.
  Parameter mul : t -> t -> t.
  Parameter succ : t -> t.
  Parameter pred : t -> t.
  Parameter land : t -> t -> t.
  Parameter lor : t -> t -> t.
  Parameter lxor : t -> t -> t.
  Parameter lnot : t -> t.
  Parameter shl : t -> t -> t.
  Parameter shr : t -> t -> t.
  Parameter lt : t -> t -> Prop.
  Parameter le : t -> t -> Prop.
  Parameter ge : t -> t -> Prop.
  Parameter gt : t -> t -> Prop.
  Parameter compare : t -> t -> comparison.
  Parameter eqb : t -> t -> bool.
  Parameter ltb : t -> t -> bool.
  Parameter leb : t -> t -> bool.
  Parameter geb : t -> t -> bool.
  Parameter gtb : t -> t -> bool.
  Parameter max_int : t.
  Parameter min_int : t.
End IntOps.


Module Int8Type <: IntType.
  Definition t := byte.
  Definition width := 8%positive.
  Definition wrapN := Byte.of_N.
  Definition to_N := Byte.to_N.
  Definition wrap_to_N := Byte.byte_N_roundtrip.
  Definition to_N_wrap := Byte.N_byte_roundtrip.
End Int8Type.

(*|
16-bit integers are defined as a pair of bytes. Note that this type must
be an inductive definition in order to support ``Number Notation``.
|*)

Record word16 := Word16 { hi : byte; lo : byte }.

Module Int16Type <: IntType.
  Definition t := word16.
  Definition width := 16%positive.

  Definition to_N x : N :=
    (Byte.to_N x.(hi)) * 256 + (Byte.to_N x.(lo)).
  Definition wrapN n :=
    {| hi := Byte.of_N (n / 256); lo := Byte.of_N n |}.

  (* TODO! *)
  Axiom wrap_to_N : forall x,
    wrapN (to_N x) = x.
  Axiom to_N_wrap : forall n,
    to_N (wrapN n) = (n mod 2^(Npos width))%N.
End Int16Type.


Module Int8 <: IntOps.
  Include MakeInt(Int8Type).
  Definition shr := signed_shr.
  Definition lt := signed_lt.
  Definition le := signed_le.
  Definition ge := signed_ge.
  Definition gt := signed_gt.
  Definition compare := signed_compare.
  Definition ltb := signed_ltb.
  Definition leb := signed_leb.
  Definition geb := signed_geb.
  Definition gtb := signed_gtb.
  Definition min_int : t := x80.
  Definition max_int : t := x7F.
End Int8.

Module Uint8 <: IntOps.
  Include MakeInt(Int8Type).
  Definition shr := unsigned_shr.
  Definition lt := unsigned_lt.
  Definition le := unsigned_le.
  Definition ge := unsigned_ge.
  Definition gt := unsigned_gt.
  Definition compare := unsigned_compare.
  Definition ltb := unsigned_ltb.
  Definition leb := unsigned_leb.
  Definition geb := unsigned_geb.
  Definition gtb := unsigned_gtb.
  Definition min_int : t := x00.
  Definition max_int : t := xFF.
End Uint8.

Module Int16 <: IntOps.
  Include MakeInt(Int16Type).
  Definition shr := signed_shr.
  Definition lt := signed_lt.
  Definition le := signed_le.
  Definition ge := signed_ge.
  Definition gt := signed_gt.
  Definition compare := signed_compare.
  Definition ltb := signed_ltb.
  Definition leb := signed_leb.
  Definition geb := signed_geb.
  Definition gtb := signed_gtb.
  Definition min_int : t := {| hi := x80; lo := x00 |}.
  Definition max_int : t := {| hi := x7F; lo := xFF |}.
  Definition concat : byte -> byte -> t := Word16.
  Definition hi := fun x => x.(hi).
  Definition lo := fun x => x.(lo).
End Int16.

Module Uint16 <: IntOps.
  Include MakeInt(Int16Type).
  Definition shr := unsigned_shr.
  Definition lt := unsigned_lt.
  Definition le := unsigned_le.
  Definition ge := unsigned_ge.
  Definition gt := unsigned_gt.
  Definition compare := unsigned_compare.
  Definition ltb := unsigned_ltb.
  Definition leb := unsigned_leb.
  Definition geb := unsigned_geb.
  Definition gtb := unsigned_gtb.
  Definition min_int : t := {| hi := x00; lo := x00 |}.
  Definition max_int : t := {| hi := xFF; lo := xFF |}.
  Definition concat : byte -> byte -> t := Word16.
  Definition hi := fun x => x.(hi).
  Definition lo := fun x => x.(lo).
End Uint16.

Definition i8 : Type := Int8.t.
Definition i16 : Type := Int16.t.
Definition u8 : Type := Uint8.t.
Definition u16 : Type := Uint16.t.

(*|
Notations
-----------------------------------------------------------------------

Unfortunately, we can't parameterize notations by scope, so we have to
define the same notations for each integer type.
|*)

Declare Scope i8_scope.
Delimit Scope i8_scope with i8.
Bind Scope i8_scope with i8.

Number Notation byte 
  Int8.of_num_signed Int8.to_hex_signed : i8_scope.

Notation "x + y"  := (Int8.add x y) : i8_scope.
Notation "x - y"  := (Int8.sub x y) : i8_scope.
Notation "x * y"  := (Int8.mul x y) : i8_scope.
Notation "x .& y" := (Int8.land x y) (at level 40) : i8_scope.
Notation "x .| y" := (Int8.lor x y) (at level 40) : i8_scope.
Notation "x .^ y" := (Int8.lxor x y) (at level 40) : i8_scope.
Notation ".~ x"   := (Int8.lnot x) (at level 35) : i8_scope.
Notation "x << y" := (Int8.shl x y) (at level 40) : i8_scope.
Notation "x >> y" := (Int8.shr x y) (at level 40) : i8_scope.
Notation "x < y"  := (Int8.lt x y) : i8_scope.
Notation "x <= y" := (Int8.le x y) : i8_scope.
Notation "x >= y" := (Int8.ge x y) : i8_scope.
Notation "x > y"  := (Int8.gt x y) : i8_scope.
Notation "x ?= y" := (Int8.compare x y) : i8_scope.
Notation "x <? y" := (Int8.ltb x y) : i8_scope.
Notation "x <=? y":= (Int8.leb x y) : i8_scope.
Notation "x =? y" := (Int8.eqb x y) : i8_scope.
Notation "x >=? y":= (Int8.geb x y) : i8_scope.
Notation "x >? y" := (Int8.gtb x y) : i8_scope.

Declare Scope u8_scope.
Delimit Scope u8_scope with u8.
Bind Scope u8_scope with u8.

Number Notation byte
  Uint8.of_num_unsigned Uint8.to_hex_unsigned : u8_scope.

Notation "x + y"  := (Uint8.add x y) : u8_scope.
Notation "x - y"  := (Uint8.sub x y) : u8_scope.
Notation "x * y"  := (Uint8.mul x y) : u8_scope.
Notation "x .& y" := (Uint8.land x y) (at level 40) : u8_scope.
Notation "x .| y" := (Uint8.lor x y) (at level 40) : u8_scope.
Notation "x .^ y" := (Uint8.lxor x y) (at level 40) : u8_scope.
Notation ".~ x"   := (Uint8.lnot x) (at level 35) : u8_scope.
Notation "x << y" := (Uint8.shl x y) (at level 40) : u8_scope.
Notation "x >> y" := (Uint8.shr x y) (at level 40) : u8_scope.
Notation "x < y"  := (Uint8.lt x y) : u8_scope.
Notation "x <= y" := (Uint8.le x y) : u8_scope.
Notation "x >= y" := (Uint8.ge x y) : u8_scope.
Notation "x > y"  := (Uint8.gt x y) : u8_scope.
Notation "x ?= y" := (Uint8.compare x y) : u8_scope.
Notation "x <? y" := (Uint8.ltb x y) : u8_scope.
Notation "x <=? y":= (Uint8.leb x y) : u8_scope.
Notation "x =? y" := (Uint8.eqb x y) : u8_scope.
Notation "x >=? y":= (Uint8.geb x y) : u8_scope.
Notation "x >? y" := (Uint8.gtb x y) : u8_scope.

Declare Scope i16_scope.
Delimit Scope i16_scope with i16.
Bind Scope i16_scope with i16.

Number Notation word16
  Int16.of_num_signed Int16.to_hex_signed : i16_scope.

Notation "x + y"  := (Int16.add x y) : i16_scope.
Notation "x - y"  := (Int16.sub x y) : i16_scope.
Notation "x * y"  := (Int16.mul x y) : i16_scope.
Notation "x .& y" := (Int16.land x y) (at level 40) : i16_scope.
Notation "x .| y" := (Int16.lor x y) (at level 40) : i16_scope.
Notation "x .^ y" := (Int16.lxor x y) (at level 40) : i16_scope.
Notation ".~ x"   := (Int16.lnot x) (at level 35) : i16_scope.
Notation "x << y" := (Int16.shl x y) (at level 40) : i16_scope.
Notation "x >> y" := (Int16.shr x y) (at level 40) : i16_scope.
Notation "x < y"  := (Int16.lt x y) : i16_scope.
Notation "x <= y" := (Int16.le x y) : i16_scope.
Notation "x >= y" := (Int16.ge x y) : i16_scope.
Notation "x > y"  := (Int16.gt x y) : i16_scope.
Notation "x ?= y" := (Int16.compare x y) : i16_scope.
Notation "x <? y" := (Int16.ltb x y) : i16_scope.
Notation "x <=? y":= (Int16.leb x y) : i16_scope.
Notation "x =? y" := (Int16.eqb x y) : i16_scope.
Notation "x >=? y":= (Int16.geb x y) : i16_scope.
Notation "x >? y" := (Int16.gtb x y) : i16_scope.

Declare Scope u16_scope.
Delimit Scope u16_scope with u16.
Bind Scope u16_scope with u16.

Number Notation word16
  Uint16.of_num_unsigned Uint16.to_hex_unsigned : u16_scope.

Notation "x + y"  := (Uint16.add x y) : u16_scope.
Notation "x - y"  := (Uint16.sub x y) : u16_scope.
Notation "x * y"  := (Uint16.mul x y) : u16_scope.
Notation "x .& y" := (Uint16.land x y) (at level 40) : u16_scope.
Notation "x .| y" := (Uint16.lor x y) (at level 40) : u16_scope.
Notation "x .^ y" := (Uint16.lxor x y) (at level 40) : u16_scope.
Notation ".~ x"   := (Uint16.lnot x) (at level 35) : u16_scope.
Notation "x << y" := (Uint16.shl x y) (at level 40) : u16_scope.
Notation "x >> y" := (Uint16.shr x y) (at level 40) : u16_scope.
Notation "x < y"  := (Uint16.lt x y) : u16_scope.
Notation "x <= y" := (Uint16.le x y) : u16_scope.
Notation "x >= y" := (Uint16.ge x y) : u16_scope.
Notation "x > y"  := (Uint16.gt x y) : u16_scope.
Notation "x ?= y" := (Uint16.compare x y) : u16_scope.
Notation "x <? y" := (Uint16.ltb x y) : u16_scope.
Notation "x <=? y":= (Uint16.leb x y) : u16_scope.
Notation "x =? y" := (Uint16.eqb x y) : u16_scope.
Notation "x >=? y":= (Uint16.geb x y) : u16_scope.
Notation "x >? y" := (Uint16.gtb x y) : u16_scope.

(*|
Extraction
-----------------------------------------------------------------------

This is a work in progress.
|*)

Module StdintExtraction.
(*
Extract Constant Int8.t         => "Stdint.Int8.t".
Extract Constant Int8.succ      => "Stdint.Int8.succ".
Extract Constant Int8.pred      => "Stdint.Int8.pred".
Extract Constant Int8.add       => "Stdint.Int8.add".
Extract Constant Int8.sub       => "Stdint.Int8.sub".
Extract Constant Int8.lnot      => "Stdint.Int8.lognot".
Extract Constant Int8.land      => "Stdint.Int8.logand".
Extract Constant Int8.lor       => "Stdint.Int8.logor".
Extract Constant Int8.lxor      => "Stdint.Int8.logxor".
Extract Constant Int8.max_int   => "Stdint.Int8.max_int".
Extract Constant Int8.min_int   => "Stdint.Int8.min_int".

Extract Constant Int16.t        => "Stdint.Int16.t".
Extract Constant Int16.succ     => "Stdint.Int16.succ".
Extract Constant Int16.pred     => "Stdint.Int16.pred".
Extract Constant Int16.add      => "Stdint.Int16.add".
Extract Constant Int16.sub      => "Stdint.Int16.sub".
Extract Constant Int16.lnot     => "Stdint.Int16.lognot".
Extract Constant Int16.land     => "Stdint.Int16.logand".
Extract Constant Int16.lor      => "Stdint.Int16.logor".
Extract Constant Int16.lxor     => "Stdint.Int16.logxor".
Extract Constant Int16.max_int  => "Stdint.Int16.max_int".
Extract Constant Int16.min_int  => "Stdint.Int16.min_int".

Extract Constant Uint8.t        => "Stdint.Uint8.t".
Extract Constant Uint8.succ     => "Stdint.Uint8.succ".
Extract Constant Uint8.pred     => "Stdint.Uint8.pred".
Extract Constant Uint8.add      => "Stdint.Uint8.add".
Extract Constant Uint8.sub      => "Stdint.Uint8.sub".
Extract Constant Uint8.lnot     => "Stdint.Uint8.lognot".
Extract Constant Uint8.land     => "Stdint.Uint8.logand".
Extract Constant Uint8.lor      => "Stdint.Uint8.logor".
Extract Constant Uint8.lxor     => "Stdint.Uint8.logxor".
Extract Constant Uint8.max_int  => "Stdint.Uint8.max_int".
Extract Constant Uint8.min_int  => "Stdint.Uint8.min_int".

Extract Constant Uint16.t       => "Stdint.Uint16.t".
Extract Constant Uint16.succ    => "Stdint.Uint16.succ".
Extract Constant Uint16.pred    => "Stdint.Uint16.pred".
Extract Constant Uint16.add     => "Stdint.Uint16.add".
Extract Constant Uint16.sub     => "Stdint.Uint16.sub".
Extract Constant Uint16.lnot    => "Stdint.Uint16.lognot".
Extract Constant Uint16.land    => "Stdint.Uint16.logand".
Extract Constant Uint16.lor     => "Stdint.Uint16.logor".
Extract Constant Uint16.lxor    => "Stdint.Uint16.logxor".
Extract Constant Uint16.max_int => "Stdint.Uint16.max_int".
Extract Constant Uint16.min_int => "Stdint.Uint16.min_int".
*)
End StdintExtraction.